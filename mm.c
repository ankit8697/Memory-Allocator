/* 
 * Simple allocator based on explicit free lists, first fit search,
 * and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      64                  4  3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  0  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is 1 
 * if and only if the block is allocated. The heap has the following form:
 *
 * begin                                                             end
 * heap                                                             heap  
 *  ---------------------------------------------------------------------  
 * |  HEAD   | hdr(16:a) | ftr(16:a) | zero or more usr blks | hdr(0:a) |
 *  --------------------------------------------------------------------
 *          |       prologue        |                       | epilogue |
 *          |         block         |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * The explicit free list is structured such that the head of the free list 
 * is stored before the prologue block. It stores a pointer to the first
 * free block.
 * 
 * Each allocated block contains a header, a footer, and at least two words of
 * payload for the user.
 * 
 * Each free block contains a header, footer, a pointer to the next free block
 * in list order, and a pointer to the previous free block in list order. The 
 * pointer to the next free block is stored immediately after the header, and
 * the pointer to the previous free block immediately thereafter. When adding
 * a block to the list, we make the head point to it after updating its next
 * field to match the previous head value. The final free block, or the head if
 * the list is empty, has NULL as the value for its pointer to the next block.
 * 
 * The allocator goes to the block pointed to by HEAD, and proceeds along the 
 * list, checking each block for size, then if that block isn't large enough, 
 * going to the next block. When it comes to NULL, it returns NULL to malloc, 
 * causing malloc to request more space.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Insert clever team name here",
    /* First member's full name */
    "Ankit Sanghi",
    /* First member's email address */
    "sanghia@carleton.edu",
    /* Second member's full name (leave blank if none) */
    "Daniel Kleber",
    /* Second member's email address (leave blank if none) */
    "kleberd@carleton.edu"
};

/* Basic constants and macros */
#define WSIZE       8       /* word size (bytes) */  
#define DSIZE       16      /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */

/* NOTE: feel free to replace these macros with helper functions and/or 
 * add new ones that will be useful for you. Just make sure you think 
 * carefully about why these work the way they do
 */

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Perform unscaled pointer arithmetic */
#define PADD(p, val) ((char *)(p) + (val))
#define PSUB(p, val) ((char *)(p) - (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0xf)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       (PSUB(bp, WSIZE))
#define FTRP(bp)       (PADD(bp, GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  (PADD(bp, GET_SIZE(HDRP(bp))))
#define PREV_BLKP(bp)  (PSUB(bp, GET_SIZE((PSUB(bp, DSIZE)))))

/* Returns (pointer to) pointer to the head node of explicit free list  */
#define HEAD         (* (void**)PSUB(heap_start, DSIZE))
#define HEAD_PTR     ((void*) PSUB(heap_start, DSIZE))

/* Given free block ptr bp, compute next free block and previous free block in list */
#define NEXT_FREE_BLKP(bp)  (* (void**) bp)
#define PREV_FREE_BLKP(bp)  (* (void**) PADD(bp, WSIZE))

/* Given free block ptr bp, compute position of pointers to next and previous free block*/
#define NEXT_FREE_BLKP_POS(bp) ((void*) bp)
#define PREV_FREE_BLKP_POS(bp) ((void*) PADD(bp, WSIZE))

/* Global variables */

// Pointer to first block
static void *heap_start = NULL;

/* Function prototypes for internal helper routines */

static bool check_heap(int lineno);
static void print_heap();
static void print_block(void *bp);
static bool check_block(int lineno, void *bp);
static void *extend_heap(size_t size);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static size_t max(size_t x, size_t y);

/* 
 * mm_init -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
int mm_init(void) {
    /* create the initial empty heap */
    if ((heap_start = mem_sbrk(4 * WSIZE)) == NULL)
        return -1;
    
    PUT(heap_start, 0);                        /* alignment padding --- 8 bytes, neither prologue nor epilogue */
    PUT(PADD(heap_start, WSIZE), PACK(OVERHEAD, 1));  /* prologue header */
    PUT(PADD(heap_start, DSIZE), PACK(OVERHEAD, 1));  /* prologue footer */
    PUT(PADD(heap_start, WSIZE + DSIZE), PACK(0, 1));   /* epilogue header */
    
    heap_start = PADD(heap_start, DSIZE); /* start the heap at the (size 0) payload of the prologue block */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void print_free_list() {
    char *bp;
    char *bp_prev = NULL;

    printf("Free List (%p):\n", HEAD);
    if (HEAD == NULL) {
        return;
    }
    for (bp = HEAD; NEXT_FREE_BLKP(bp) != NULL; bp = NEXT_FREE_BLKP(bp)) {
        if (bp == bp_prev) {
            printf("Something blew up at [%p], after [%p] \n", bp, bp_prev);
            exit(0);
        }
        bp_prev = bp;
        print_block(bp);
    }
    print_block(bp);
}

/* 
 * add_to_list -- Adds a free block into the explicit free list
 * Takes a pointer to a coalesced block and adds it to the explicit free list
 * Returns nothing
 * The input block must be a free block
 */
static void add_to_list(void *bp) {
    if (HEAD != NULL) {
        PUT(PREV_FREE_BLKP_POS(HEAD), (size_t) bp);
    }
    PUT(NEXT_FREE_BLKP_POS(bp), (size_t) HEAD);
    PUT(PREV_FREE_BLKP_POS(bp), (size_t) NULL);
    PUT(HEAD_PTR, (size_t) bp);
}

/* 
 * remove_from_list -- Removes a free block into the explicit free list
 * Takes a pointer to a free block and removes it from the explicit free list
 * Returns nothing
 * The input block must be a free block
 */
static void remove_from_list(void *bp) {
    // If the block is head
    if (bp == HEAD && NEXT_FREE_BLKP_POS(bp) != NULL) {
        PUT(HEAD_PTR, (size_t) NEXT_FREE_BLKP(bp));
    } 
    else if (bp == HEAD && NEXT_FREE_BLKP_POS(bp) == NULL) {
        PUT(bp, 0);
    
    } 
    // Block is not the head
    else {
        if (NEXT_FREE_BLKP(bp) != NULL) {
            PUT(PREV_FREE_BLKP_POS(NEXT_FREE_BLKP(bp)), (size_t)PREV_FREE_BLKP(bp));
        }
        PUT(NEXT_FREE_BLKP_POS(PREV_FREE_BLKP(bp)), (size_t) NEXT_FREE_BLKP(bp));

    }
}


/* 
 * mm_malloc -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        /* Add overhead and then round up to nearest multiple of double-word alignment */
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    }
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);            
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = max(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    place(bp, asize);
    return bp;
}

/* 
 * mm_free -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 */
void mm_free(void *bp) {
    /* Set the footer value to the size packed with 0
     * Set the header value to the size packed with 0
     * Coalesce the block
     */
    PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    coalesce(bp);
}

/*
 * EXTRA CREDIT
 * mm_realloc -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
*/
void *mm_realloc(void *ptr, size_t size) {
    // TODO: implement this function for EXTRA CREDIT
    return NULL;
}


/* The remaining routines are internal helper routines */


/* 
 * place -- Place block of asize bytes at start of free block bp 
 *          and <How are you handling splitting?>
 * Takes a pointer to a free block and the size of block to place inside it
 * Returns nothing
 * <Are there any preconditions or postconditions?>
 */
static void place(void *bp, size_t asize) {

    /* Go to footer of bp. Subtract asize from it.
     * Jump backwards by that amount - 8, put the footer value there.
     * Jump backwards 8 bytes and put asize | 1 there.
     * Go to the header of bp and put asize | 1 there.
     */
    // we shouldn't split if nextsize is smaller than 32
    size_t nextsize = GET_SIZE(HDRP(bp)) - asize;
    // If the remaining free block to be split is less than 32, don't split
    remove_from_list(bp);
    if (nextsize < DSIZE + OVERHEAD) {
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    } else {
        PUT(FTRP(bp), nextsize); // Update footer of free to have updated size after splitting
        PUT(PADD(bp, asize - WSIZE), nextsize); // Updating header of free block after splitting
        add_to_list(PADD(bp, asize));
        PUT(HDRP(bp), PACK(asize, 1)); // Update header of bp
        PUT(FTRP(bp), PACK(asize, 1)); // Update footer of bp
    }
}

/*
 * coalesce -- Boundary tag coalescing. 
 * Takes a pointer to a free block
 * Return ptr to coalesced block
 * <Are there any preconditions or postconditions?>
 */
static void *coalesce(void *bp) {
    /*
     * Go to footer of previous block
     * If free, set the header size to that size + coalesced block size
     * Go to header of block after input block
     * If free, get size of that block and add new block size to existing block size
     * Go to the footer of the block to be coalesced and update the size 
     */
    void* coalesced_block = bp;
    int was_on_list = 0;
    if (!GET_ALLOC(HDRP(PREV_BLKP(bp)))) {
        PUT(HDRP(PREV_BLKP(bp)), GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(bp)));
        coalesced_block = PREV_BLKP(bp);
        was_on_list = 1;
    }
    if (!GET_ALLOC(HDRP(NEXT_BLKP(coalesced_block)))) {
        remove_from_list(NEXT_BLKP(coalesced_block));
        PUT(HDRP(coalesced_block), GET_SIZE(HDRP(NEXT_BLKP(coalesced_block))) + GET_SIZE(HDRP(coalesced_block)));
    }
    PUT(FTRP(coalesced_block), GET(HDRP(coalesced_block)));
    if (!was_on_list) {
        add_to_list(coalesced_block);
    }
    return coalesced_block;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize) {
    /* search from the start of the free list to the end */
    for (char* bp = HEAD; bp != NULL; bp = NEXT_FREE_BLKP(bp)) {
        if (asize <= GET_SIZE(HDRP(bp)))
            return bp;
    }

    return NULL;  /* no fit found */
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = words * WSIZE;
    if (words % 2 == 1)
        size += WSIZE;
    if ((long)(bp = mem_sbrk(size)) < 0) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header --- replaces old epilogue */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer  --- one block after b/c replaces epilogue*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header  --- in remaining block*/

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * check_heap -- Performs basic heap consistency checks for an implicit free list allocator 
 * and prints out all blocks in the heap in memory order. 
 * Checks include proper prologue and epilogue, alignment, and matching header and footer
 * Takes a line number (to give the output an identifying tag).
 */
static bool check_heap(int line) {
    char *bp;

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("(check_heap at line %d) Error: bad prologue header\n", line);
        return false;
    }

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!check_block(line, bp)) {
            return false;
        }
    }
    
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("(check_heap at line %d) Error: bad epilogue header\n", line);
        return false;
    }

    return true;
}

/*
 * check_block -- Checks a block for alignment and matching header and footer
 */
static bool check_block(int line, void *bp) {
    if ((size_t)bp % DSIZE) {
        printf("(check_heap at line %d) Error: %p is not double-word aligned\n", line, bp);
        return false;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("(check_heap at line %d) Error: header does not match footer\n", line);
        return false;
    }
    return true;
}

/*
 * print_heap -- Prints out the current state of the implicit free list
 */
static void print_heap() {
    char *bp;

    printf("Heap (%p):\n", heap_start);
    printf("Free list head at (%p)\n", HEAD);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        print_block(bp);
    }

    print_block(bp);    
}

/*
 * print_block -- Prints out the current state of a block
 */
static void print_block(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: End of free list\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c] next: [%p] prev: [%p]\n", bp, 
       hsize, (halloc ? 'a' : 'f'), 
       fsize, (falloc ? 'a' : 'f'), 
       NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp)); 
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}
