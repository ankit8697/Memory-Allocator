#
# Makefile for lab 5
#

CC = gcc
CFLAGS = -Wall -Wextra -Werror -Wno-unused-parameter -Wno-unused-function

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o

mdriver: CFLAGS += -Og -ggdb3 # add -pg here to enable gprof profiling of mdriver
mdriver: rebuild $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.opt: CFLAGS += -O2 # add -pg here to enable gprof profiling of mdriver.opt
mdriver.opt: rebuild $(OBJS)
	$(CC) $(CFLAGS) -o mdriver.opt $(OBJS)

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h

rebuild:
	rm -f *.o

clean:
	rm -f *~ *.o mdriver mdriver.opt
