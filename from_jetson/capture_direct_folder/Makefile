INCLUDE_DIRS = 
LIB_DIRS = 
CC=gcc

CDEFS=
CFLAGS= -O0 -g $(INCLUDE_DIRS) $(CDEFS)
LIBS= -lrt

HFILES= 
CFILES= capture_direct.c

SRCS= ${HFILES} ${CFILES}
OBJS= ${CFILES:.c=.o}

all:	capture_direct

clean:
	-rm -f *.o *.d
	-rm -f capture_direct

distclean:
	-rm -f *.o *.d

capture_direct: ${OBJS}
	$(CC) $(LDFLAGS) $(CFLAGS) -o $@ $@.o $(LIBS)

depend:

.c.o:
	$(CC) $(CFLAGS) -c $<
