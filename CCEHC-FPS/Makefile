CFLAGS = -O3 -static -m64
TARGET = CCEHC-FPS

all: ${TARGET} clean

${TARGET}: basis_wpms.h wpms.h paws.h wpms.cpp	
	g++ ${CFLAGS} wpms.cpp -o ${TARGET}

clean:
	rm -f *~

cleanup:
	rm -f ${TARGET}
	rm -f *~
