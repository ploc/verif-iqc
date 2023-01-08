SRC = $(wildcard *.c)

all: ${SRC:%.c=%.run} 

%.run: %.c
	frama-c -wp -wp-model real -wp-timeout 60 -wp-prover Alt-Ergo-Poly $<


