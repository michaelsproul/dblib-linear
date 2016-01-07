.PHONY: clean

all: Util.vo

%.vo: %.v
	coqc $^

clean:
	rm -f *.vo *.glob
