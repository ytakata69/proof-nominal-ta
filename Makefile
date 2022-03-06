.PHONY: clean all default
%.vo: %.v
	coqc $<

all: tree.vo
tree.vo: gset.vo

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~
