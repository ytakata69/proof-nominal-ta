targets = gset.vo

.PHONY: clean all default
%.vo: %.v
	coqc $<

all: $(targets)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~
