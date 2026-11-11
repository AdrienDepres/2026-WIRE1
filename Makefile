ROCQ ?= rocq

.PHONY: all clean

all:
	$(ROCQ) compile CorrectionReview.v
	$(ROCQ) compile Tree33.v
	$(ROCQ) compile Theorem36.v
	$(ROCQ) compile Theorem51.v

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache .nia.cache
