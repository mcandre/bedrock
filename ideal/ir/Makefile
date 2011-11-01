ROOT    := ../..
MODULES := Mir Baby Malloc \
	Typed Pure Impure SlList \
	BabyTyped HoTyped \
	Lambda LambdaTest \
	IfStar IfStarTest \
	Wrap SqlTree Sql SqlTest
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
