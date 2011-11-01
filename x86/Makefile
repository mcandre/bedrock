ROOT    := ..
MODULES := WordViewNat WordViewN BitView WordView \
	   Semantics Struct Sep Refl ExtTactics Tactics MultiWord x86
EXAMPLES := Null Allocated FreeList MallocI MallocImpl # Malloc BSets SLL SlabAlloc Test
VS      := $(MODULES:%=%.v) $(EXAMPLES:%=examples/%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     -R . x86 \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
