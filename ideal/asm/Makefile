ROOT    := ../..
MODULES := Ideal Baby LinkedListRev Malloc \
	Arrays ArrayList \
	BSets SinglyLinkedList BinarySearchTree \
	OMaps AssociationList Hashtable \
	Memoize AppendCPS ThreadLib
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
