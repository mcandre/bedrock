MODULES    := PropX PropXTac Machine Assembly Structured Separation Bedrock Word
VS         := $(MODULES:%=%.v)

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Bedrock $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

package:
	hg archive -t tgz /tmp/bedrock.tgz
