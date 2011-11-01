.PHONY: all clean dist

all:
	# BEWARE: This will probably take a long time!
	$(MAKE) -C src
	$(MAKE) -C ideal/asm
	$(MAKE) -C ideal/ir

clean:
	$(MAKE) -C src clean
	$(MAKE) -C ideal/asm clean
	$(MAKE) -C ideal/ir clean

dist:
	hg archive -t tgz /tmp/bedrock.tgz
