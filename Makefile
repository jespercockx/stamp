ADGA_PRELUDE := /home/thomasw/.cabal-sandboxes/Agda-Core/agda-prelude/src

all: plugin test

sandbox:
	cabal sandbox init
	cp cabal.sandbox.config core-plugin/
	cp cabal.sandbox.config test-core-plugin/

plugin:
	(cd core-plugin; cabal clean; \
	AGDA_PRELUDE=$(ADGA_PRELUDE) SANDBOX=../$(wildcard .cabal-sandbox/*-packages.conf.d) cabal install -j --reinstall)

test:
	(cd test-core-plugin; cabal clean; cabal -j1 run)


.PHONY: plugin test
