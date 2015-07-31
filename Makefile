ADGA_PRELUDE := /home/jesper/agda-prelude/src

all: utils plugin test

sandbox:
	cabal sandbox init
	cp cabal.sandbox.config utils/
	cp cabal.sandbox.config core-plugin/
	cp cabal.sandbox.config test-core-plugin/

utils:
	(cd utils; cabal clean; cabal install -j --force-reinstalls)

plugin:
	(cd core-plugin; cabal clean; \
	AGDA_PRELUDE=$(ADGA_PRELUDE) SANDBOX=../$(wildcard .cabal-sandbox/*-packages.conf.d) cabal install -j --reinstall)

test:
	(cd test-core-plugin; cabal clean; cabal -j1 run)


.PHONY: utils plugin test
