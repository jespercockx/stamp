all: plugin test

sandbox:
	cabal sandbox init
	cp cabal.sandbox.config core-plugin/
	cp cabal.sandbox.config test-core-plugin/

plugin:
	(cd core-plugin; cabal clean; cabal install -j --reinstall)

test:
	(cd test-core-plugin; cabal clean; cabal -j1 run)


.PHONY: plugin test
