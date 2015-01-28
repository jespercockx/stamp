all: plugin test

plugin:
	(cd core-plugin; cabal clean; cabal install -j --reinstall)

test:
	(cd test-core-plugin; cabal clean; cabal -j1 run)
