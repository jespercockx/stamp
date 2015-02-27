all: utils plugin test

utils:
	(cd utils; cabal clean; cabal install -j --reinstall --force-reinstalls)

plugin:
	(cd core-plugin; cabal clean; cabal install -j --reinstall)

test:
	(cd test-core-plugin; cabal clean; cabal -j1 run)
