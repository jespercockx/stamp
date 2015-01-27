all:
	(cd core-plugin; cabal install -j --reinstall)
	(cd test-core-plugin; cabal clean; cabal build)
