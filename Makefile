all: test-core-plugin


core-plugin/Plugin.hs: core-plugin/Plugin.agda
	(cd core-plugin; agda -c --ghc-flag="-package ghc" -i ~/agda-prelude/src -i . Plugin.agda

core-plugin: core-plugin/Plugin.hs
	(cd core-plugin; cabal install -j --reinstall)

test-core-plugin: core-plugin
	(cd test-core-plugin; cabal build -j1)
