
# Dependencies

* Agda HEAD with the patch Agda-223.patch (might need rebasing)
* https://github.com/UlfNorell/agda-prelude

Best to install both in one cabal sandbox.

Update the ADGA_PRELUDE variable in the makefile

# Compilation

* Make a cabal sandbox in the root of this project:

        make sandbox

* Add agda-prelude's agda-ffi to the sandbox

        cabal sandbox add-source /path/to/agda-prelude/agda-ffi
        
* Compile everything

        make
