doconSource = /home/mechvel/docon/2.12/docon/source
configure:
	runghc Setup.hs configure --ghc --user --prefix=${doconSource}/inst -v
#                                     \ --enable-library-profiling
# --user  means to search packages both in the System and User area.

build:
	runghc Setup.hs build
install:
	runghc Setup.hs install --user
