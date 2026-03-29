EXEC         = naskets
EXAMPLES_DIR = examples
TESTS        = $(wildcard $(EXAMPLES_DIR)/*.nsk)
TIMEOUT_SEC  = 0.1

.PHONY: all build test clean

all: build

build:
	@cabal build
	@cp $$(cabal list-bin $(EXEC)) ./$(EXEC)

test: build
	@for file in $(TESTS); do                                                                  \
	    echo "" ;                                                                              \
	    echo "**** $$file ****\n" ;                                                            \
	    TFILE=$$(mktemp) ;                                                                     \
	    ./$(EXEC) $$file hello world &                                                         \
	    PID=$$! ;                                                                              \
	    ( sleep $(TIMEOUT_SEC); if kill $$PID 2>/dev/null; then echo timeout > $$TFILE; fi ) & \
	    WATCHER=$$! ;                                                                          \
	    wait $$PID     2>/dev/null ;                                                           \
	    kill $$WATCHER 2>/dev/null ;                                                           \
	    wait $$WATCHER 2>/dev/null ;                                                           \
	    if [ -s $$TFILE ]; then                                                                \
	        echo "[TIMEOUT] $$file execution exceeded $(TIMEOUT_SEC) seconds." ;               \
	    fi ;                                                                                   \
	    rm -f $$TFILE ;                                                                        \
	done
	@echo ""
	@echo "Done."

clean:
	@cabal clean
	@rm -f $(EXEC)
	@rm -f *~ src/*~ examples/*~
