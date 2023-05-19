FSTAR  ?= fstar.exe
KRML   ?= $(KRML_HOME)/krml
MODULE ?= Code
SRC	   ?= ./fstar/

INCLUDE_DIRS = \
							$(KRML_HOME)/krmllib \

FSTAR_INCLUDES = $(addprefix --include , $(INCLUDE_DIRS))

check:
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --record_hints --use_hints

%.fst-in:
	@echo $(FSTAR_INCLUDES)

%.fsti-in:
	@echo $(FSTAR_INCLUDES)

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --codegen krml --odir gen $(FSTAR_INCLUDES) --include $(SRC)
	cd gen && $(KRML) *.krml -skip-linking -skip-compilation

extract-ocaml:
	@mkdir -p gen
<<<<<<< HEAD
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen OCaml --odir gen --include $(SRC)

clean:
	rm -rf gen
	rm -rf fstar/*.fst~
	rm -rf fstar/*.fsti~
=======
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen OCaml --odir gen

check:
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --record_hints --use_hints
>>>>>>> refs/remotes/origin/main
