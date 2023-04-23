FSTAR  ?= fstar.exe
KRML   ?= $(KRML_HOME)/krml
MODULE ?= Monotonic.ST
SRC	   ?= ./fstar/

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen krml --odir gen
	cd gen && $(KRML) *.krml -skip-linking -skip-compilation

extract-ocaml:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen OCaml --odir gen
