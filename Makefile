FSTAR  ?= fstar.exe
KRML   ?= $(KRML_HOME)/krml
MODULE ?= Main
SRC	   ?= ./fstar/

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen krml --odir gen
	cd gen && $(KRML) *.krml -skip-linking -skip-compilation

extract-ocaml:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen OCaml --odir gen
