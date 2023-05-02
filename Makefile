FSTAR  ?= fstar.exe
KRML   ?= $(KRML_HOME)/krml
MODULE ?= Main
SRC	   ?= ./fstar/

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen krml --odir gen --include $(KRML_HOME)/krmllib
	cd gen && $(KRML) *.krml -skip-linking -skip-compilation

extract-ocaml:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --codegen OCaml --odir gen

check:
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --record_hints --use_hints
