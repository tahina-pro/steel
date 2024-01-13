ifeq ($(OS),Windows_NT)
  OCAMLPATH:=$(OCAMLPATH);$(shell cygpath -m $(FSTAR_HOME)/lib)
else
  OCAMLPATH:=$(OCAMLPATH):$(FSTAR_HOME)/lib
endif
export OCAMLPATH

all: extract
	src/ocaml/dune.sh
	cp -f src/_build/default/ocaml/main.exe .

extract:
	+$(MAKE) -C src extract
