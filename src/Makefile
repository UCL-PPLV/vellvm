# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml imp
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(COQLIBDIR)/paco/src Paco -R $(EXTRACTDIR) Extract -R ../lib/CompCert compcert -R $(COQLIBDIR)/RelationAlgebra/ RelationAlgebra
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

QUICKCHICKFILES := ImpQuickChick OllvmQuickChick MemoryQuickChick
IMPCOQFILES := Maps Imp ImpCEvalFun Compiler
COQFILES :=   Classes Util Ollvm_ast  Misc AstLib Dom CFG CFGProp Effects StepSemantics Memory DeadInstr Transform $(IMPCOQFILES) DecidableEquality
OLLVMFILES := 


DEPENDENCYFILES := DEPIMP SetTheory DataDependency
OPTIMISATIONFILES := ConstantFolding
RELATIONALGEBRAFILES := ast

LOOPFILES := LoopIdentification



VFILES := $(COQFILES:%=coq/%.v) $(DEPENDENCYFILES:%=coq/Dependency/%.v) $(OPTIMISATIONFILES:%=coq/Optimisations/%.v) $(LOOPFILES:%=coq/Loops/%.v)
VOFILES := $(COQFILES:%=coq/%.vo) $(DEPENDENCYFILES:%=coq/Dependency/%.vo) $(OPTIMISATIONFILES:%=coq/Optimisations/%.vo) $(LOOPFILES:%=coq/Loops/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vellvm

coq: $(VOFILES)

extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	touch $(EXTRACTDIR)/STAMP


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend



# Directories containing plain Caml code
OCAMLDIRS= $(EXTRACTDIR) $(MLDIR) 

COMMA=,
OCAMLINCLUDES=$(patsubst %,-I %, $(OCAMLDIRS))
print-ocaml-includes:
	@echo $(OCAMLINCLUDES)

OCAMLLIBS := unix,str

.PHONY: clean main.native test

main.native: 
	@echo "Compiling Vellvm"
	ocamlbuild -r -use-menhir -yaccflag --explain $(OCAMLINCLUDES) -libs $(OCAMLLIBS) main.native

vellvm: main.native
	cp main.native vellvm

test: vellvm
	./vellvm --test-pp-dir ../tests/ll

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	ocamlbuild -clean
	rm -rf output
	rm -f vellvm

-include .depend
