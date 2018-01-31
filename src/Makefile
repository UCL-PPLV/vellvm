# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml imp
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(COQLIBDIR)/paco/src Paco -R $(EXTRACTDIR) Extract -R ../lib/CompCert compcert
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES := Ollvm_ast Classes Util Misc AstLib Dom CFG CFGProp Effects StepSemantics Memory DeadInstr Transform DecidableEquality DecidableProp
OPTIMISATIONFILES := EqNat transform SSA_semantics paco_util donothing optimisation_stepsem step_trace congruence_definition congruence_proof maps lattice kildall static_analysis static_analysis_proof const_prop const_prop_proof
OLLVMFILES := 

VFILES := $(COQFILES:%=coq/%.v) $(OPTIMISATIONFILES:%=coq/optimisations/%.v)
VOFILES := $(COQFILES:%=coq/%.vo) $(OPTIMISATIONFILES:%=coq/optimisations/%.vo)

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

.PHONY: clean main.native test qc restore

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
