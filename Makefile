COQMAKEFILE := coq_makefile
COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-disj-pattern-notation'

SEMANTICS_DIR := semantics
SEMANTICS_THEORIES_DIR := $(SEMANTICS_DIR)/theories
TNUM_DIR := tnum

COQINCLUDES := -R $(SEMANTICS_THEORIES_DIR) bpf.semantics -R $(TNUM_DIR) bpf.tnum
TNUMFILES := $(sort $(wildcard $(TNUM_DIR)/*.v))

.PHONY: all semantics clean distclean tnumcode bpfcode validation validation1 validation2 validationcode

all: semantics _CoqProject CoqMakefile
	@echo "Building tnum proofs..."
	$(MAKE) -f CoqMakefile

semantics:
	$(MAKE) -C $(SEMANTICS_DIR)

_CoqProject: Makefile
	@echo "$(COQINCLUDES)" > $@

CoqMakefile: _CoqProject $(TNUMFILES) Makefile
	@echo "Generating tnum build system..."
	$(COQMAKEFILE) -f $< $(TNUMFILES) $(COQEXTRAFLAGS) -o $@

clean:
	@echo "Cleaning tnum build artifacts..."
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	$(MAKE) -C $(SEMANTICS_DIR) clean
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf

tnumcode:
	coqwc $(TNUMFILES)

bpfcode:
	$(MAKE) -C $(SEMANTICS_DIR) bpfcode

validationcode:
	$(MAKE) -C $(SEMANTICS_DIR) validationcode

validation:
	$(MAKE) -C $(SEMANTICS_DIR) validation

validation1:
	$(MAKE) -C $(SEMANTICS_DIR) validation1

validation2:
	$(MAKE) -C $(SEMANTICS_DIR) validation2

distclean: clean
