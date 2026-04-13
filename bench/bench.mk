# bench/bench.mk — Performance-benchmark rules.  See bench/README.md
# for an overview of how the pipeline fits together.

BENCH_DIMS      = types nonrec rec args ctors
BENCH_REPS      = 3
BENCH_BUILD     = bench/build
BENCH_RESULTS   = bench/results/latest
BENCH_CSVS      = $(BENCH_DIMS:%=bench/%.csv)
BENCH_SUMMARIES = $(BENCH_DIMS:%=$(BENCH_RESULTS)/%.csv)
BENCH_PNGS      = $(BENCH_SUMMARIES:.csv=.png)

# We run the OCaml helper scripts under the bytecode interpreter.  The csv
# library lives outside the stdlib, so feed it via -I + csv.cma; unix.cma is in
# the stdlib and needs no extra path.
BENCH_OCAML     = ocaml -I $(shell ocamlfind query csv) csv.cma

bench: $(BENCH_PNGS)
.PHONY: bench

test: bench

$(BENCH_BUILD)/bench-deps.mk: $(BENCH_CSVS) bench/gen_mk.awk
	$(SHOW)'BENCH-DEPS $@'
	$(HIDE)mkdir -p $(@D)
	$(HIDE)awk -v reps='$(BENCH_REPS)' \
	    -v build='$(BENCH_BUILD)' \
	    -v results='$(BENCH_RESULTS)' \
	    -f bench/gen_mk.awk $(BENCH_CSVS) > $@

-include $(BENCH_BUILD)/bench-deps.mk

# The .v recipes are supplied by bench-deps.mk.

# Generic .out rule: run the .v file injected as a prerequisite by
# bench-deps.mk through coqtop in batch mode.  Depend on the library VO files
# (not TESTVOFILES) so only the theories are rebuilt before a bench.  Prereqs
# expand at rule-read time so we can't reference VOFILES here (it's defined
# later in CoqMakefile); $(VFILES) is set by `include CoqMakefile.conf` before
# CoqMakefile.local is read.
#
# We use $(COQTOP) -batch rather than $(COQC) because a single .v file is
# compiled once per repetition: three parallel $(COQC) invocations racing on
# the same .vo/.vos/.vok/.glob output paths caused intermittent "Uncaught
# exception End_of_file" anomalies in CI.  coqtop -batch runs the file for
# side effects without touching any output file.
$(BENCH_BUILD)/%.out: $(VFILES:.v=.vo)
	$(SHOW)'BENCH $(filter %.v,$^)'
	$(HIDE)mkdir -p $(@D)
	$(HIDE)$(COQTOP) -batch $(COQDEBUG) $(COQFLAGS) $(COQLIBS) \
	    -load-vernac-source $(basename $(filter %.v,$^)) > $@

$(BENCH_RESULTS)/%.csv: bench/summarize.ml
	$(SHOW)'SUMMARIZE $@'
	$(HIDE)mkdir -p $(@D)
	$(HIDE)$(BENCH_OCAML) bench/summarize.ml -dim $* \
	    $(filter %.out,$^) > $@

$(BENCH_RESULTS)/%.png: $(BENCH_RESULTS)/%.csv bench/plot.ml
	$(SHOW)'PLOT $@'
	$(HIDE)$(BENCH_OCAML) unix.cma bench/plot.ml $< $@

clean::
	$(HIDE)rm -rf $(BENCH_BUILD) $(BENCH_RESULTS)
