# Contributing

## Running the tests

Run `make test` from the repo root (inside `nix develop` if you use the
flake) to build the library and run the entire test suite.

There are two kinds of tests:

- **End-to-end functionality tests** under `tests/*.v`. Each file is a
  small Rocq development that exercises the derivation machinery on a
  particular shape of inductive type (mutual recursion, records,
  nested types, `nored` mode, etc.) and acts as both a regression
  test and a usage example.

- **Performance benchmarks** under `bench/`.  These measure how long
  the derivation tactics take on synthetic inductive types of varying
  shapes.

## How the benchmarks work

Each benchmark sweep (e.g. `types`, `ctors`, `rec`) is described by a
plain CSV file at `bench/<dim>.csv`.  Each row lists the parameters
that should be passed to `bench/gen_bench.ml` to produce one
synthetic Rocq file (number of mutually inductive types, number of
constructors per type, number of recursive and nonrecursive arguments,
etc.).

`bench/gen_mk.awk` reads those CSVs and emits a make fragment with
one `.v` recipe per row plus the dependencies that wire each .v file
to several `.out` files — one per repetition.  The number of
repetitions is set once in `bench/bench.mk` via `BENCH_REPS`, so we
can take a median and smooth out noise; `make -j` parallelises the
runs across cores.

The sweeps cover the factors we care about for derivation
performance: number of mutually inductive types, number of
constructors, number of recursive arguments per constructor, number
of nonrecursive arguments, and the combination of both kinds of
arguments.  Each sweep produces one summary CSV and one PNG plot
under `bench/results/latest/`, so you end up with one graph per
factor showing how each derivation step scales.
