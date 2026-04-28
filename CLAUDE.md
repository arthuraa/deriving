# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Deriving is a Coq library that automatically derives instances of MathComp classes (`eqType`, `choiceType`, `countType`, `finType`, `orderType`) for inductive data types, analogous to Haskell's `deriving`. It targets Coq 8.17–Rocq 9.1 with MathComp ssreflect 2.2–2.5.

## Build Commands

```bash
make              # Build the library (generates CoqMakefile via coq_makefile, then compiles)
make test         # Compile test files in tests/
make clean        # Clean build artifacts including generated tactics.v
make install      # Install via opam
```

Alternative: `nix build` or `nix develop` (provides dev shell with coq-lsp).

## Build System

- `Makefile` generates `CoqMakefile` from `_CoqProject` using `coq_makefile`, then delegates to it.
- `CoqMakefile.local` adds custom rules: generating `theories/tactics.v` and compiling tests.
- `theories/tactics.v` is **auto-generated** — do not edit it directly. It is produced by `ocaml make_tactics.ml` which scans `theories/base.v` and `theories/ind.v` for `Hint Unfold` directives and emits `Declare Reduction` forms.

## Architecture

The library namespace is `deriving` (mapped from `theories/` via `-Q theories deriving` in `_CoqProject`).

### Core modules (theories/)

- **base.v** — Foundational utilities: type equality/casting primitives, transport lemmas, the `deriving` hint database, and unfold hints consumed by `make_tactics.ml`.
- **ind.v** — Inductive type infrastructure: `fun_split` for decomposing function types, `lift_class` for lifting type classes through inductive parameters, polymorphic type handling.
- **tactics.v** — (generated) `deriving_compute` and `deriving_lazy` reduction tactics built from the unfold hints in base.v and ind.v.
- **infer.v** — Notations for defining `IndType` instances: `[indDef for rect]` and `[infer indType of T ...]`.
- **instances.v** — Pre-built `IndType` + derived instances for standard types (unit, bool, nat, option, sum, prod, seq, comparison, positive, N, Z, ascii, string).
- **compat.v** — MathComp version compatibility shim (handles `Order.disp_t` differences).
- **deriving.v** — Convenience re-export of all public modules.

### Instance derivation modules (theories/instances/)

- **eqtype.v** — Derives `hasDecEq` (decidable equality).
- **tree_of_ind.v** — Converts inductive types to decision trees; core infrastructure used by other derivations.
- **fintype.v** — Derives `isFinite` (requires non-recursive types with finType parameters).
- **order.v** — Derives `isOrder` (lexicographic total order on constructors then arguments).

### Derivation workflow

```coq
(* 1. Define type *)
Inductive foo := Foo1 of nat | Foo2 of foo & nat.

(* 2. Register IndType *)
Definition foo_indDef := [indDef for foo_rect].
Canonical foo_indType := IndType foo foo_indDef.

(* 3. Derive and register instances *)
Definition foo_hasDecEq := [derive hasDecEq for foo].
HB.instance Definition _ := foo_hasDecEq.
```

Derivation flags: `[derive ...]` (cbv simplification), `[derive lazy ...]` (lazy eval), `[derive nored ...]` (no simplification — use for large types, keep opaque with `Qed`).

### Special cases

- **Records**: Coq doesn't auto-generate induction principles for records. Add `Scheme T_rect := Induction for T Sort Type.` first.
- **Mutually recursive types**: Use `Combined Scheme` to produce a joint recursor.
- **Nested inductive types**: Requires a hand-written recursor.

## Tests

Test files in `tests/` serve as both regression tests and usage examples: `syntax.v` (mutual recursion, `nored`), `tree.v`, `mutual.v`, `nested.v`, `three.v` (three-way mutual), `records.v`.

## Style Guidelines

- Keep lines as close to 80 characters as possible, but never above 80.
- Use ssreflect tactics by default.

## CI

GitHub Actions with Nix (`nix build`) across x86_64-linux, aarch64-linux, aarch64-darwin, x86_64-darwin. Caching via Cachix.
