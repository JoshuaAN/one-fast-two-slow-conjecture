# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Lean 4 + Mathlib formalization of the "one fast / two slow" server queueing-control
proof (see `One_fast_two_slow_conjecture-2.pdf`). The mathematical goal is to show that a
*relaxed* value iteration coincides with the *true* nonpreemptive value iteration, by
proving that an invariant cone of value functions is preserved by every operator in the
Bellman recursion. Definitions and lemmas carry comments tying them back to numbered
equations/lemmas in the PDF.

## Build / run

```bash
lake exe cache get   # fetch prebuilt Mathlib (do this before the first build)
lake build           # build the library + `untitled` executable
lake exe untitled    # runs Main, prints "ok"
```

There is no test suite; correctness *is* the build — if `lake build` succeeds, every proof
checks. To check a single file, `lake build OneFastTwoSlow.<Module>` (e.g.
`lake build OneFastTwoSlow.EventClosure`).

Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.29.1`); Mathlib rev is pinned
in `lakefile.toml`. Don't bump either casually — Mathlib lemma names drift between versions.

### Source directory must match the library name

Lake uses the default `srcDir = "."`, so module `OneFastTwoSlow.Foo` resolves to the file
`OneFastTwoSlow/Foo.lean`. The source directory must therefore be named **`OneFastTwoSlow/`**.
As of this writing the working tree has the directory named `one-fast-two-slow/`, which does
**not** resolve and makes `lake build` fail with `no such file or directory`. Rename it to
`OneFastTwoSlow/` (or set `srcDir`/`globs` in `lakefile.toml`) to build. This is the open
"Fix Untitled folder name" item in `README.md`.

## Architecture

Everything hangs off the invariant cone `InCone` (the cone `𝒦`, conditions K1–K6) defined in
`Defs.lean`. The proof strategy is: show each operator in the Bellman step keeps a value
function inside `𝒦`, and that staying inside `𝒦` forces the relaxed assignment operator to
agree with the true one.

Module dependency order (each imports the ones above it; `Main.lean` imports all):

- **`Defs.lean`** — core objects: `State := ℕ × Fin 3`, `ValueFn := State → ℝ`,
  `QueueParams` (rates μ₁ > μ₂ > 0, Λ ≥ 0). Operators: `P` (event operator), `Q_true` vs
  `Q_modified` (true vs relaxed assignment — `Q_modified` is deliberately written via
  explicit case-splitting on `min` to make closure proofs tractable), holding cost `c`,
  and Bellman steps `T` / `T_modified` (`V ↦ c + ρ·P(Q V)`). `InCone` bundles K1–K6;
  `BoundaryComp` bundles the two boundary inequalities (5.1)–(5.2).
- **`Basic.lean`** — `𝒦` is a convex cone: contains `0` and `c`, closed under `+` and
  nonnegative scaling; plus `convex_x` (x-convexity derived from K2/K3).
- **`AssignmentClosure.lean`** — Lemma 2: `𝒦` is closed under `Q_modified`.
- **`EventClosure.lean`** — Lemma 3: `𝒦` is closed under `P`.
- **`BoundaryDominance.lean`** — Lemma 4: one relaxed Bellman step establishes
  `BoundaryComp` (the boundary comparisons).
- **`RelaxedEqualsTrue.lean`** — Proposition 1: relaxed and true recursions coincide;
  defines `iterate` (the value-iteration sequence from `0`) and `iterate_mem_cone`.
- **`BellmanConsistency.lean`** — combines the above into `value_consistency` (the paper's
  Lemma 5): `T_modified` agrees with `T` along the iteration.

## Conventions in the proofs

- `Fin 3` indexes the slow-server count `y ∈ {0,1,2}`; K2/K3 are stated over `Fin 2` and
  injected via `.castSucc`/`.succ`. Reducing these to numerals often needs explicit `rfl`
  bridges like `((0 : Fin 2).castSucc : Fin 3) = 0` (see `convex_x` in `Basic.lean`) before
  `linarith`.
- Inequality goals are typically discharged with `linarith`/`nlinarith` after pulling the
  relevant `InCone` field (`hf.K1 …`) into context; arithmetic identities go through
  `simp only [c]; push_cast; ring`.
- `Q_modified` proofs lean on `min_cases` / `min_le_left`/`min_le_right` to handle the
  tail-minimum branches.
