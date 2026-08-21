# Haferkamp et al. 2022 formalization progress (2026-08-21)

Attached sources: `/Users/michael/Downloads/s41567-022-01539-6.pdf` and `/Users/michael/Downloads/41567_2022_1539_MOESM1_ESM.pdf`. Target is full unconditional, dependency-closed Lean formalization of every stated lemma/theorem, preserving the source's assumptions only.

## Exact paper inventory and open core

Main Theorem 1 / supplement Appendix B: random fixed architecture of `T` backward-light-cone-containing blocks, at most `L` gates per block, `R` gates total, independent Haar `SU(4)` gates. Under the proof-supported pre-saturation range `T < 4^n - 1`, exact unitary circuit complexity is almost surely `>= R/(9L) - n/3`. Appendix C state form uses `T < 2^(n+1)-1`.

Supplement required results: Tarski--Seidenberg; finite smooth semialgebraic stratification/dimension; polynomial image dimension; low-rank locus; high-rank Clifford/light-cone lemma; main theorem; randomized architecture corollary; slight robustness corollary; approximate/weighted/strong complexity results. Pipeline cards exist under `docs/drafts/pipeline/0-backlog`, main theorem active at `docs/drafts/pipeline/1-in-progress/haferkamp-2022-linear-quantum-circuit-complexity-theorem-1.md`.

Corpus/mathlib audits already run via `scripts/formal_tools.py research` and `rg`. There is no existing exact formalization of paper architecture, contraction, accessible dimension, light-cone rank induction, real semialgebraic Tarski layer, or theorem. Mathlib has no semialgebraic/Tarski/QE layer. Existing complex algebraic modules (`MvPolynomialMatrixRankDefect`, `ComplexAffineAlgebraicStratification*`) are useful only for complex support. Existing static-local circuit theorems and Clifford modules are different results, not substitutes.

Mathlib verified in `/tmp/hgt-sard-probe.lean`: `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`; possible main-theorem bridge via smooth local charts, but it does not discharge attached supplement Theorems 2--3.

## Closed Lean foundation built this session

All target-built; no `sorry`, `admit`, custom axiom, opaque, or unsafe declaration.

1. `formal/GaloisForLFunctions/HTGeometry/FiniteSpecialUnitaryHaarMeasure.lean`
   - finite-dimensional `Matrix.specialUnitaryGroup ι ℂ` compact topological group;
   - Borel topology, normalized Haar `finiteSpecialUnitaryHaar`, probability instance, left-invariant integral;
   - exact `#print axioms` only `[propext, Classical.choice, Quot.sound]`.

2. `formal/GaloisForLFunctions/HTGeometry/FiniteSpecialUnitaryHaarProduct.lean`
   - independent finite product of special-unitary Haar choices via `Measure.pi`;
   - normalized probability proof; same closed axiom audit.

3. `formal/GaloisForLFunctions/HTGeometry/HaferkampTwoQubitArchitecture.lean`
   - `splitTwoQubitConfig`: register split into an ordered Boolean pair plus rest;
   - `TwoQubitArchitecture n R` with ordered distinct locations;
   - verified lift `twoQubitLift` from local `SU(4)` to full-register unitary by tensor/reindex;
   - theorem `twoQubitLift_mem_specialUnitary` from `Matrix.det_reindexAlgEquiv`, `Matrix.det_kronecker`, and local determinant one;
   - time-ordered contraction via `List.ofFn` / `List.prod`, independent Haar gate law.

4. `formal/GaloisForLFunctions/HTGeometry/HaferkampExactCircuitComplexity.lean`
   - exact circuit structure and `exactTwoQubitCircuitComplexity : ℕ∞` as nested infimum over concrete equality witnesses;
   - `exactTwoQubitCircuitComplexity_le_gateCount`;
   - `le_exactTwoQubitCircuitComplexity_iff`, the universal quantifier form necessary for lower bounds.

These modules were imported into `formal/GaloisForLFunctions/HTGeometry.lean`; never build the umbrella. Target commands used: `lake env lean <leaf>` first, then `lake build GaloisForLFunctions.HTGeometry.<leaf>` only. Stale-process checks showed no matching Lean/lake process.

## Lint state

Earlier project lint passed. After unrelated concurrent untracked modules appeared, global `scripts/formal_tools.py lint` fails exclusively because these are unreachable from their umbrellas: `GaloisForLFunctions.RHTower.ChenGuptaLiHtDyadicPhase` and `GaloisForLFunctions.HTGeometry.TriangularIntervalFubini`. Do not modify them; outside Haferkamp scope. Own modules are imported and target audits green.

## Current next concrete task

Formalize the paper's high-rank Lemma 4. Supplement text at `/tmp/hgt-linear-growth-supplement.txt` lines ~199 onward: build backward-light-cone block Clifford gates mapping each nontrivial Pauli string to a selected single-site Z; inductively select `T` Pauli strings outside spans of previous conjugated strings when `T < 4^n-1`; use derivative-insertion formula to get rank `>= T`. Need build exact combinatorial backward-light-cone architecture and local Clifford-Pauli construction first. No numerical computation allowed.
