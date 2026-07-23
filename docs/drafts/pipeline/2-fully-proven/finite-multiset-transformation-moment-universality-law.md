# Finite multiset transformation–moment universality law

- **ID:** finite-multiset-transformation-moment-universality-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** closure of sharp `PowerSumTorelli` with the corpus's conjugation, reciprocal, and weighted-reciprocal spectral symmetries
- **Statement:** For any map `τ : ℂ → ℂ`, an `n`-point complex multiset is fixed by `τ` if and only if its power sums through order `n` agree with those of its `τ`-image; reciprocal and weighted function-field spectral closures are immediate instances.

## Goal

Extract the transformation-independent law underlying finite Satake, local-factor, and
function-field spectral dualities instead of proving one symmetry at a time.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

If the transformed multiset equals the original, mapping by `z ↦ z^k` and summing proves every
moment identity.  Conversely, the assumed identities through order `n` are exactly the hypotheses
of sharp finite `powerSum_torelli_finite` for the original family and its pointwise transformed
family.  Torelli recovers multiset equality.  No algebraic, continuous, or involutive property of
the transformation is needed.

## Audit

- **[CORPUS]:** `PowerSumTorelli` compares two supplied finite families but does not package map-fixedness
- **[CORPUS]:** Satake and function-field modules prove only forward consequences for named symmetries
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; no transformation-uniform fixed-multiset iff appears in corpus
- **Status:** `[PAPER-PROVED] [EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — universal transformation closure extracted from exact finite Torelli statement
- 2026-07-22 — exact development check passed with `lake env lean GaloisForLFunctions/HTGeometry/FiniteMultisetTransformationMomentUniversalityLaw.lean`
