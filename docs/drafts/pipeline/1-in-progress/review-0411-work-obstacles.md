# Formalization of review-0411 work obstacles

- **ID:** review-0411-work-obstacles
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0411/obstacles-summary.md`, §2.1.
- **Goal:** Resolve all 35 listed tasks with exact Lean statements and audited dependencies.

## Scope

Open: A1–A15, A17–A29, A31–A33, A35–A38. A row with several obligations remains
open until every obligation is discharged. Existing results are prerequisites, not new solutions.
No numerical experiments or trusted computation; certificates require kernel proofs.

## Current mathematical target

**A10.** For the window index `ι(A)`, define
`Lₙ = sup {A : ι(A) ≤ n}` in `EReal`. Prove
`ι(A) = #{n : Lₙ < A}`, local finiteness of the thresholds, and
`Lₙ < ∞ ↔ n < #{ρ : Re ρ > 1/2}`. The existing jump-multiple theorem
varies the critical ratio, not the length.

The missing analytic step is preservation of every finite negative subspace under
inward dilation. Dominated convergence of the zero-side Gram entries and openness
of finite negative definiteness would give `ι(A) = sup_{B<A} ι(B)`.

## Other first candidates

- A29: compose the reflection-pair smoothed-count identity with the named receivers.
- A7: evaluate the first-stage Schur complement.
- A19, A28: finite collar cases and the atomic-lattice spectral bound.

## Verification

Each completed theorem requires direct `lake --old env lean` checking, transitive
`#print axioms` inspection, and its owning umbrella import. No item is discharged yet.
