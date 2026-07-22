# Suzuki finite-grade trace detector

- **ID:** `suzuki-finite-grade-trace-detector`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean) / finite-dimensional connector
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [BRIDGE, NOT NOVEL BY ITSELF] [NOT RH]`
- **Parent:**
  `../../1-in-progress/suzuki-log-translation-flux-finite-grade-detector.md`
- **Statement:** A jointly separating scalar trace hierarchy on a finite-dimensional
  square-Evans packet contains at most `finrank` separating coordinates; for a hierarchy indexed
  by natural grade, one finite initial cutoff separates.

## Theorems

For a finite-dimensional vector space `E`, index type `ι`, and family

```text
trace : ι -> Dual k E,
```

Lean proves:

```text
(forall x, (forall i, trace i x=0) -> x=0)
 -> exists n pick,
      n<=finrank k E and
      (forall x, (forall j, trace (pick j) x=0) -> x=0).
```

The natural-grade corollary proves existence of `N` such that vanishing of `trace k` for every
`k<=N` forces `x=0`.

## Formal certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/SuzukiFiniteGradeTraceDetector.lean`
- Declarations:
  - `GaloisForLFunctions.RHTower.exists_finite_trace_detector`
  - `GaloisForLFunctions.RHTower.exists_finite_grade_trace_cutoff`
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Role and boundary

This is standard finite-dimensional duality, not claimed as standalone scientific novelty.  Its
source-specific consequence is strategic: once arbitrary finite-order Suzuki residuals jointly
separate the finite square-Evans packet, an infinite dense-seam sum is unnecessary.  The theorem
does not construct those residuals or prove joint separation.

## Gates

- [x] theorem stated over arbitrary field and finite-dimensional packet
- [x] separating subfamily bounded by packet dimension
- [x] natural-grade finite cutoff corollary
- [x] unconditional Lean proof
- [x] targeted module build and axiom audit
- [ ] analytic Suzuki residual hierarchy constructed to arbitrary finite grade
- [ ] joint source-specific separation proved
- [ ] RH

## Log

- 2026-07-22 — formalized finite-coordinate and finite-grade compression of a jointly separating
  hierarchy.
