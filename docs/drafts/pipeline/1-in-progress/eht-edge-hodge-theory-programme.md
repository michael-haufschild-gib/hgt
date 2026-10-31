# Edge Hodge theory of the scaling surface (EHT) — programme card

- **ID:** EHT
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.7
- **Statement:** theory of the degenerating family `W_{φ,c,N}` (complete Weil matrices), its
  detection edge, limit structure, flows, integer invariants and selectivity.

## Goal
Answer the six questions of §2.7 by Lean theorems (equivalence / classification / no-go), build the
tools listed there, and prove edge-valid statements (identities, inherited polarizations, integer
invariants). Folder `formal/GaloisForLFunctions/EdgeHodgeTheory/`, umbrella
`EdgeHodgeTheory.lean`, README there.

## Module plan (one theorem cluster each)
1. `IntegersAlongPaths` — index semicontinuity (both sides), local constancy at nondegenerate
   points, constancy along nondegenerate paths on connected sets, crossing bound by nullity;
   deformation to a positive model ⇔ positive. Tools: HKT `eventually_le_hermNegIndex`, HTG
   `posIndex_add_negIndex_add_nullIndex`.
2. `TheEdgeOfTheCompleteWeilFamily` — edge `e_φ(N)`, hyperplane edge; RH ⇒ edge = ⊤; universal
   lower bounds (CACT power-log, fixed overlap); ¬RH ⇒ frequently edge ≤ 2(log N)^α (α > 1/4,
   RAPT), hyperplane α > 1/2 (RIT); edge dichotomy; edge exponent spectrum.
3. `TheEdgeCeilingLaw` — profile covariance: every C² profile (RAPT growthTwo law), Gevrey (HKT
   quasi-analytic boundary), sinc critical overlap (TM).
4. `TheLimitStructure` — Ramanujan-graded limit, repayment polarization, Farey superposition
   identity of the limit form, degeneration `E_m(c) → 0`, ground-state ordering if provable.
5. `TheKreinLangerCeilingAlongFlows` — defect ≤ κ(K_ζ) at every resolution (HKT/EAHT), reached.
6. `EdgeSelectivity` — flips bounded edge (RAPT `tiltedUnitSpline_flip_selective`), ζ unbounded.
7. `NoSofteningAtResolution` — Kronecker square same edge (HTG `negIndex_kronecker`).
8. `FrobeniusAtInfinity` — conj = reflection ⇔ critical; 𝔽_q calibration `ᾱ = q/α`.
9. `TheFunctionFieldFlowIsTrivial` — ACS CurveDatum window law: detection within 2g scales.
10. `TheEdgeLogic` — abstract: universal regime of a class ⊆ below each member's edge.
11. Heat edge / deformation readings (RIT heat defect as a path of glued states).

## State
- README first draft written.
- Next: module 1.

## Log
- 2026-10-31 — created; README draft.
