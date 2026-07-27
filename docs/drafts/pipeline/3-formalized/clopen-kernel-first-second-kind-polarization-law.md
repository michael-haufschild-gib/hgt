# Clopen-kernel first/second-kind polarization law

- **ID:** clopen-kernel-first-second-kind-polarization-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** closure of `ComplexKernelTransfer`, `FirstKindBounded`, `OrthonormalDecay`, and `GlobalSecondKindEscapeFromClopenKernelLaw`
- **Statement:** A closed nonempty bounded-kernel locus forces, at every real point, bounded aggregate first- and second-kind kernel roots, a positive Christoffel limit, summability and decay of the first-kind family, and simultaneous escape of every common bound by adjacent recurrence-weighted second-kind coordinates.

## Goal

Determine the strongest joint first/second-kind consequence of the existing clopen-kernel transfer,
rather than treating its boundedness and Wronskian-escape outputs as unrelated endpoints.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [x] 2 → 3  formalized: `ClopenKernelFirstSecondKindPolarizationLaw.lean`, axiom-clean, in the umbrella
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Closedness plus one bounded-kernel point makes the locus all of `ℂ`.  Restriction to a real point
gives `BoundedKernel`, hence `FirstKindBounded` and a positive Christoffel limit.  The same transfer
gives summability of the first-kind kernel series, hence orthonormal decay.  The constant nonzero
orthonormal Wronskian then forces the two adjacent recurrence-weighted second-kind coordinates to
escape every common bound.  Unpacking `BoundedKernel` shows the sharp separation: aggregate
second-kind kernel roots remain uniformly bounded although the weighted coordinates cannot.

## Audit

- **[CORPUS]:** `ComplexKernelTransfer` supplies global aggregate boundedness and summability
- **[CORPUS]:** `FirstKindBounded` supplies the exact Christoffel equivalence
- **[CORPUS]:** `GlobalSecondKindEscapeFromClopenKernelLaw` supplies only the weighted escape endpoint
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; no existing theorem states the simultaneous aggregate-bounded/coordinate-unbounded polarization profile
- **Status:** `[PAPER-PROVED] [EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — terminal same-folder closure found from exact Lean statements
- 2026-07-22 — exact development check passed with `lake env lean GaloisForLFunctions/HTGeometry/ClopenKernelFirstSecondKindPolarizationLaw.lean`

## Formalization

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/ClopenKernelFirstSecondKindPolarizationLaw.lean`
(imported by `GaloisForLFunctions.HTGeometry`; builds clean; both theorems depend only on
`propext, Classical.choice, Quot.sound`).

| Card item | Lean name |
|---|---|
| the complete profile at every real point: bounded kernel, bounded first kind, positive Christoffel limit, summability, decay, and joint escape | `HTGeometry.clopenKernel_firstSecondKind_complete_polarization` |
| the sharp separation: explicit positive aggregate bounds `S`, `P` for both kernel roots, yet no common bound for the two adjacent recurrence-weighted second-kind coordinates | `HTGeometry.clopenKernel_bounded_aggregate_unbounded_weighted_coordinates` |

The proof is the card's own closure: `boundedKernel_of_isClosed` propagates the single bounded-kernel
point to all of `ℂ`, `firstKindBounded_of_boundedKernel` and
`firstKindBounded_iff_christoffelLimit_pos` give the Christoffel positivity,
`summable_kernel_everywhere_of_isClosed` plus `normSq_monicOrthoC_ofReal` give the real-slice
summability, `tendsto_orthonormalPoly_eval_zero` the decay, and
`weightedSecondKind_escape_everywhere_of_isClosed_boundedKernel` the escape -- so the law is a
genuine closure of the four corpus files rather than a restatement of any one of them.
