# Clopen-kernel first/second-kind polarization law

- **ID:** clopen-kernel-first-second-kind-polarization-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** closure of `ComplexKernelTransfer`, `FirstKindBounded`, `OrthonormalDecay`, and `GlobalSecondKindEscapeFromClopenKernelLaw`
- **Statement:** A closed nonempty bounded-kernel locus forces, at every real point, bounded aggregate first- and second-kind kernel roots, a positive Christoffel limit, summability and decay of the first-kind family, and simultaneous escape of every common bound by adjacent recurrence-weighted second-kind coordinates.

## Goal

Determine the strongest joint first/second-kind consequence of the existing clopen-kernel transfer,
rather than treating its boundedness and Wronskian-escape outputs as unrelated endpoints.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
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
