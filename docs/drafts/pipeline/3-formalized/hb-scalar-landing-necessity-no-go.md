# HB scalar-landing necessity and direct-landing no-go

- **ID:** HB-C-A.9v-survivor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md · C-A.9v
- **Statement:** Balanced canonical landing residual equals Bochner multiplier times scalar RSZ
  residual plus complete cusp residual; boundary-free nondegenerate landing is equivalent to scalar
  RSZ landing.

## Goal

Close hostile audit of claimed C-A.9u-to-canonical landing and identify exact surviving HB proof
burden.

## Gates

- [x] 0 → 1 in-progress: corpus-derived conjecture and RH chain recorded
- [x] 1 → 2 fully-proven: exact algebraic and pole-fill normalization proof
- [x] 2 → 3 formalized: targeted Lean build and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition not prepared

## Approach

Push C-A.9u through arbitrary complex-linear finite-part reporters, compare with canonical
Stokes completion, classify landing residuals, then certify nontrivial normalization mismatch at
`s=t=2` using `xi(w)=w(w-1)Lambda(w)/2` and Euler-half-plane nonvanishing.

C-A.9w later proves these are abstract height-linear reporters only: analytic-family finite part
does not factor through pointwise spectral specialization.  Thus the residual theorem remains
correct, while the genuine scalar RSZ survivor must be formulated as a meromorphic
parameter-family identity before specialization.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinScalarLandingNoGo`
- Exact residual:
  `d4BM_actualBalancedCanonicalLandingResidual_eq`
- Necessary-and-sufficient survivor:
  `d4BM_actualBoundaryFreeCanonicalBalancedLanding_iff_scalarRSZ`
- Closed direct-landing countermodel:
  `d4BM_directScalarLanding_from_zeroCusp_not_forced`
- Exact normalization no-go:
  `d4BM_canonicalScalarVertex_ne_classicalCompletedRSZ_at_two`
- Verification: direct `lake env lean` pass; targeted `lake build` pass `12476/12476`; headline
  axiom audit only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-29 — paper proof and Lean formalization completed; direct shortcut retired
- 2026-08-29 — C-A.9w representation correction recorded; residual classification unchanged
