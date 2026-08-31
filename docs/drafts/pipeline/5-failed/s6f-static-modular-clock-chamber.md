# Static modular-clock chamber for theta rank-three D1

- **ID:** TCD-D1-STATIC-CHAMBER
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/theta-rank-three-direct-parabolic-determinant.md
- **Statement:** Known strict Lyapunov/source inequalities plus `0 < -Z < 3/10` do not force the universal rank-three reflected theta D1 polynomial to be positive.

## Goal

The proposed implication would have supplied positive singular-face orientation, hence global
native D1, the finite TCD/S6F gate, cofinal Hankel/Bezoutian landing, Weil positivity, and RH.

## Gates

- [x] 0 → 1 in-progress: exact source-pure conjecture and RH proof chain recorded
- [x] 1 → 2 fully-proven: dependency-closed continuity counterexample proved
- [x] 2 → 3 formalized: Lean theorem `modularThetaLyapunov_strictClockChamber_not_sufficient_for_D1`
- [ ] 3 → 4 publication-ready: standalone exposition and independent novelty review

## Approach

Perturb the exact negative rational seam state along reduced modular data
`Z=-t`, `R=5/2`, `S=-t`.  Its Lyapunov image is
`A=(25/4)(1-t²)`, `W=(11/6)t`.  All target strict inequalities hold for small positive `t`, while
continuity of multivariate-polynomial evaluation preserves negative D1 from `t=0`.

## No-go closure

- **Exact killing theorem/mechanism:** `modularThetaLyapunov_strictClockChamber_not_sufficient_for_D1`; the negative seam chamber penetrates the complete strict static clock chamber.
- **Strongest positive survivor:** `exists_rightNeighborhood_modularThetaLyapunov_strictClockChamber_D1_neg`; negative D1 occupies a full right neighborhood on the reduced-modular ray while every currently known static chamber inequality holds.
- **New insight:** Static localization cannot orient a hypothetical D1 singular face.  Any surviving proof must use actual centre-anchored physical-orbit incidence or a new dynamical invariant not reducible to these signs and clock bounds.
- **Status:** Paper proof dependency-closed; Lean formalized in `GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeStaticPhysicalClockChamberNoGo`. Corpus and primary-arXiv audit found no prior combined-chamber result; priority provisional.

## Log

- 2026-08-31 — conjectured from exact corpus chamber and projective-clock theorems; falsified by open-ray penetration; formalized in Lean.
