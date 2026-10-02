# TH: uniform factor-sixteen pair reserve fails

- **ID:** TH-growth-pair-reserve-sixteen
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/theta-c5-curvature-defect-growth.md
- **Statement:** The proposed inequality `16 D7(q) N(q) P0(q) P8(q) < P2(q)` does not hold for every `q≥3/2`.

## Goal

The proposed reserve would absorb the positive odd sectors in the complete
curvature-growth transfer. Here `Pj=polynomialMoment(q,3,j)` and
`P2(q)=anchorCoolingNumerator(q,3,3)+2 P1(q) N(q)^2` denotes the full pair
polynomial, not the second moment. The actual source starts at `π−3/2`;
failure at the enlarged endpoint is not a source or RH falsification.

## No-go closure

- **Exact killing theorem:** `dominantPairPolynomial_reserve_sixteen_fails`
  proves the strict reverse inequality at `q=3/2`.
- **Positive survivor:** the actual complete cumulant transfer satisfies
  `growthTransferFunctional(q,κ) ≤ −transferAbsorptionResidual(q)` on
  `q≥3/2`. The residual retains the literal dominant pair divided by
  `2P²`, the stable eighth moment, and the finite odd-sector loss. The
  dominant pair equals `dominantAtomScale(q)² P2(q)/q⁹` and is positive.
- **New insight:** the comparison must retain the pair's coordinate
  dependence. The exact residual and support-gap decay laws expose a
  relative-cooling proof. The pair derivative sign is now closed, while
  the coarse residual is strictly negative at the actual center; see
  theta-growth-coarse-eighth-absorption.md. Exact dominant cubic
  absorption and mixed-tail isolation provide the replacement.
- **Status:** dependency-closed paper proof and Lean survivor audited.
  Both the obstruction and residual/formula endpoints are in
  `ThetaCuspCurvatureDefectGrowthAbsorptionResidual.lean`.
  Scratch axiom audits report only `propext`, `Classical.choice`,
  `Quot.sound`. Final `lake --old env lean -o … <leaf.lean>` exited 0
  with empty log `/tmp/th-growth-absorption-residual-final.log`.

## Paper proof of the survivor

Use the exact eight-sector logarithmic identity. The dominant single
transfer vanishes; the deep single transfer lies between zero and `C D8`.
Mixed and deep pairs have stable support, so the complete pair dominates
its positive dominant pair. Normalized weights are positive, at most
`1/k`, and the pair weight is at least `1/(2P²)`. Drop the favorable
even sectors. The three adverse sectors are bounded by
`C (3⁷ M0²+5⁷ M0⁴+7⁷ M0⁶) M8`. Combining these inequalities gives the
stated residual bound. Exact polynomial-to-moment transport gives the
pair formula. No residual positivity premise enters either theorem.

## Log

- 2026-10-02 — symbolic endpoint obstruction and exact positive survivor
  formalized; route TH and the complete absorption problem remain active.
