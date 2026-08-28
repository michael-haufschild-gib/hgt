# Theta C5 cofinal functional absorption

- **ID:** `theta-c5-cofinal-functional-absorption`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed structural theorems
- **Source:** literal completed-theta product fibres, higher/first atom likelihood ratio, and exact source C5 numerator
- **Statement:** For every `t > 0` in the modular-center first-fibre-rise chamber,

  ```text
  thetaCuspCompletedProductFiberCofinalFunctionalAbsorptionBudgetAtZero(t) <= 0.
  ```

  In Lean notation the chamber premise is

  ```text
  thetaCuspCompletedProductFiberAmplitude 1 0 0
    < thetaCuspCompletedProductFiberAmplitude 1 0 t.
  ```

## Corpus derivation

This conjecture was frozen only after corpus search exposed all of its terms:

1. `thetaCuspCompletedProductFiberAmplitude_one_add_higherTail` gives the exact completed
   product-fibre split `source = first fibre + cofinal higher tail`.
2. `exists_thetaCuspCompletedProductFiberAmplitude_one_rise` proves that the first-fibre-rise
   chamber is nonempty.
3. `thetaCuspReflectedSourceFirstDrop_pos` forces the cofinal higher-tail drop to be strictly
   positive in that chamber.
4. `thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn` and the exact derivative chain through
   the higher likelihood jets provide the source-specific variables for attacking the sign.
5. The new unconditional total-variance identity proves

   ```text
   A1*A2*C5(A1+A2,D1+D2,J1+J2)
     = A2*(A1+A2)*C5(A1,D1,J1)
       + A1*(A1+A2)*C5(A2,D2,J2)
       + 4*t^2*(A1*D2-A2*D1)^2.
   ```

6. At modular center the infinite cofinal tail is literal, not a formal residual:

   ```text
   higherTail(t) = firstFiber(t) * R(t) * (2 + R(t)),
   R = higherAtomTail / firstAtom.
   ```

   Lean proves both tail derivative identities through order two and identifies the residual
   curvature with the functional fifth-root numerator of the actual infinite tail.

Therefore, in the rise chamber, the product of first and tail drops is negative and Lean proves

```text
source C5(0,t) >= 0
  iff cofinalFunctionalAbsorptionBudgetAtZero(t) <= 0.
```

This is not generic positive-mixture closure. The first component has negative accumulated drop;
the higher tail must absorb the first-fibre curvature and the strictly nonnegative projective-flux
mismatch square.

## Attack

Differentiate the exact factorization

```text
higherTail = firstFiber * R * (2 + R)
```

twice. Substitute the corpus derivative chains for the first-atom log density and `R,R',R''` into
the functional absorption budget. The target should become a source-pure polynomial/covariance
inequality in the higher-likelihood spectral moments. Monotone likelihood ratio supplies the
orientation, but is not assumed sufficient: if the resulting covariance has an uncontrolled
third-moment term, pivot to the exact higher-likelihood cumulant Riccati hierarchy rather than to
a generic moment bound.

Failure criterion: an exact theta-derived sign reversal of this budget. If found, retain the
sharp scale chamber or equality classification and retire only the modular-center cofinal
absorption subroute.

## RH proof chain and uncovered joins

This conjecture contributes to the following explicit corpus chain:

1. **Cofinal absorption at modular-center rise scales** (this card) gives source `C5 >= 0` there by
   `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_cofinalFunctionalBudget_nonpos`.
2. Combine with the already proved local positive C5 chamber and still-open off-center/complement
   transport to obtain global
   `thetaCuspReflectedSourceFifthRootCurvatureNumerator >= 0`.
3. `thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureNumeratorFailure` then rules
   out every negative literal source rank-four odd wall.
4. `thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres`, followed by
   `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall`, lands this at physical
   center-mixed rank four.
5. Rank four is not RH. Still-open higher-packet positivity and a cofinal no-escape theorem must
   upgrade the finite-rank source orientation to the universal theta packet/tilt-flux sign.
6. `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` then identifies that universal sign
   with RH (equivalently use `riemannHypothesis_iff_xiWeilPolarization_nonneg`).

Thus this conjecture closes one genuine C5 chamber in the first rank-four arrow; it does not hide
the later all-rank and source-to-Weil joins.

## Novelty / hostile audit

- Corpus had no fifth-root mixture law, no cofinal C5 budget, and no likelihood factorization of
  the completed product-fibre tail before this card's Lean module.
- Planat--Solé, *Second-Level Concavity of the Riemann Xi Kernel* (arXiv:2608.19160), proves a
  different Laguerre-expression log-concavity theorem and makes no RH claim; it contains neither
  this `C5` total-variance identity nor the cofinal budget.
- Michałowski, *On the Pólya Frequency Order of the de Bruijn--Newman Kernel* (arXiv:2602.20313),
  leaves global `PF4` open and studies a different Toeplitz threshold; it contains no product-fibre
  likelihood absorption law.
- Exact August 2026 searches found no external statement of the algebraic total-variance identity,
  literal cofinal-tail curvature split, or the conjectured budget sign. This is a literature-search
  conclusion, not a Lean theorem.

## Lean artifacts

- `GaloisForLFunctions.HilbertMetric.FifthRootCurvatureMixture`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureTotalVariance`
- Main exact hard core:
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_cofinalFunctionalBudget_nonpos`
- Likelihood factorization:
  `thetaCuspCompletedProductFiberHigherTail_zero_eq_firstFiber_mul_likelihoodFactor`

## Gates

- [x] corpus-derived statement and exact source coordinates
- [x] explicit downstream RH chain with uncovered joins named
- [x] total-variance identity, literal tail jets, chamber nonemptiness, and exact iff formalized
- [x] August 2026 primary-literature collision audit
- [ ] prove or refute functional absorption sign from theta likelihood/cumulant structure
- [ ] extend surviving sign mechanism off modular center and across complement chamber
- [ ] close global source C5 and physical rank-four wall
- [ ] build higher packets and cofinal source-to-Weil no-escape

## Log

- 2026-08-29 — Opened after corpus search and exact Lean reduction. No computation entered the
  proof or the conjecture.
