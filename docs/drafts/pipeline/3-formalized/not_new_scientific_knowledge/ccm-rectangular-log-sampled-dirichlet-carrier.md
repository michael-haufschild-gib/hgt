# Log-sampled rectangular shifted-zeta carrier

- **ID:** `ccm-rectangular-log-sampled-dirichlet-carrier`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / unconditional CCM Dirichlet foundation
- **Novelty status:** not promoted separately as new scientific knowledge
- **Lean modules:**
  `formal/GaloisForLFunctions/RHTower/CCMRectangularDirichletLandau.lean`,
  `CCMShiftedXiCancellation.lean`, `CCMShiftedXiNormalConvergence.lean`,
  `CCMShiftedXiPoleJet.lean`, `CCMShiftedXiGlobalOrder.lean`,
  `CCMShiftedXiLandauContinuation.lean`, `CCMShiftedXiLandauPoleContradiction.lean`,
  `CCMRectangularDominantFold.lean`, `CCMRectangularWeilCompleteness.lean`, and
  `CCMRectangularScrewCurvature.lean`, `CCMRectangularTransverseGrowth.lean`,
  `CCMRectangularPoleTomography.lean`, and
  `CCMRectangularObservablePoleTomography.lean`, and
  `CCMRectangularObservableDivisorTomography.lean`, and
  `CCMRectangularFullObservableDivisorTomography.lean`, and
  `CCMRectangularManuscriptCapstone.lean`

## Theorem

Let `XiRightZeroCopy` be the multiplicity copies of Xi zeros with
`Re(rho-1/2)>0`, put `w=rho-1/2`, and define

```text
c_L(w)=A_L(w)^2.
```

Unconditionally:

1. `sum |c_L(w)|<infinity`; if `L>0`, every `c_L(w)` is nonzero.
2. At the logarithmic aperture `a_n=(log n)/2`, the selected growing edge is

   ```text
   c_L(w)n^w.
   ```

3. The actual Xi divisor satisfies the multiplicity-exact reciprocal law

   ```text
   sum_w 1/(|w| sqrt(|w|)) < infinity.
   ```

   This is extracted from the unconditional `O(R log R)` Xi zero-count.
4. On `Re z>=3/4`, uniformly away from the zeta pole,

   ```text
   |zeta(z)| <= C_d sqrt(|z|+2).
   ```

5. Consequently,

   ```text
   sum_w c_L(w) zeta(s-w)
   ```

   converges locally normally and is holomorphic on an explicit positive-radius
   ball centred at the actual real boundary `1+delta_*`.
6. Schwarz conjugation makes the logarithmic samples real.  Their ordinary
   Dirichlet coefficients are `O(n^delta_*)`, and on `Re s>1+delta_*` their
   L-series is exactly twice the shifted-zeta carrier.
7. If those real coefficients are eventually bounded below, adding a constant
   and deleting a finite prefix gives a nonnegative Dirichlet series.  A
   scale-local Landau theorem, with arbitrary Taylor displacement `h>0`, forces
   this series to converge at a real point strictly left of `1+delta_*`.
8. Multiplication by `xi(s-1/2)` cancels every shifted-zeta pole.  At a pole
   associated with a Xi zero of multiplicity `m`, the equal-support fiber has
   exact analytic order `m-1`, whereas every off-support term and its locally
   normally convergent infinite sum have order at least `m`.  Landau continuation
   therefore gives an impossible order comparison.
9. Hence a nonempty right Xi divisor forces the logarithmically sampled
   coefficients below every real level cofinally.  Functional-equation folding
   and the aperture-uniform remainder transfer this to the actual rectangular
   Weil values.
10. For every fixed `L>0`, RH is equivalent both to pointwise nonnegativity and
    to eventual lower boundedness of this single sampled family.
11. The divisor-side screw profile

    ```text
    Psi_Xi(t)=sum_q [cosh(t(rho_q-1/2))-1]/(rho_q-1/2)^2
    ```

    is absolutely convergent and real-valued, and the exact identity

    ```text
    Q_L(a)=2[Psi_Xi(2a)+Psi_Xi(2a-2L)-2Psi_Xi(2a-L)+2Psi_Xi(L)]
    ```

    turns the theorem into a fixed-width discrete-curvature criterion on the
    arithmetic mesh `t=log n`.
12. If the right Xi divisor is nonempty, the same scalar sequence has sharp
    power exponent equal to the supremal transverse displacement `delta_*`:
    it is `O(n^delta_*)`, but exceeds `C n^alpha` cofinally for every
    `0<=alpha<delta_*` and every `C>=0`.  Under RH it is uniformly bounded.
    Thus norm boundedness is another exact RH criterion, and the carrier
    quantitatively recovers the horizontal defect when one exists.
13. The Xi-cancelled shifted-zeta carrier divided by `xi(s-1/2)` is meromorphic
    on `Re s>1`.  Its simple poles are exactly the shifted right-divisor
    coordinates `s=1+(rho-1/2)`.  A zero of multiplicity `m` still produces
    order `-1`, because the numerator has exact order `m-1` and the denominator
    exact order `m`.
14. The complete actual Weil sequence differs from the full right-divisor
    coefficients by one globally defined remainder.  A late cutoff decomposes
    that remainder into a bounded tail plus a finite prefix, proving that its
    L-series is analytic on `Re s>1`.  The resulting continuation is attached
    to the full sequence and contains no cutoff parameter.  Its simple-pole
    support is exactly the shifted right Xi support.
15. The observable pole weights recover analytic multiplicity exactly.  If
    `rho` has multiplicity `m`, then the trailing coefficient at
    `s=1+(rho-1/2)` is

    ```text
    2 m A_L(rho-1/2)^2.
    ```

    Division by the nonzero window factor therefore recovers `m`.  The same
    complete scalar sequence determines the full right off-critical divisor,
    not only its support.
16. The normalized pole weight is intrinsic: it is unchanged when the positive
    rectangular width or the multiplicity copy naming a fixed support point is
    changed.  There is no cutoff coordinate in the final continuation.

The earlier safe-half-plane estimate remains available: for every `eps>0` and
`Re s>=3/2+eps`,

   ```text
   |zeta(s-w)| <= 1+1/eps
   ```

   uniformly over the right-half Xi divisor.

## Exact formal surface

- `XiRightZeroCopy`
- `xiRightCenteredZero`
- `xiRectangularRightCoefficient`
- `xiRectangularRightCoefficient_ne_zero`
- `norm_xiRectangularRightCoefficient_le`
- `xiRectangularRightCoefficient_summable`
- `xiRightTransverseSup`
- `xiRightTransverseSup_pos`
- `xiRightTransverseSup_le_half`
- `nonempty_xiRightZeroCopy_of_not_riemannHypothesis`
- `xiSpectralPoint_inv_three_halves_summable`
- `norm_riemannZeta_le_sqrt_norm_add_two`
- `xiRectangularShiftedZetaSeries`
- `norm_riemannZeta_sub_xiRightCenteredZero_le`
- `xiRectangularShiftedZetaSeries_summable`
- `summableLocallyUniformlyOn_xiRectangularShiftedZeta_ball`
- `analyticOnNhd_xiRectangularShiftedZetaSeries_landauBall`
- `exists_analyticOnNhd_xiRectangularShiftedZetaSeries_actualLandauBall`
- `xiRectangularRightDirichletCoefficientReal`
- `norm_xiRectangularRightDirichletComplex_le`
- `LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta`
- `landau_local_summability_transfer`
- `LSeries_xiRectangularLandauCoefficient_eq_continuation`
- `exists_xiRectangularLandauCoefficient_summable_left_of_boundary`
- `xiRectangularTwoEdgeDominant_logSample_of_right`
- `xiRectangularCancelledSeries_order`
- `xiRightShiftedPole_re_le_of_landau_summable`
- `xiRectangularRightDirichletCoefficientReal_cofinally_unbounded_below`
- `tsum_xiRectangularTwoEdgeDominant_logSample_eq_ofReal_rightCoefficient`
- `xiWeilPolarization_rectangular_logSample_cofinally_unbounded_below`
- `riemannHypothesis_iff_rectangular_logSample_weil_nonneg`
- `riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow`
- `xiScrewDivisorTerm_summable`
- `star_xiScrewDivisor`
- `xiWeilPolarization_rectangular_eq_screwCurvature`
- `not_riemannHypothesis_implies_xiScrewWindowCurvature_logSample_cofinally_unbounded_below`
- `riemannHypothesis_iff_xiScrewWindowCurvature_logSample_nonneg`
- `riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow`
- `xiRectangularRightDirichletCoefficientReal_cofinally_exceeds_power`
- `norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis`
- `norm_xiWeilPolarization_rectangular_logSample_le_transverse_power`
- `xiWeilPolarization_rectangular_logSample_cofinally_exceeds_power`
- `xiRightTransverseSup_is_sharp_rectangular_power_exponent`
- `riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd`
- `meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one_iff`
- `LSeries_xiRectangularRightDirichletComplex_eq_continuation`
- `norm_xiRectangularWeilRemainderCoefficient_le`
- `analyticAt_LSeries_xiRectangularWeilRemainderCoefficient`
- `LSeries_xiRectangularWeilTailCoefficient_eq_continuation`
- `meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff`
- `meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation`
- `normalizedObservableResidue_eq_xiRightMultiplicity`
- `normalizedObservableResidue_intrinsic`
- `meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation_cutoff_invariant`
- `exists_xiRectangularAdmissibleCutoff`
- `xiRectangularWeilFullRemainderCoefficient_LSeriesSummable`
- `analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient`
- `LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation`
- `meromorphicOn_xiRectangularWeilFullContinuation_rightOne`
- `meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff`
- `meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation`
- `normalizedFullObservableResidue_eq_xiRightMultiplicity`
- `normalizedFullObservableResidue_intrinsic`
- `riemannHypothesis_iff_fullObservableContinuation_analytic_rightOne`
- `fixedWindowLogarithmicWeilCompleteness_capstone`
- `fixedWindowObservablePoleTomography_capstone`
- `fixedWindowObservableSupportRecovery_capstone`
- `fixedWindowObservableDivisorTomography_capstone`
- `fixedWindowObservableDivisorUniversality_capstone`
- `fixedWindowFullObservableDivisorTomography_capstone`
- `fixedWindowFullObservableDivisorUniversality_capstone`

## Boundary

The divisor-side theorem is complete, including arbitrary multiplicity, the
nonattained transverse supremum, the fixed rectangular profile, and the
logarithmic integer sampling.  The remaining RH-bearing theorem is source-side:
derive one eventual finite lower bound for this explicit curvature family from
an unconditional prime--Gamma--theta or semilocal operator construction.  Such
a source floor must not be imported from the Xi divisor or from an equivalent
RH sign hypothesis.

## Verification

- exact module build: passed
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced
- capstone axioms: `[propext, Classical.choice, Quot.sound]`
