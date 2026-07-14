import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquareEnergySpectrum
import GaloisForLFunctions.RHTower.PrimeArchThermalKrylovEquivalence
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum

/-!
# Atomwise thermal defect and prime square-energy spectrum

One right-half Xi zero produces two simultaneous positive signatures.  Its reciprocal-square
coordinate contributes a strictly positive term to the static thermal orientation energy, while
the same horizontal displacement forces lower bounds for the linear and squared Dirichlet
abscissae of the square-sampled dyadic prime overshoot.

This explains the exact relation to finite KMS thermodynamic limits.  KMS positivity supplies the
closed positive moment cone unconditionally, including when such an atom exists.  The missing RH
datum is the vanishing of every atomwise orientation term; on the prime side, the same datum is
the collapse of the forced square-energy exponents to the critical boundary.
-/

open Complex Filter LSeries Topology

namespace RHTower

noncomputable section

/-- Every positive-transverse Xi copy contributes a strictly positive summand to the thermal
orientation energy. -/
theorem xiRightZeroCopy_thermalOrientationTerm_pos (q : XiRightZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q.1).im ^ 2 := by
  apply sq_pos_of_ne_zero
  intro him
  have hre : (q.1.1 : ℂ).re = 1 / 2 := by
    rw [xiZeroCopyReciprocalSquare_eq] at him
    exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1.1).mp him
  have hpos := xiRightCenteredZero_re_pos q
  rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hpos
  norm_num at hpos
  linarith

/-- **Atomwise thermal--prime exponent law.**  A single right-half Xi copy simultaneously
contributes positive static thermal orientation energy and forces the exact linear and Hilbert
square-sample abscissa lower bounds. -/
theorem xiRightZeroCopy_thermalPrimeSquareEnergySpectrum (q : XiRightZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q.1).im ^ 2 ∧
      (((2 * (q.1.1 : ℂ).re : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ∧
      (((4 * (q.1.1 : ℂ).re - 1 : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient := by
  have hzero : xi (q.1.1 : ℂ) = 0 :=
    xi_eq_zero_of_mem_divisor_support q.1.1
  have hrho : 1 / 2 < (q.1.1 : ℂ).re := by
    have hpos := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hpos
    norm_num at hpos
    linarith
  exact ⟨xiRightZeroCopy_thermalOrientationTerm_pos q,
    two_mul_xi_zero_re_le_squarePrimeWindowPositiveExcess_abscissa
      hzero hrho,
    four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
      hzero hrho⟩

/-- A nonempty positive-transverse Xi divisor makes the total thermal orientation energy
strictly positive by an explicit atomwise comparison.  This proof does not obtain the atom from
`¬RiemannHypothesis`; the divisor copy is the input. -/
theorem xiThermalOrientationEnergy_pos_of_nonempty_xiRightZeroCopy
    (hne : Nonempty XiRightZeroCopy) :
    0 < xiThermalOrientationEnergy := by
  obtain ⟨q⟩ := hne
  have hterm := summable_xiThermalOrientationTerm.le_tsum q.1
    (fun r _ => sq_nonneg (xiZeroCopyReciprocalSquare r).im)
  rw [← xiThermalOrientationEnergy] at hterm
  exact (xiRightZeroCopy_thermalOrientationTerm_pos q).trans_le hterm

/-- The unconditional sixth Hermitian mass of the centered reciprocal Xi coordinates.  This is
the finite constant which converts a transverse half-plane width into a quadratic thermal-source
gap bound. -/
def xiThermalCubicReciprocalMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiReciprocalCoordinate q‖ ^ 6

/-- The cubic reciprocal mass is summable. -/
theorem summable_xiThermalCubicReciprocalMass :
    Summable (fun q : XiZeroCopy => ‖xiReciprocalCoordinate q‖ ^ 6) := by
  have h := (summable_xiZeroCopyReciprocalSquare_pow 2).norm
  apply h.congr
  intro q
  simp only [xiZeroCopyReciprocalSquare, xiReciprocalCoordinate, norm_pow,
    Nat.reduceAdd]
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul]

/-- The cubic reciprocal mass is strictly positive.  This uses one zero from the unconditional
infinite Xi divisor and the nonvanishing of its centered spectral coordinate. -/
theorem xiThermalCubicReciprocalMass_pos :
    0 < xiThermalCubicReciprocalMass := by
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let rho : XiDivisorSupport := ⟨z, hz⟩
  have hpos := xi_divisor_pos_on_support rho
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  rw [xiThermalCubicReciprocalMass]
  exact summable_xiThermalCubicReciprocalMass.tsum_pos
    (fun r => by positivity)
    q
    (pow_pos (norm_pos_iff.mpr (inv_ne_zero (xiSpectralPoint_ne_zero q))) 6)

/-- Pointwise quadratic transverse control of one thermal orientation atom.  A global Xi
half-plane width `alpha` gives
`Im(lambda_q)^2 <= 4*alpha^2*|xiSpectralPoint(q)^(-1)|^6`. -/
theorem xiThermalOrientationTerm_le_cubicReciprocalMass_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      4 * alpha ^ 2 * ‖xiReciprocalCoordinate q‖ ^ 6 := by
  have hdelta := abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have himAbs : |(xiSpectralPoint q).im| ≤ alpha := by
    rw [xiSpectralPoint_im_eq]
    simpa only [abs_sub_comm] using hdelta
  have himSq : (xiSpectralPoint q).im ^ 2 ≤ alpha ^ 2 := by
    nlinarith [sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]
  have hpoint : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hDpos : 0 < Complex.normSq (xiSpectralPoint q) :=
    Complex.normSq_pos.mpr hpoint
  have hnorm : ‖(xiSpectralPoint q)⁻¹‖ ^ 6 =
      1 / Complex.normSq (xiSpectralPoint q) ^ 3 := by
    rw [norm_inv, div_eq_mul_inv, one_mul, inv_pow]
    congr 1
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.sq_norm]
  rw [xiZeroCopyReciprocalSquare, xiReciprocalCoordinate, hnorm]
  simp only [pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  rw [show
      (xiSpectralPoint q).re / Complex.normSq (xiSpectralPoint q) *
          (-(xiSpectralPoint q).im / Complex.normSq (xiSpectralPoint q)) +
        (-(xiSpectralPoint q).im / Complex.normSq (xiSpectralPoint q)) *
          ((xiSpectralPoint q).re / Complex.normSq (xiSpectralPoint q)) =
        -2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im /
          Complex.normSq (xiSpectralPoint q) ^ 2 by field_simp; ring]
  have hreSq : (xiSpectralPoint q).re ^ 2 ≤
      Complex.normSq (xiSpectralPoint q) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (xiSpectralPoint q).im]
  have hcore :
      (xiSpectralPoint q).re ^ 2 * (xiSpectralPoint q).im ^ 2 ≤
        alpha ^ 2 * Complex.normSq (xiSpectralPoint q) := by
    calc
      _ ≤ (xiSpectralPoint q).re ^ 2 * alpha ^ 2 :=
        mul_le_mul_of_nonneg_left himSq (sq_nonneg _)
      _ ≤ Complex.normSq (xiSpectralPoint q) * alpha ^ 2 :=
        mul_le_mul_of_nonneg_right hreSq (sq_nonneg _)
      _ = _ := by ring
  calc
    (-2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im /
          Complex.normSq (xiSpectralPoint q) ^ 2) *
        (-2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im /
          Complex.normSq (xiSpectralPoint q) ^ 2) =
        4 * (xiSpectralPoint q).re ^ 2 * (xiSpectralPoint q).im ^ 2 /
          Complex.normSq (xiSpectralPoint q) ^ 4 := by field_simp; ring
    _ ≤ (4 * alpha ^ 2 * Complex.normSq (xiSpectralPoint q)) /
          Complex.normSq (xiSpectralPoint q) ^ 4 := by
      rw [div_le_div_iff_of_pos_right (pow_pos hDpos 4)]
      nlinarith [hcore]
    _ = 4 * alpha ^ 2 * (1 / Complex.normSq (xiSpectralPoint q) ^ 3) := by
      field_simp [ne_of_gt hDpos]
    _ = 4 * (alpha * alpha) *
          (1 / Complex.normSq (xiSpectralPoint q) ^ 3) := by ring

/-- **Quadratic thermal saturation budget.**  A transverse Xi half-plane bound of width `alpha`
controls the complete thermal orientation energy by `4*alpha^2` times the unconditional cubic
reciprocal mass. -/
theorem xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha) :
    xiThermalOrientationEnergy ≤
      4 * alpha ^ 2 * xiThermalCubicReciprocalMass := by
  rw [xiThermalOrientationEnergy, xiThermalCubicReciprocalMass]
  have hscaled := summable_xiThermalCubicReciprocalMass.mul_left
    (4 * alpha ^ 2)
  have hle := summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q =>
      xiThermalOrientationTerm_le_cubicReciprocalMass_of_halfPlaneBound
        halpha hzeros q)
    hscaled
  simpa only [tsum_mul_left] using hle

/-- **Intrinsic transverse--thermal value law.**  The actual rightmost transverse Xi
displacement controls the thermodynamic source gap quadratically, with the unconditional sixth
reciprocal mass as coefficient. -/
theorem xiThermalSourceGap_le_intrinsicTransverseCubicBudget :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * xiRightTransverseSup ^ 2 * xiThermalCubicReciprocalMass := by
  have hzeros : XiZeroHalfPlaneBound xiRightTransverseSup :=
    (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le
      xiRightTransverseSup_nonneg).2 (by
        rw [xiProjectiveReflectionRadius_eq_transverseSup])
  have hbound :=
    xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
      xiRightTransverseSup_nonneg hzeros
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- **Normalized thermal-gap prime exponent law.**  The square root of the thermal/source gap,
normalized by the unconditional sixth reciprocal mass, is a direct forced excess above the
critical abscissa for the linear square-sampled prime overshoot.  The transverse Xi radius has
been eliminated from the statement. -/
theorem one_add_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcess_abscissa
    (hne : Nonempty XiRightZeroCopy) :
    (((1 + Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessDirichletCoefficient := by
  have hmass : 0 < xiThermalCubicReciprocalMass :=
    xiThermalCubicReciprocalMass_pos
  have hbudget := xiThermalSourceGap_le_intrinsicTransverseCubicBudget
  have hsqrt :
      Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) ≤
        2 * xiRightTransverseSup := by
    rw [Real.sqrt_le_left (mul_nonneg (by norm_num) xiRightTransverseSup_nonneg)]
    rw [div_le_iff₀ hmass]
    nlinarith
  have hreal :
      1 + Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) ≤
        1 + 2 * xiRightTransverseSup := by
    linarith
  have hcast :
      (((1 + Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact hcast.trans
    (one_add_two_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcess_abscissa hne)

/-- The Hilbert square-sampled prime overshoot detects twice the same normalized thermal/source
gap exponent. -/
theorem one_add_two_mul_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcessSquare_abscissa
    (hne : Nonempty XiRightZeroCopy) :
    (((1 + 2 * Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
      LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient := by
  have hmass : 0 < xiThermalCubicReciprocalMass :=
    xiThermalCubicReciprocalMass_pos
  have hbudget := xiThermalSourceGap_le_intrinsicTransverseCubicBudget
  have hsqrt :
      Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) ≤
        2 * xiRightTransverseSup := by
    rw [Real.sqrt_le_left (mul_nonneg (by norm_num) xiRightTransverseSup_nonneg)]
    rw [div_le_iff₀ hmass]
    nlinarith
  have hreal :
      1 + 2 * Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) ≤
        1 + 4 * xiRightTransverseSup := by
    linarith
  have hcast :
      (((1 + 2 * Real.sqrt
          ((xiThermalSecondMoment - normalizedPrimeArchMoment 1) /
            xiThermalCubicReciprocalMass) : ℝ) : EReal)) ≤
        (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact hcast.trans
    (one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa hne)

/-- Every explicit finite thermal second moment is bounded above by the unconditional
thermodynamic second moment. -/
theorem xiThermalTruncation_one_le_secondMoment (N : ℕ) :
    xiThermalTruncation N 1 ≤ xiThermalSecondMoment := by
  calc
    xiThermalTruncation N 1 =
        ∑ j ∈ Finset.range N, xiThermalNode (xiThermalEnumeration j) ^ 2 := by
      simp only [xiThermalTruncation, pow_one, pow_two]
    _ ≤ ∑' j : ℕ, xiThermalNode (xiThermalEnumeration j) ^ 2 :=
      hasSum_xiThermalEnumeration_sq.summable.sum_le_tsum
        (Finset.range N) (fun j _ => sq_nonneg _)
    _ = xiThermalSecondMoment := hasSum_xiThermalEnumeration_sq.tsum_eq

/-- **Eventual finite-system cap criterion.**  RH is equivalent to the source value eventually
bounding the second moments of the explicit growing finite KMS systems.  Exact convergence to the
source and control of the other moments are unnecessary. -/
theorem riemannHypothesis_iff_eventually_xiThermalTruncation_one_le_source :
    RiemannHypothesis ↔
      ∀ᶠ N in atTop,
        xiThermalTruncation N 1 ≤ normalizedPrimeArchMoment 1 := by
  constructor
  · intro hRH
    have heq := xiThermalSecondMoment_eq_source_iff_rh.mpr hRH
    exact Filter.Eventually.of_forall fun N =>
      (xiThermalTruncation_one_le_secondMoment N).trans_eq heq
  · intro hupper
    apply xiThermalSecondMoment_le_source_iff_rh.mp
    exact le_of_tendsto tendsto_xiThermalTruncation_one hupper

/-- **Vanishing-error finite-system cap criterion.**  It is enough, and is equivalent to RH, that
for every positive error the source value plus that error eventually bounds the second moments of
the growing finite KMS systems.  No candidate thermodynamic limit has to be supplied. -/
theorem riemannHypothesis_iff_eventually_xiThermalTruncation_one_le_source_add_eps :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N in atTop,
          xiThermalTruncation N 1 ≤ normalizedPrimeArchMoment 1 + ε := by
  constructor
  · intro hRH ε hε
    have heq := xiThermalSecondMoment_eq_source_iff_rh.mpr hRH
    exact Filter.Eventually.of_forall fun N =>
      (xiThermalTruncation_one_le_secondMoment N).trans
        (by linarith [heq])
  · intro hupper
    apply xiThermalSecondMoment_le_source_iff_rh.mp
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact le_of_tendsto tendsto_xiThermalTruncation_one (hupper ε hε)

/-- A linear square-sample abscissa bound at width `alpha` quantitatively forces the thermal
second moment to lie within `4*alpha^2` cubic reciprocal masses of its source value. -/
theorem xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcess_abscissa
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ≤
        (((1 + 2 * alpha : ℝ) : EReal))) :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * alpha ^ 2 * xiThermalCubicReciprocalMass := by
  have hzeros : XiZeroHalfPlaneBound alpha := by
    intro rho hzero
    by_cases hrho : 1 / 2 < rho.re
    · have hzeroBound :=
        two_mul_xi_zero_re_le_squarePrimeWindowPositiveExcess_abscissa
          hzero hrho
      have hreal : 2 * rho.re ≤ 1 + 2 * alpha := by
        exact_mod_cast hzeroBound.trans habscissa
      linarith
    · linarith
  have hbound :=
    xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
      halpha hzeros
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- The squared square-sample abscissa bound at its exact quadrupled width gives the same
quadratic thermal/source value budget. -/
theorem xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcessSquare_abscissa
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        (((1 + 4 * alpha : ℝ) : EReal))) :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * alpha ^ 2 * xiThermalCubicReciprocalMass := by
  have hzeros : XiZeroHalfPlaneBound alpha := by
    intro rho hzero
    by_cases hrho : 1 / 2 < rho.re
    · have hzeroBound :=
        four_mul_xi_zero_re_sub_one_le_squarePrimeWindowPositiveExcessSquare_abscissa
          hzero hrho
      have hreal : 4 * rho.re - 1 ≤ 1 + 4 * alpha := by
        exact_mod_cast hzeroBound.trans habscissa
      linarith
    · linarith
  have hbound :=
    xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
      halpha hzeros
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- The critical linear square-sample abscissa discharges the exact reverse thermal/source
inequality required by the operator-state RH criterion. -/
theorem xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcess_abscissa_le_one
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ≤
        ((1 : ℝ) : EReal)) :
    xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 := by
  have hbound :=
    xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcess_abscissa
      (alpha := 0) le_rfl (by simpa using habscissa)
  norm_num at hbound
  linarith

/-- The critical Hilbert square-sample abscissa gives the same exact operator-state saturation
discharge. -/
theorem xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        ((1 : ℝ) : EReal)) :
    xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 := by
  have hbound :=
    xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcessSquare_abscissa
      (alpha := 0) le_rfl (by simpa using habscissa)
  norm_num at hbound
  linarith

/-- Critical linear square-energy abscissa proves RH through the discharged thermal saturation
law. -/
theorem riemannHypothesis_of_squarePrimeWindowPositiveExcess_abscissa_le_one
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ≤
        ((1 : ℝ) : EReal)) :
    RiemannHypothesis :=
  xiThermalSecondMoment_le_source_iff_rh.mp
    (xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcess_abscissa_le_one
      habscissa)

/-- Critical Hilbert square-energy abscissa proves RH through the same one-value operator-state
saturation law. -/
theorem riemannHypothesis_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one
    (habscissa :
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        ((1 : ℝ) : EReal)) :
    RiemannHypothesis :=
  xiThermalSecondMoment_le_source_iff_rh.mp
    (xiThermalSecondMoment_le_source_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one
      habscissa)

/-- Linear square-sample energy at its natural doubled exponent gives an explicit quadratic
upper bound for the thermodynamic thermal/source value gap. -/
theorem xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcessEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => dyadicWeightedPrimeWindowPositiveExcess (m ^ 2))
        (1 + 2 * alpha))) :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * alpha ^ 2 * xiThermalCubicReciprocalMass := by
  have hzeros : XiZeroHalfPlaneBound alpha := fun rho hzero =>
    xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessEnergy
      halpha hSquare hzero
  have hbound :=
    xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
      halpha.le hzeros
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- Hilbert square-sample energy at the exact quadrupled exponent gives the same quadratic
thermal/source saturation budget. -/
theorem xiThermalSourceGap_le_of_squarePrimeWindowPositiveExcessSquareEnergy
    {alpha : ℝ} (halpha : 0 < alpha)
    (hSquare : Summable
      (realDirichletWeightedTerm
        (fun m => (dyadicWeightedPrimeWindowPositiveExcess (m ^ 2)) ^ 2)
        (1 + 4 * alpha))) :
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      4 * alpha ^ 2 * xiThermalCubicReciprocalMass := by
  have hzeros : XiZeroHalfPlaneBound alpha := fun rho hzero =>
    xi_zero_re_le_half_add_of_squarePrimeWindowPositiveExcessSquareEnergy
      halpha hSquare hzero
  have hbound :=
    xiThermalOrientationEnergy_le_cubicReciprocalMass_of_halfPlaneBound
      halpha.le hzeros
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  linarith

/-- **Thermodynamic-limit--prime square-energy spectrum.**  Finite KMS systems and their
thermodynamic second-moment limit exist unconditionally.  If the positive-transverse Xi divisor
is nonempty, then the limiting thermal value is strictly larger than the continued prime--Gamma
source value, while the linear and Hilbert square-sampled prime overshoots have exact global
abscissa lower bounds `1 + 2*delta` and `1 + 4*delta`, where
`delta = xiRightTransverseSup`.

Thus finite-system positivity is compatible with an off-line zero; source-value saturation and
critical square-energy are the two coupled boundary conditions. -/
theorem xiThermalLimit_primeSquareEnergySpectrum
    (hne : Nonempty XiRightZeroCopy) :
    (∀ M, FiniteKMSWightmanMomentSequence (xiThermalTruncation M)) ∧
      SequenceTraceHankelNonnegative xiThermalPositiveMoment ∧
      Tendsto (fun M => xiThermalTruncation M 1) atTop
        (nhds xiThermalSecondMoment) ∧
      normalizedPrimeArchMoment 1 < xiThermalSecondMoment ∧
      (((1 + 2 * xiRightTransverseSup : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessDirichletCoefficient ∧
      (((1 + 4 * xiRightTransverseSup : ℝ) : EReal)) ≤
        LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient := by
  have horientation :=
    xiThermalOrientationEnergy_pos_of_nonempty_xiRightZeroCopy hne
  have hsource := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  exact ⟨finiteKMSWightmanMomentSequence_xiThermalTruncation,
    sequenceTraceHankelNonnegative_xiThermalPositiveMoment,
    tendsto_xiThermalTruncation_one,
    by linarith,
    one_add_two_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcess_abscissa hne,
    one_add_four_mul_xiRightTransverseSup_le_squarePrimeWindowPositiveExcessSquare_abscissa hne⟩

end

end RHTower
