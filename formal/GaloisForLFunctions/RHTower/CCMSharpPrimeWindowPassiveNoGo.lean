import GaloisForLFunctions.HTGeometry.DirichletHalfPlaneSignRigidity
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowDirichlet

/-!
# Passive-impedance no-go for the sharp dyadic prime source

Route I proposed realizing

`Z(z) = dyadicSharpPrimeContinuedSource (1 - I*z)`

as a passive scalar impedance on the upper half-plane.  This module disproves both possible
Nevanlinna orientations on every upper tail.  The first oscillatory source coefficient is the
strictly positive coefficient at `2`; first-coefficient extraction then gives opposite imaginary
signs on the two lines `Re z = 1` and `Re z = -1`, arbitrarily high in the upper half-plane.

The proof is unconditional and uses only the literal Dirichlet source on its absolute-convergence
half-plane.  Internal network coupling cannot evade a value-level contradiction after equality with
this source is required on an open overlap.
-/

open Complex Filter Real LSeries

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-- Complex form of the real sharp dyadic source coefficient. -/
abbrev dyadicSharpPrimeSourceComplexCoeff (n : ℕ) : ℂ :=
  ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)

/-- The exact source sequence has a finite absolute-convergence abscissa. -/
theorem dyadicSharpPrimeSourceComplexCoeff_abscissa_lt_top :
    LSeries.abscissaOfAbsConv dyadicSharpPrimeSourceComplexCoeff < ⊤ := by
  have hs : LSeriesSummable dyadicSharpPrimeSourceComplexCoeff (2 : ℂ) :=
    dyadicSharpPrimeSourceCoefficient_LSeriesSummable (by norm_num)
  exact hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)

/-- The first nonconstant sharp source coefficient is strictly positive.  Explicitly,
`S(2) = 4 * (sqrt 2 - 1) - sqrt 2 * log 2 > 0`. -/
theorem dyadicSharpPrimeSourceComplexCoeff_two_pos :
    0 < (dyadicSharpPrimeSourceComplexCoeff 2).re := by
  simp only [dyadicSharpPrimeSourceComplexCoeff, ofReal_re]
  exact (by
    have hlog : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
      linarith
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hfour : 4 < 3 * Real.sqrt 2 := by nlinarith
    have hsqrtne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    rw [dyadicSharpPrimeSourceCoefficient, dyadicWeightedPrimeWindow]
    norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    field_simp
    nlinarith)

/-- The positive unit-frequency phase of the first oscillatory coefficient. -/
theorem two_cpow_I_im_pos : 0 < ((2 : ℂ) ^ Complex.I).im := by
  rw [show ((2 : ℂ) ^ Complex.I).im = Real.sin (Real.log 2) by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    rw [← Complex.ofNat_log]
    exact Complex.exp_ofReal_mul_I_im (Real.log 2)]
  apply Real.sin_pos_of_pos_of_lt_pi (Real.log_pos (by norm_num))
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  linarith [Real.pi_gt_three]

/-- The conjugate unit-frequency phase is strictly negative. -/
theorem two_cpow_neg_I_im_neg : ((2 : ℂ) ^ (-Complex.I)).im < 0 := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num)]
  rw [← Complex.ofNat_log]
  have harg : ((Real.log 2 : ℝ) : ℂ) * (-Complex.I) =
      ((-Real.log 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  exact neg_neg_of_pos (by
    apply Real.sin_pos_of_pos_of_lt_pi (Real.log_pos (by norm_num))
    have hlog : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
      linarith
    linarith [Real.pi_gt_three])

/-- The positive first mode controls the peeled `+I` twist eventually. -/
theorem eventually_dyadicSharpPrimePeeledTwist_I_im_pos :
    ∀ᶠ x : ℝ in atTop,
      0 < (LSeries
        (lseriesPeeledCoeff
          (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff Complex.I) 1)
        (x : ℂ)).im := by
  apply eventually_lseriesPeeledPowerTwist_im_pos 1 Complex.I
    dyadicSharpPrimeSourceComplexCoeff_abscissa_lt_top
  rw [dyadicSharpPrimeSourceComplexCoeff]
  simp only [Complex.mul_im, ofReal_re, ofReal_im, zero_mul]
  simpa [dyadicSharpPrimeSourceComplexCoeff] using
    mul_pos dyadicSharpPrimeSourceComplexCoeff_two_pos two_cpow_I_im_pos

/-- The conjugate first mode controls the peeled `-I` twist eventually. -/
theorem eventually_dyadicSharpPrimePeeledTwist_neg_I_im_neg :
    ∀ᶠ x : ℝ in atTop,
      (LSeries
        (lseriesPeeledCoeff
          (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff (-Complex.I)) 1)
        (x : ℂ)).im < 0 := by
  apply eventually_lseriesPeeledPowerTwist_im_neg 1 (-Complex.I)
    dyadicSharpPrimeSourceComplexCoeff_abscissa_lt_top
  rw [dyadicSharpPrimeSourceComplexCoeff]
  simp only [Complex.mul_im, ofReal_re, ofReal_im, zero_mul]
  simpa [dyadicSharpPrimeSourceComplexCoeff] using
    mul_neg_of_pos_of_neg dyadicSharpPrimeSourceComplexCoeff_two_pos
      two_cpow_neg_I_im_neg

/-- On the initial half-plane, the peeled `+I` twist has the same imaginary part as the literal
continued source on `x-I`; the deleted index-one coefficient is real. -/
theorem dyadicSharpPrimePeeledTwist_I_im_eq_continuedSource
    {x : ℝ} (hx : 3 / 2 < x) :
    (LSeries
      (lseriesPeeledCoeff
        (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff Complex.I) 1)
      (x : ℂ)).im =
      (dyadicSharpPrimeContinuedSource ((x : ℂ) - Complex.I)).im := by
  have hre : 3 / 2 < ((x : ℂ) - Complex.I).re := by simpa using hx
  have hs : LSeriesSummable dyadicSharpPrimeSourceComplexCoeff ((x : ℂ) - Complex.I) :=
    dyadicSharpPrimeSourceCoefficient_LSeriesSummable hre
  have htwist : LSeriesSummable
      (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff Complex.I) (x : ℂ) :=
    (LSeriesSummable_powerTwist _ _ _).2 (by simpa using hs)
  have hsource : LSeries dyadicSharpPrimeSourceComplexCoeff ((x : ℂ) - Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) - Complex.I) := by
    exact LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hre
  rw [LSeries_peeled_eq_sub_sum htwist 1, LSeries_powerTwist]
  rw [hsource]
  norm_num [Finset.sum_range_succ, LSeries.term, lseriesPowerTwistCoeff]

/-- Conjugate source-overlap identity for the peeled `-I` twist. -/
theorem dyadicSharpPrimePeeledTwist_neg_I_im_eq_continuedSource
    {x : ℝ} (hx : 3 / 2 < x) :
    (LSeries
      (lseriesPeeledCoeff
        (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff (-Complex.I)) 1)
      (x : ℂ)).im =
      (dyadicSharpPrimeContinuedSource ((x : ℂ) + Complex.I)).im := by
  have hre : 3 / 2 < ((x : ℂ) + Complex.I).re := by simpa using hx
  have hs : LSeriesSummable dyadicSharpPrimeSourceComplexCoeff ((x : ℂ) + Complex.I) :=
    dyadicSharpPrimeSourceCoefficient_LSeriesSummable hre
  have htwist : LSeriesSummable
      (lseriesPowerTwistCoeff dyadicSharpPrimeSourceComplexCoeff (-Complex.I)) (x : ℂ) :=
    (LSeriesSummable_powerTwist _ _ _).2 (by simpa using hs)
  have hsource : LSeries dyadicSharpPrimeSourceComplexCoeff ((x : ℂ) + Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) + Complex.I) := by
    exact LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hre
  rw [LSeries_peeled_eq_sub_sum htwist 1, LSeries_powerTwist]
  rw [show (x : ℂ) - -Complex.I = (x : ℂ) + Complex.I by ring]
  rw [hsource]
  norm_num [Finset.sum_range_succ, LSeries.term, lseriesPowerTwistCoeff]

/-- The source is eventually in the open upper half-plane on `x-I`. -/
theorem eventually_dyadicSharpPrimeContinuedSource_sub_I_im_pos :
    ∀ᶠ x : ℝ in atTop,
      0 < (dyadicSharpPrimeContinuedSource ((x : ℂ) - Complex.I)).im := by
  filter_upwards [eventually_dyadicSharpPrimePeeledTwist_I_im_pos,
    eventually_gt_atTop (3 / 2 : ℝ)] with x hsign hx
  rw [← dyadicSharpPrimePeeledTwist_I_im_eq_continuedSource hx]
  exact hsign

/-- The source is eventually in the open lower half-plane on `x+I`. -/
theorem eventually_dyadicSharpPrimeContinuedSource_add_I_im_neg :
    ∀ᶠ x : ℝ in atTop,
      (dyadicSharpPrimeContinuedSource ((x : ℂ) + Complex.I)).im < 0 := by
  filter_upwards [eventually_dyadicSharpPrimePeeledTwist_neg_I_im_neg,
    eventually_gt_atTop (3 / 2 : ℝ)] with x hsign hx
  rw [← dyadicSharpPrimePeeledTwist_neg_I_im_eq_continuedSource hx]
  exact hsign

/-- Literal source in Route I's impedance coordinate `s = 1 - I*z`. -/
def dyadicSharpPrimeImpedance (z : ℂ) : ℂ :=
  dyadicSharpPrimeContinuedSource (1 - Complex.I * z)

/-- `Re z = 1` corresponds to the source line `s = x-I`. -/
theorem dyadicSharpPrimeImpedance_posLine (x : ℝ) :
    dyadicSharpPrimeImpedance
        ((1 : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) - Complex.I) := by
  rw [dyadicSharpPrimeImpedance]
  congr 1
  rw [mul_add, mul_one]
  have hmid : Complex.I * (((x - 1 : ℝ) : ℂ) * Complex.I) =
      ((x - 1 : ℝ) : ℂ) * (Complex.I * Complex.I) := by ring
  rw [hmid, Complex.I_mul_I]
  push_cast
  ring

/-- `Re z = -1` corresponds to the conjugate source line `s = x+I`. -/
theorem dyadicSharpPrimeImpedance_negLine (x : ℝ) :
    dyadicSharpPrimeImpedance
        ((-1 : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) + Complex.I) := by
  rw [dyadicSharpPrimeImpedance]
  congr 1
  rw [mul_add]
  have hmid : Complex.I * (((x - 1 : ℝ) : ℂ) * Complex.I) =
      ((x - 1 : ℝ) : ℂ) * (Complex.I * Complex.I) := by ring
  rw [hmid, Complex.I_mul_I]
  push_cast
  ring

/-- Positive-imaginary witnesses occur above every prescribed height. -/
theorem exists_high_dyadicSharpPrimeImpedance_im_pos (Y : ℝ) :
    ∃ z : ℂ, Y < z.im ∧ 0 < (dyadicSharpPrimeImpedance z).im := by
  have hevent := eventually_dyadicSharpPrimeContinuedSource_sub_I_im_pos.and
    (eventually_gt_atTop (Y + 1))
  obtain ⟨x, hsign, hx⟩ := hevent.exists
  refine ⟨(1 : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero]
    linarith
  · rw [dyadicSharpPrimeImpedance_posLine]
    exact hsign

/-- Negative-imaginary witnesses occur above every prescribed height. -/
theorem exists_high_dyadicSharpPrimeImpedance_im_neg (Y : ℝ) :
    ∃ z : ℂ, Y < z.im ∧ (dyadicSharpPrimeImpedance z).im < 0 := by
  have hevent := eventually_dyadicSharpPrimeContinuedSource_add_I_im_neg.and
    (eventually_gt_atTop (Y + 1))
  obtain ⟨x, hsign, hx⟩ := hevent.exists
  refine ⟨(-1 : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · simp only [Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, zero_mul, add_zero]
    linarith
  · rw [dyadicSharpPrimeImpedance_negLine]
    exact hsign

/-- **Terminal Herglotz no-go.**  The literal Route-I impedance does not map any upper tail into
the closed upper half-plane. -/
theorem dyadicSharpPrimeImpedance_not_upperHalfPlaneValued_above (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im → 0 ≤ (dyadicSharpPrimeImpedance z).im) := by
  intro h
  obtain ⟨z, hz, hneg⟩ := exists_high_dyadicSharpPrimeImpedance_im_neg Y
  exact hneg.not_ge (h z hz)

/-- **Terminal anti-Herglotz no-go.**  The literal Route-I impedance does not map any upper tail
into the closed lower half-plane. -/
theorem dyadicSharpPrimeImpedance_not_lowerHalfPlaneValued_above (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im → (dyadicSharpPrimeImpedance z).im ≤ 0) := by
  intro h
  obtain ⟨z, hz, hpos⟩ := exists_high_dyadicSharpPrimeImpedance_im_pos Y
  exact hpos.not_ge (h z hz)

end RHTower
