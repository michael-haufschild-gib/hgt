import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaAntipodalPolarization

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set
open GaloisForLFunctions

noncomputable section

namespace RHTower

/-- Common-degree shifted reversal of the left hard-edge polynomial channel. -/
def routeUHardEdgeCommonLeftReversedPolynomial
    (a : ℝ) (P Q : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedReversedPolynomial (a ^ 2)
    (routeUHardEdgeCommonLiftDegree a P Q)
    (routeUHardEdgeCommonLeftCoefficients a P Q)

/-- Common-degree shifted reversal of the right hard-edge polynomial channel. -/
def routeUHardEdgeCommonRightReversedPolynomial
    (a : ℝ) (P Q : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedReversedPolynomial (a ^ 2)
    (routeUHardEdgeCommonLiftDegree a P Q)
    (routeUHardEdgeCommonRightCoefficients a P Q)

/-- Shifted reversal of a hard-edge polynomial padded to a prescribed reciprocal degree. -/
def routeUHardEdgeDegreePaddedReversedPolynomial
    (a : ℝ) (d : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedReversedPolynomial (a ^ 2) d
    (Polynomial.toFn (d + 1) (xiHardEdgeReciprocalPolynomial a P))

theorem eval_routeUHardEdgeDegreePaddedReversedPolynomial
    (a : ℝ) (d : ℕ) (P : Polynomial ℝ)
    (hdeg : (xiHardEdgeReciprocalPolynomial a P).natDegree ≤ d)
    {W : ℝ} (hW : a ^ 2 + W ≠ 0) :
    (routeUHardEdgeDegreePaddedReversedPolynomial a d P).eval W =
      (a ^ 2 + W) ^ d * P.eval ((a ^ 2 - W) / (a ^ 2 + W)) := by
  let c := Polynomial.toFn (d + 1) (xiHardEdgeReciprocalPolynomial a P)
  have hden : ((a ^ 2 : ℝ) : ℂ) + (W : ℂ) ≠ 0 := by
    exact_mod_cast hW
  have h := eval_xiShiftedReversedPolynomial_eq (a ^ 2) d c (W : ℂ) hden
  have hof : Polynomial.ofFn (d + 1) c = xiHardEdgeReciprocalPolynomial a P := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hdeg)
  rw [hof, evalRealPolynomial_xiHardEdgeReciprocalPolynomial] at h
  have harg : (((2 * a ^ 2 : ℝ) : ℂ) *
        ((((a ^ 2 : ℝ) : ℂ) + (W : ℂ))⁻¹) - 1) =
      (((a ^ 2 - W) / (a ^ 2 + W) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hW]
    ring
  rw [harg, evalRealPolynomial_ofReal] at h
  have hsum : (((a ^ 2 : ℝ) : ℂ) + (W : ℂ)) = ((a ^ 2 + W : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsum] at h
  change (xiShiftedReversedPolynomial (a ^ 2) d c).eval W = _
  have hre := congrArg Complex.re h
  simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  exact hre

theorem eval_routeUHardEdgeCommonLeftReversedPolynomial
    (a : ℝ) (P Q : Polynomial ℝ) {W : ℝ} (hW : a ^ 2 + W ≠ 0) :
    (routeUHardEdgeCommonLeftReversedPolynomial a P Q).eval W =
      (a ^ 2 + W) ^ routeUHardEdgeCommonLiftDegree a P Q *
        P.eval ((a ^ 2 - W) / (a ^ 2 + W)) := by
  let d := routeUHardEdgeCommonLiftDegree a P Q
  let c := routeUHardEdgeCommonLeftCoefficients a P Q
  have hden : ((a ^ 2 : ℝ) : ℂ) + (W : ℂ) ≠ 0 := by
    exact_mod_cast hW
  have h := eval_xiShiftedReversedPolynomial_eq (a ^ 2) d c (W : ℂ) hden
  rw [show Polynomial.ofFn (d + 1) c = xiHardEdgeReciprocalPolynomial a P by
    exact ofFn_routeUHardEdgeCommonLeftCoefficients a P Q] at h
  rw [evalRealPolynomial_xiHardEdgeReciprocalPolynomial] at h
  have harg : (((2 * a ^ 2 : ℝ) : ℂ) *
        ((((a ^ 2 : ℝ) : ℂ) + (W : ℂ))⁻¹) - 1) =
      (((a ^ 2 - W) / (a ^ 2 + W) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hW]
    ring
  rw [harg, evalRealPolynomial_ofReal] at h
  have hsum : (((a ^ 2 : ℝ) : ℂ) + (W : ℂ)) = ((a ^ 2 + W : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsum] at h
  change (xiShiftedReversedPolynomial (a ^ 2) d c).eval W = _
  have hre := congrArg Complex.re h
  simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  simpa only [d] using hre

theorem eval_routeUHardEdgeCommonRightReversedPolynomial
    (a : ℝ) (P Q : Polynomial ℝ) {W : ℝ} (hW : a ^ 2 + W ≠ 0) :
    (routeUHardEdgeCommonRightReversedPolynomial a P Q).eval W =
      (a ^ 2 + W) ^ routeUHardEdgeCommonLiftDegree a P Q *
        Q.eval ((a ^ 2 - W) / (a ^ 2 + W)) := by
  let d := routeUHardEdgeCommonLiftDegree a P Q
  let c := routeUHardEdgeCommonRightCoefficients a P Q
  have hden : ((a ^ 2 : ℝ) : ℂ) + (W : ℂ) ≠ 0 := by
    exact_mod_cast hW
  have h := eval_xiShiftedReversedPolynomial_eq (a ^ 2) d c (W : ℂ) hden
  rw [show Polynomial.ofFn (d + 1) c = xiHardEdgeReciprocalPolynomial a Q by
    exact ofFn_routeUHardEdgeCommonRightCoefficients a P Q] at h
  rw [evalRealPolynomial_xiHardEdgeReciprocalPolynomial] at h
  have harg : (((2 * a ^ 2 : ℝ) : ℂ) *
        ((((a ^ 2 : ℝ) : ℂ) + (W : ℂ))⁻¹) - 1) =
      (((a ^ 2 - W) / (a ^ 2 + W) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hW]
    ring
  rw [harg, evalRealPolynomial_ofReal] at h
  have hsum : (((a ^ 2 : ℝ) : ℂ) + (W : ℂ)) = ((a ^ 2 + W : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsum] at h
  change (xiShiftedReversedPolynomial (a ^ 2) d c).eval W = _
  have hre := congrArg Complex.re h
  simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  simpa only [d] using hre

theorem xiShiftedReversedPolynomial_add
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    xiShiftedReversedPolynomial y d (c + e) =
      xiShiftedReversedPolynomial y d c + xiShiftedReversedPolynomial y d e := by
  rw [xiShiftedReversedPolynomial, xiShiftedReversedPolynomial,
    xiShiftedReversedPolynomial]
  simp only [Pi.add_apply, Polynomial.C_add, add_mul, Finset.sum_add_distrib]

theorem xiShiftedReversedPolynomial_sub
    (y : ℝ) (d : ℕ) (c e : Fin (d + 1) → ℝ) :
    xiShiftedReversedPolynomial y d (c - e) =
      xiShiftedReversedPolynomial y d c - xiShiftedReversedPolynomial y d e := by
  rw [xiShiftedReversedPolynomial, xiShiftedReversedPolynomial,
    xiShiftedReversedPolynomial]
  simp only [Pi.sub_apply, Polynomial.C_sub, sub_mul, Finset.sum_sub_distrib]

/-- Pointwise polarization of the literal nonnegative polynomial--Gaussian density. -/
theorem routeUPolynomialGaussianDensity_norm_polarization
    (Q R : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    (‖routeUPolynomialGaussianDensity (Q + R) t x‖ -
        ‖routeUPolynomialGaussianDensity (Q - R) t x‖) / 4 =
      Q.eval (x ^ 2) * R.eval (x ^ 2) * Real.exp (-(t.1 * x ^ 2)) := by
  simp only [routeUPolynomialGaussianDensity, evenSquarePolynomial,
    Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.eval_add,
    Polynomial.eval_sub, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg, abs_of_nonneg]
  · ring
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)

theorem eval_routeUHardEdgeEvenChannel_neg
    (P : Polynomial ℝ) (x : ℝ) :
    (routeUHardEdgeEvenChannel P).eval (-x) =
      (routeUHardEdgeEvenChannel P).eval x := by
  have h := congrArg (fun Q : Polynomial ℝ => Q.eval x)
    (routeUHardEdgeAntipodalPolynomial_evenChannel P)
  simpa only [eval_routeUHardEdgeAntipodalPolynomial] using h

theorem eval_routeUHardEdgeOddChannel_neg
    (P : Polynomial ℝ) (x : ℝ) :
    (routeUHardEdgeOddChannel P).eval (-x) =
      -(routeUHardEdgeOddChannel P).eval x := by
  have h := congrArg (fun Q : Polynomial ℝ => Q.eval x)
    (routeUHardEdgeAntipodalPolynomial_oddChannel P)
  simpa only [eval_routeUHardEdgeAntipodalPolynomial, Polynomial.eval_neg] using h

theorem eval_routeUHardEdgeOddChannel_zero (P : Polynomial ℝ) :
    (routeUHardEdgeOddChannel P).eval 0 = 0 := by
  have h := eval_routeUHardEdgeOddChannel_neg P 0
  norm_num at h ⊢
  linarith

/-- Common reciprocal degree of the actual antipodal channel pair. -/
def routeUHardEdgeKelvinDegree (a : ℝ) (P : Polynomial ℝ) : ℕ :=
  routeUHardEdgeCommonLiftDegree a
    (routeUHardEdgeEvenChannel P) (routeUHardEdgeOddChannel P)

/-- Common-degree shifted reversal of the actual even antipodal channel. -/
def routeUHardEdgeKelvinEvenReversedPolynomial
    (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  routeUHardEdgeCommonLeftReversedPolynomial a
    (routeUHardEdgeEvenChannel P) (routeUHardEdgeOddChannel P)

/-- Common-degree shifted reversal of the actual odd antipodal channel. -/
def routeUHardEdgeKelvinOddReversedPolynomial
    (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  routeUHardEdgeCommonRightReversedPolynomial a
    (routeUHardEdgeEvenChannel P) (routeUHardEdgeOddChannel P)

private theorem routeUHardEdgeKelvinCoordinate_real_inversion
    {a W : ℝ} (ha : 0 < a) (hW : 0 < W) :
    (a ^ 2 - (a ^ 2) ^ 2 / W) / (a ^ 2 + (a ^ 2) ^ 2 / W) =
      -((a ^ 2 - W) / (a ^ 2 + W)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hW0 : W ≠ 0 := ne_of_gt hW
  field_simp [ha0, hW0]
  ring

private theorem routeUHardEdgeKelvinDenominator_factor
    {a W : ℝ} (ha : 0 < a) (hW : 0 < W) :
    a ^ 2 + (a ^ 2) ^ 2 / W =
      (a ^ 2 / W) * (a ^ 2 + W) := by
  have hW0 : W ≠ 0 := ne_of_gt hW
  field_simp [hW0]
  ring

/-- Padding turns hard-edge antipody into an exact Kelvin covariance of shifted reversal. -/
theorem routeUHardEdgeDegreePaddedReversedPolynomial_antipodal_kelvin
    {a W : ℝ} (ha : 0 < a) (hW : 0 < W) (d : ℕ) (P : Polynomial ℝ)
    (hdeg : (xiHardEdgeReciprocalPolynomial a P).natDegree ≤ d)
    (hdegAnti : (xiHardEdgeReciprocalPolynomial a
      (routeUHardEdgeAntipodalPolynomial P)).natDegree ≤ d) :
    (routeUHardEdgeDegreePaddedReversedPolynomial a d
        (routeUHardEdgeAntipodalPolynomial P)).eval W =
      (W / a ^ 2) ^ d *
        (routeUHardEdgeDegreePaddedReversedPolynomial a d P).eval
          ((a ^ 2) ^ 2 / W) := by
  have hdenW : a ^ 2 + W ≠ 0 := by positivity
  have hdenInv : a ^ 2 + (a ^ 2) ^ 2 / W ≠ 0 := by positivity
  rw [eval_routeUHardEdgeDegreePaddedReversedPolynomial _ _ _ hdegAnti hdenW,
    eval_routeUHardEdgeDegreePaddedReversedPolynomial _ _ _ hdeg hdenInv,
    routeUHardEdgeKelvinCoordinate_real_inversion ha hW,
    eval_routeUHardEdgeAntipodalPolynomial,
    routeUHardEdgeKelvinDenominator_factor ha hW,
    mul_pow]
  have hcancel : (W / a ^ 2) * (a ^ 2 / W) = 1 := by
    field_simp [ne_of_gt ha, ne_of_gt hW]
  have hpowCancel : (W / a ^ 2) ^ d * (a ^ 2 / W) ^ d = 1 := by
    rw [← mul_pow, hcancel, one_pow]
  calc
    (a ^ 2 + W) ^ d *
        P.eval (-((a ^ 2 - W) / (a ^ 2 + W))) =
      1 * ((a ^ 2 + W) ^ d *
        P.eval (-((a ^ 2 - W) / (a ^ 2 + W)))) := by ring
    _ = ((W / a ^ 2) ^ d * (a ^ 2 / W) ^ d) *
        ((a ^ 2 + W) ^ d *
          P.eval (-((a ^ 2 - W) / (a ^ 2 + W)))) := by rw [hpowCancel]
    _ = (W / a ^ 2) ^ d *
        ((a ^ 2 / W) ^ d * (a ^ 2 + W) ^ d *
          P.eval (-((a ^ 2 - W) / (a ^ 2 + W)))) := by ring

/-- Even shifted reversal is Kelvin-invariant at the common reciprocal degree. -/
theorem routeUHardEdgeKelvinEvenReversedPolynomial_inversion
    {a W : ℝ} (ha : 0 < a) (hW : 0 < W) (P : Polynomial ℝ) :
    (routeUHardEdgeKelvinEvenReversedPolynomial a P).eval
        ((a ^ 2) ^ 2 / W) =
      (a ^ 2 / W) ^ routeUHardEdgeKelvinDegree a P *
        (routeUHardEdgeKelvinEvenReversedPolynomial a P).eval W := by
  have hdenW : a ^ 2 + W ≠ 0 := by positivity
  have hdenInv : a ^ 2 + (a ^ 2) ^ 2 / W ≠ 0 := by positivity
  rw [routeUHardEdgeKelvinEvenReversedPolynomial,
    eval_routeUHardEdgeCommonLeftReversedPolynomial _ _ _ hdenInv,
    eval_routeUHardEdgeCommonLeftReversedPolynomial _ _ _ hdenW,
    routeUHardEdgeKelvinCoordinate_real_inversion ha hW,
    eval_routeUHardEdgeEvenChannel_neg,
    routeUHardEdgeKelvinDenominator_factor ha hW,
    mul_pow]
  simp only [routeUHardEdgeKelvinDegree]
  ring

/-- Odd shifted reversal is Kelvin-anti-invariant at the common reciprocal degree. -/
theorem routeUHardEdgeKelvinOddReversedPolynomial_inversion
    {a W : ℝ} (ha : 0 < a) (hW : 0 < W) (P : Polynomial ℝ) :
    (routeUHardEdgeKelvinOddReversedPolynomial a P).eval
        ((a ^ 2) ^ 2 / W) =
      -(a ^ 2 / W) ^ routeUHardEdgeKelvinDegree a P *
        (routeUHardEdgeKelvinOddReversedPolynomial a P).eval W := by
  have hdenW : a ^ 2 + W ≠ 0 := by positivity
  have hdenInv : a ^ 2 + (a ^ 2) ^ 2 / W ≠ 0 := by positivity
  rw [routeUHardEdgeKelvinOddReversedPolynomial,
    eval_routeUHardEdgeCommonRightReversedPolynomial _ _ _ hdenInv,
    eval_routeUHardEdgeCommonRightReversedPolynomial _ _ _ hdenW,
    routeUHardEdgeKelvinCoordinate_real_inversion ha hW,
    eval_routeUHardEdgeOddChannel_neg,
    routeUHardEdgeKelvinDenominator_factor ha hW,
    mul_pow]
  simp only [routeUHardEdgeKelvinDegree]
  ring

/-- Literal Gaussian even--odd cross density of the common-degree shifted reversals. -/
def routeUHardEdgeKelvinCrossDensity
    (a : ℝ) (P : Polynomial ℝ) (t x : ℝ) : ℝ :=
  (routeUHardEdgeKelvinEvenReversedPolynomial a P).eval (x ^ 2) *
    (routeUHardEdgeKelvinOddReversedPolynomial a P).eval (x ^ 2) *
      Real.exp (-(t * x ^ 2))

/-- The Kelvin cross density is exactly the archimedean polarization occurring in the literal
completed prime--Gamma cross balance. -/
theorem routeUHardEdgeKelvinCrossDensity_eq_archPolarization
    (a : ℝ) (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (x : ℝ) :
    routeUHardEdgeKelvinCrossDensity a P t.1 x =
      (‖routeUPolynomialGaussianDensity
          (xiShiftedReversedPolynomial (a ^ 2) (routeUHardEdgeKelvinDegree a P)
            (routeUHardEdgeCommonFullCoefficients a
              (routeUHardEdgeEvenChannel P) (routeUHardEdgeOddChannel P))) t x‖ -
        ‖routeUPolynomialGaussianDensity
          (xiShiftedReversedPolynomial (a ^ 2) (routeUHardEdgeKelvinDegree a P)
            (routeUHardEdgeCommonAntipodalCoefficients a
              (routeUHardEdgeEvenChannel P) (routeUHardEdgeOddChannel P))) t x‖) / 4 := by
  let E := routeUHardEdgeEvenChannel P
  let O := routeUHardEdgeOddChannel P
  let d := routeUHardEdgeKelvinDegree a P
  let c := routeUHardEdgeCommonLeftCoefficients a E O
  let e := routeUHardEdgeCommonRightCoefficients a E O
  have hpolar := routeUPolynomialGaussianDensity_norm_polarization
    (xiShiftedReversedPolynomial (a ^ 2) d c)
    (xiShiftedReversedPolynomial (a ^ 2) d e) t x
  rw [← xiShiftedReversedPolynomial_add,
    ← xiShiftedReversedPolynomial_sub] at hpolar
  exact hpolar.symm

/-- The cross density is anti-covariant under physical hard-edge inversion. -/
theorem routeUHardEdgeKelvinCrossDensity_inversion
    {a t x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinCrossDensity a P t (a ^ 2 / x) =
      -(a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P) *
        Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) *
          routeUHardEdgeKelvinCrossDensity a P t x := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have harg : (a ^ 2 / x) ^ 2 = (a ^ 2) ^ 2 / x ^ 2 := by
    field_simp [ne_of_gt hx]
  have heven := routeUHardEdgeKelvinEvenReversedPolynomial_inversion
    ha hx2 P
  have hodd := routeUHardEdgeKelvinOddReversedPolynomial_inversion
    ha hx2 P
  rw [← harg] at heven hodd
  rw [routeUHardEdgeKelvinCrossDensity, routeUHardEdgeKelvinCrossDensity,
    heven, hodd]
  have hpow :
      (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P) =
        (a ^ 2 / x ^ 2) ^ routeUHardEdgeKelvinDegree a P *
          (a ^ 2 / x ^ 2) ^ routeUHardEdgeKelvinDegree a P := by
    rw [two_mul, pow_add]
  rw [hpow]
  have hexp : Real.exp (-(t * (a ^ 2 / x) ^ 2)) =
      Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) *
        Real.exp (-(t * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem routeUHardEdgeKelvinCrossDensity_inversion_neg_of_pos
    {a t x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ)
    (hpos : 0 < routeUHardEdgeKelvinCrossDensity a P t x) :
    routeUHardEdgeKelvinCrossDensity a P t (a ^ 2 / x) < 0 := by
  rw [routeUHardEdgeKelvinCrossDensity_inversion ha hx P]
  have hfactor : 0 <
      (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P) *
        Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) := by
    positivity
  nlinarith

theorem routeUHardEdgeKelvinCrossDensity_inversion_pos_of_neg
    {a t x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ)
    (hneg : routeUHardEdgeKelvinCrossDensity a P t x < 0) :
    0 < routeUHardEdgeKelvinCrossDensity a P t (a ^ 2 / x) := by
  rw [routeUHardEdgeKelvinCrossDensity_inversion ha hx P]
  have hfactor : 0 <
      (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P) *
        Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) := by
    positivity
  nlinarith

/-- The odd cross channel vanishes at the self-dual hard-edge seam. -/
theorem routeUHardEdgeKelvinOddReversedPolynomial_selfDual_zero
    {a : ℝ} (ha : 0 < a) (P : Polynomial ℝ) :
    (routeUHardEdgeKelvinOddReversedPolynomial a P).eval (a ^ 2) = 0 := by
  have hden : a ^ 2 + a ^ 2 ≠ 0 := by positivity
  rw [routeUHardEdgeKelvinOddReversedPolynomial,
    eval_routeUHardEdgeCommonRightReversedPolynomial _ _ _ hden]
  have hcoord : (a ^ 2 - a ^ 2) / (a ^ 2 + a ^ 2) = (0 : ℝ) := by
    field_simp [ne_of_gt ha]
    ring
  rw [hcoord, eval_routeUHardEdgeOddChannel_zero, mul_zero]

theorem routeUHardEdgeKelvinCrossDensity_selfDual_zero
    {a t : ℝ} (ha : 0 < a) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinCrossDensity a P t a = 0 := by
  rw [routeUHardEdgeKelvinCrossDensity, routeUHardEdgeKelvinOddReversedPolynomial_selfDual_zero
    ha P, mul_zero, zero_mul]

/-- Jacobian-paired oriented cross current for an arbitrary real source weight. -/
def routeUHardEdgeKelvinPairedCrossCurrent
    (a : ℝ) (P : Polynomial ℝ) (t : ℝ) (weight : ℝ → ℝ) (x : ℝ) : ℝ :=
  routeUHardEdgeKelvinCrossDensity a P t x * weight x +
    (a ^ 2 / x ^ 2) *
      routeUHardEdgeKelvinCrossDensity a P t (a ^ 2 / x) *
        weight (a ^ 2 / x)

/-- Exact modular-weight defect carried by one Kelvin orbit. -/
theorem routeUHardEdgeKelvinPairedCrossCurrent_eq_weightDefect
    {a t x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (P : Polynomial ℝ) (weight : ℝ → ℝ) :
    routeUHardEdgeKelvinPairedCrossCurrent a P t weight x =
      routeUHardEdgeKelvinCrossDensity a P t x *
        (weight x -
          (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) *
            Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) *
              weight (a ^ 2 / x)) := by
  rw [routeUHardEdgeKelvinPairedCrossCurrent,
    routeUHardEdgeKelvinCrossDensity_inversion ha hx P]
  have hpow :
      (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) =
        (a ^ 2 / x ^ 2) *
          (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P) := by
    rw [pow_succ]
    ring
  rw [hpow]
  ring

/-- Literal Gamma-rate specialization of the Kelvin modular current. -/
theorem routeUHardEdgeKelvinPairedGammaCrossCurrent_eq_weightDefect
    {a t x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinPairedCrossCurrent a P t gammaHardyPhaseRate x =
      routeUHardEdgeKelvinCrossDensity a P t x *
        (gammaHardyPhaseRate x -
          (a ^ 2 / x ^ 2) ^ (2 * routeUHardEdgeKelvinDegree a P + 1) *
            Real.exp (-(t * ((a ^ 2 / x) ^ 2 - x ^ 2))) *
              gammaHardyPhaseRate (a ^ 2 / x)) := by
  exact routeUHardEdgeKelvinPairedCrossCurrent_eq_weightDefect
    ha hx P gammaHardyPhaseRate

end RHTower
