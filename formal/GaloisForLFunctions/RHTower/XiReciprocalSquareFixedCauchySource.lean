import GaloisForLFunctions.RHTower.XiReciprocalSquareCountableCauchySource
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

/-!
# One fixed Cauchy source value detects RH

The existing rank-one reciprocal-square criterion asks for quadratic reality at every regular
continued-Cauchy pole.  Functional-equation and Schwarz quartets make that family redundant.
For any one regular pole off both coordinate axes, its orientation defect is a nonzero scalar
multiple of a sum of nonnegative quartet variances.  Each variance vanishes exactly when its
centered Xi spectral point is real.

Thus one fixed scalar quadratic value detects RH.  The forward implication below is proved by the
explicit quartet decomposition, not by invoking an older RH equivalence or a density theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Contribution of one centered Xi spectral point to the imaginary part of the reciprocal-square
quadratic value at a Cauchy pole. -/
def xiReciprocalSquareCauchySpectralTerm (z a : ℂ) : ℝ :=
  -(a⁻¹ ^ (2 : ℕ)).im / Complex.normSq (a - z)

private lemma inv_sq_im (a : ℂ) :
    (a⁻¹ ^ (2 : ℕ)).im = -2 * a.re * a.im / Complex.normSq a ^ (2 : ℕ) := by
  rw [pow_two, mul_im, Complex.inv_re, Complex.inv_im]
  ring

theorem xiReciprocalSquareCauchySpectralTerm_eq (z a : ℂ) :
    xiReciprocalSquareCauchySpectralTerm z a =
      2 * a.re * a.im /
        (Complex.normSq a ^ (2 : ℕ) * Complex.normSq (a - z)) := by
  rw [xiReciprocalSquareCauchySpectralTerm, inv_sq_im]
  ring

private lemma inner_reciprocalSquare_cauchy_im (z a : ℂ) :
    (inner ℂ (a⁻¹ ^ (2 : ℕ) * (a - z)⁻¹) ((a - z)⁻¹)).im =
      xiReciprocalSquareCauchySpectralTerm z a := by
  rw [RCLike.inner_apply]
  rw [map_mul, map_pow, map_inv₀, map_inv₀]
  simp only [xiReciprocalSquareCauchySpectralTerm]
  rw [show (starRingEnd ℂ) (a - z) =
      (starRingEnd ℂ) a - (starRingEnd ℂ) z by simp]
  have hnorm :
      (starRingEnd ℂ) ((a - z)⁻¹) * (a - z)⁻¹ =
        (‖(a - z)⁻¹‖ : ℂ) ^ (2 : ℕ) := by
    exact RCLike.conj_mul ((a - z)⁻¹)
  rw [show (a - z)⁻¹ *
      (((starRingEnd ℂ) a)⁻¹ ^ (2 : ℕ) *
        ((starRingEnd ℂ) a - (starRingEnd ℂ) z)⁻¹) =
      ((starRingEnd ℂ) (a⁻¹ ^ (2 : ℕ))) *
        ((starRingEnd ℂ) ((a - z)⁻¹) * (a - z)⁻¹) by
      simp only [map_pow, map_inv₀, map_sub]
      ring]
  rw [hnorm, Complex.mul_im]
  have hrealRe (r : ℝ) : ((r : ℂ) ^ (2 : ℕ)).re = r ^ (2 : ℕ) := by
    rw [pow_two]
    simp [Complex.mul_re]
    ring
  have hrealIm (r : ℝ) : ((r : ℂ) ^ (2 : ℕ)).im = 0 := by
    rw [pow_two]
    simp [Complex.mul_im]
  rw [hrealRe, hrealIm]
  simp only [mul_zero, conj_im, norm_inv, inv_pow]
  rw [Complex.sq_norm]
  ring

private lemma real_quartet_identity
    (x y u v A B C D R Q : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) (hQ : Q ≠ 0)
    (hAeq : A = (x - u) ^ (2 : ℕ) + (y - v) ^ (2 : ℕ))
    (hBeq : B = (x - u) ^ (2 : ℕ) + (-y - v) ^ (2 : ℕ))
    (hCeq : C = (x + u) ^ (2 : ℕ) + (y + v) ^ (2 : ℕ))
    (hDeq : D = (x + u) ^ (2 : ℕ) + (-y + v) ^ (2 : ℕ))
    (hReq : R = x ^ (2 : ℕ) + y ^ (2 : ℕ) + u ^ (2 : ℕ) + v ^ (2 : ℕ)) :
    2 * x * y / Q * (1 / A - 1 / B + 1 / C - 1 / D) =
      64 * u * v * (x ^ (2 : ℕ) * y ^ (2 : ℕ) * R) / (Q * A * B * C * D) := by
  subst A
  subst B
  subst C
  subst D
  subst R
  field_simp
  ring

/-- Exact positive-variance identity for one functional-equation/Schwarz spectral quartet. -/
theorem xiReciprocalSquareCauchySpectralTerm_quartet
    (z a : ℂ)
    (ha : a ≠ 0) (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0)
    (hapz : a + z ≠ 0)
    (hcapz : (starRingEnd ℂ) a + z ≠ 0) :
    xiReciprocalSquareCauchySpectralTerm z a +
        xiReciprocalSquareCauchySpectralTerm z ((starRingEnd ℂ) a) +
        xiReciprocalSquareCauchySpectralTerm z (-a) +
        xiReciprocalSquareCauchySpectralTerm z (-(starRingEnd ℂ) a) =
      64 * z.re * z.im *
        (a.re ^ (2 : ℕ) * a.im ^ (2 : ℕ) *
          (Complex.normSq a + Complex.normSq z)) /
        (Complex.normSq a ^ (2 : ℕ) *
          Complex.normSq (a - z) *
          Complex.normSq ((starRingEnd ℂ) a - z) *
          Complex.normSq (a + z) *
          Complex.normSq ((starRingEnd ℂ) a + z)) := by
  have hnorma : Complex.normSq a ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr ha)
  have h1 : Complex.normSq (a - z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr haz)
  have h2 : Complex.normSq ((starRingEnd ℂ) a - z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hcaz)
  have h3 : Complex.normSq (a + z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hapz)
  have h4 : Complex.normSq ((starRingEnd ℂ) a + z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hcapz)
  rw [xiReciprocalSquareCauchySpectralTerm_eq,
    xiReciprocalSquareCauchySpectralTerm_eq,
    xiReciprocalSquareCauchySpectralTerm_eq,
    xiReciprocalSquareCauchySpectralTerm_eq]
  simp only [conj_re, conj_im, neg_re, neg_im, Complex.normSq_conj,
    Complex.normSq_neg]
  rw [show Complex.normSq (-a - z) = Complex.normSq (a + z) by
        rw [show -a - z = -(a + z) by ring, Complex.normSq_neg],
      show Complex.normSq (-(starRingEnd ℂ) a - z) =
          Complex.normSq ((starRingEnd ℂ) a + z) by
        rw [show -(starRingEnd ℂ) a - z =
          -((starRingEnd ℂ) a + z) by ring, Complex.normSq_neg]]
  simp only [neg_neg]
  rw [show
      2 * a.re * a.im /
              (Complex.normSq a ^ (2 : ℕ) * Complex.normSq (a - z)) +
            2 * a.re * -a.im /
              (Complex.normSq a ^ (2 : ℕ) *
                Complex.normSq ((starRingEnd ℂ) a - z)) +
          2 * -a.re * -a.im /
            (Complex.normSq a ^ (2 : ℕ) * Complex.normSq (a + z)) +
        2 * -a.re * a.im /
          (Complex.normSq a ^ (2 : ℕ) *
            Complex.normSq ((starRingEnd ℂ) a + z)) =
        2 * a.re * a.im / Complex.normSq a ^ (2 : ℕ) *
          (1 / Complex.normSq (a - z) -
            1 / Complex.normSq ((starRingEnd ℂ) a - z) +
            1 / Complex.normSq (a + z) -
            1 / Complex.normSq ((starRingEnd ℂ) a + z)) by ring]
  apply real_quartet_identity
      a.re a.im z.re z.im
      (Complex.normSq (a - z))
      (Complex.normSq ((starRingEnd ℂ) a - z))
      (Complex.normSq (a + z))
      (Complex.normSq ((starRingEnd ℂ) a + z))
      (Complex.normSq a + Complex.normSq z)
      (Complex.normSq a ^ (2 : ℕ))
      h1 h2 h3 h4 (pow_ne_zero 2 hnorma)
  · simp [Complex.normSq_apply, pow_two]
  · simp [Complex.normSq_apply, pow_two]
  · simp [Complex.normSq_apply, pow_two]
  · simp [Complex.normSq_apply, pow_two]
  · simp [Complex.normSq_apply, pow_two]
    ring

/-- Imaginary part of the reciprocal-square quadratic value at one regular continued-Cauchy
source pole. -/
def xiReciprocalSquareContinuedCauchyOrientationDefect
    (z : XiContinuedCauchyPoint) : ℝ :=
  (inner ℂ
    (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
    (xiWeilContinuedCauchyLp z)).im

theorem xiSpectralPoint_sub_continuedCauchyPoint_ne
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiSpectralPoint q - (z : ℂ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  exact z.1.property
    ((XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ)).mpr ⟨q, h⟩)

/-- Exact spectral expansion of one Cauchy orientation defect. -/
theorem xiReciprocalSquareContinuedCauchyOrientationDefect_eq_tsum
    (z : XiContinuedCauchyPoint) :
    xiReciprocalSquareContinuedCauchyOrientationDefect z =
      ∑' q : XiZeroCopy,
        xiReciprocalSquareCauchySpectralTerm (z : ℂ) (xiSpectralPoint q) := by
  rw [xiReciprocalSquareContinuedCauchyOrientationDefect, lp.inner_eq_tsum]
  have hsum : Summable (fun q : XiZeroCopy =>
      inner ℂ
        ((xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)) q)
        ((xiWeilContinuedCauchyLp z) q)) :=
    lp.summable_inner
      (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
      (xiWeilContinuedCauchyLp z)
  rw [Complex.im_tsum hsum]
  apply tsum_congr
  intro q
  rw [xiReciprocalSquareOperator_apply]
  change (inner ℂ
      ((xiSpectralPoint q)⁻¹ ^ (2 : ℕ) *
        (xiSpectralPoint q - (z : ℂ))⁻¹)
      ((xiSpectralPoint q - (z : ℂ))⁻¹)).im = _
  exact inner_reciprocalSquare_cauchy_im (z : ℂ) (xiSpectralPoint q)

theorem summable_xiReciprocalSquareCauchySpectralTerm
    (z : XiContinuedCauchyPoint) :
    Summable (fun q : XiZeroCopy =>
      xiReciprocalSquareCauchySpectralTerm (z : ℂ) (xiSpectralPoint q)) := by
  have hsum : Summable (fun q : XiZeroCopy =>
      inner ℂ
        ((xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)) q)
        ((xiWeilContinuedCauchyLp z) q)) :=
    lp.summable_inner
      (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
      (xiWeilContinuedCauchyLp z)
  have hsumIm : Summable (fun q : XiZeroCopy =>
      (inner ℂ
        ((xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)) q)
        ((xiWeilContinuedCauchyLp z) q)).im) := by
    apply hsum.norm.of_norm_bounded
    intro q
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  apply hsumIm.congr
  intro q
  rw [xiReciprocalSquareOperator_apply]
  change (inner ℂ
      ((xiSpectralPoint q)⁻¹ ^ (2 : ℕ) *
        (xiSpectralPoint q - (z : ℂ))⁻¹)
      ((xiSpectralPoint q - (z : ℂ))⁻¹)).im = _
  exact inner_reciprocalSquare_cauchy_im (z : ℂ) (xiSpectralPoint q)

/-- Four symmetry-related spectral contributions, indexed without quotienting the divisor. -/
def xiReciprocalSquareCauchyQuartetTerm
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) : ℝ :=
  xiReciprocalSquareCauchySpectralTerm (z : ℂ) (xiSpectralPoint q) +
    xiReciprocalSquareCauchySpectralTerm (z : ℂ)
      (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) +
    xiReciprocalSquareCauchySpectralTerm (z : ℂ)
      (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
    xiReciprocalSquareCauchySpectralTerm (z : ℂ)
      (xiSpectralPoint
        (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q)))

/-- The four symmetry pullbacks of a summable weight on the Xi divisor are jointly summable. -/
private theorem summable_quartet_of_summable {t : XiZeroCopy → ℝ} (ht : Summable t) :
    Summable (fun q => t q + t (xiZeroCopyLineConjEquiv q) + t (xiZeroCopyReflectEquiv q) +
      t (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))) := by
  have hline : Summable (fun q => t (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr ht
  have hreflect : Summable (fun q => t (xiZeroCopyReflectEquiv q)) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr ht
  have hboth : Summable (fun q => t (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hline
  exact ((ht.add hline).add hreflect).add hboth

/-- Each symmetry pullback has the same sum, so the quartet sums to four times the weight. -/
private theorem tsum_quartet_of_summable {t : XiZeroCopy → ℝ} (ht : Summable t) :
    ∑' q, (t q + t (xiZeroCopyLineConjEquiv q) + t (xiZeroCopyReflectEquiv q) +
      t (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))) = 4 * ∑' q, t q := by
  have hline : Summable (fun q => t (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr ht
  have hreflect : Summable (fun q => t (xiZeroCopyReflectEquiv q)) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr ht
  have hboth : Summable (fun q => t (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hline
  have hlineSum : (∑' q, t (xiZeroCopyLineConjEquiv q)) = ∑' q, t q :=
    xiZeroCopyLineConjEquiv.tsum_eq t
  have hreflectSum : (∑' q, t (xiZeroCopyReflectEquiv q)) = ∑' q, t q :=
    xiZeroCopyReflectEquiv.tsum_eq t
  have hbothSum : (∑' q, t (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))) = ∑' q, t q :=
    (xiZeroCopyReflectEquiv.trans xiZeroCopyLineConjEquiv).tsum_eq t
  rw [((ht.add hline).add hreflect).tsum_add hboth, (ht.add hline).tsum_add hreflect,
    ht.tsum_add hline, hlineSum, hreflectSum, hbothSum]
  ring

theorem summable_xiReciprocalSquareCauchyQuartetTerm
    (z : XiContinuedCauchyPoint) :
    Summable (xiReciprocalSquareCauchyQuartetTerm z) :=
  summable_quartet_of_summable
    (t := fun q => xiReciprocalSquareCauchySpectralTerm (z : ℂ) (xiSpectralPoint q))
    (summable_xiReciprocalSquareCauchySpectralTerm z)

theorem tsum_xiReciprocalSquareCauchyQuartetTerm
    (z : XiContinuedCauchyPoint) :
    ∑' q : XiZeroCopy, xiReciprocalSquareCauchyQuartetTerm z q =
      4 * xiReciprocalSquareContinuedCauchyOrientationDefect z := by
  rw [xiReciprocalSquareContinuedCauchyOrientationDefect_eq_tsum]
  exact tsum_quartet_of_summable
    (t := fun q => xiReciprocalSquareCauchySpectralTerm (z : ℂ) (xiSpectralPoint q))
    (summable_xiReciprocalSquareCauchySpectralTerm z)

/-- Nonnegative variance carried by one centered Xi quartet at one Cauchy pole. -/
def xiReciprocalSquareCauchyQuartetVariance (z a : ℂ) : ℝ :=
  (a.re ^ (2 : ℕ) * a.im ^ (2 : ℕ) *
      (Complex.normSq a + Complex.normSq z)) /
    (Complex.normSq a ^ (2 : ℕ) *
      Complex.normSq (a - z) *
      Complex.normSq ((starRingEnd ℂ) a - z) *
      Complex.normSq (a + z) *
      Complex.normSq ((starRingEnd ℂ) a + z))

theorem xiReciprocalSquareCauchyQuartetTerm_eq_variance
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiReciprocalSquareCauchyQuartetTerm z q =
      64 * (z : ℂ).re * (z : ℂ).im *
        xiReciprocalSquareCauchyQuartetVariance
          (z : ℂ) (xiSpectralPoint q) := by
  let a : ℂ := xiSpectralPoint q
  have ha : a ≠ 0 := xiSpectralPoint_ne_zero q
  have haz : a - (z : ℂ) ≠ 0 :=
    xiSpectralPoint_sub_continuedCauchyPoint_ne z q
  have hcaz : (starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  have hnegaz : -a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyReflectEquiv q)
  have hapz : a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegaz
    rw [show -a - (z : ℂ) = -(a + (z : ℂ)) by ring, h]
    simp
  have hnegcaz : -(starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect, xiSpectralPoint_lineConj,
      map_neg] using
        xiSpectralPoint_sub_continuedCauchyPoint_ne z
          (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))
  have hcapz : (starRingEnd ℂ) a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegcaz
    rw [show -(starRingEnd ℂ) a - (z : ℂ) =
      -((starRingEnd ℂ) a + (z : ℂ)) by ring, h]
    simp
  rw [xiReciprocalSquareCauchyQuartetTerm, xiSpectralPoint_lineConj,
    xiSpectralPoint_reflect, xiSpectralPoint_lineConj,
    xiSpectralPoint_reflect, map_neg]
  unfold xiReciprocalSquareCauchyQuartetVariance
  convert xiReciprocalSquareCauchySpectralTerm_quartet
    (z : ℂ) a ha haz hcaz hapz hcapz using 1
  simp only [a]
  ring

theorem xiReciprocalSquareCauchyQuartetVariance_nonneg
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    0 ≤ xiReciprocalSquareCauchyQuartetVariance
      (z : ℂ) (xiSpectralPoint q) := by
  unfold xiReciprocalSquareCauchyQuartetVariance
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
          (Complex.normSq_nonneg _))
        (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _))

theorem summable_xiReciprocalSquareCauchyQuartetVariance
    (z : XiContinuedCauchyPoint)
    (hzre : (z : ℂ).re ≠ 0) (hzim : (z : ℂ).im ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      xiReciprocalSquareCauchyQuartetVariance
        (z : ℂ) (xiSpectralPoint q)) := by
  let c : ℝ := 64 * (z : ℂ).re * (z : ℂ).im
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hzre) hzim
  have hscaled : Summable (fun q : XiZeroCopy =>
      c * xiReciprocalSquareCauchyQuartetVariance
        (z : ℂ) (xiSpectralPoint q)) := by
    refine (summable_xiReciprocalSquareCauchyQuartetTerm z).congr ?_
    intro q
    exact xiReciprocalSquareCauchyQuartetTerm_eq_variance z q
  refine (hscaled.mul_left c⁻¹).congr ?_
  intro q
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Total orientation defect as one signed scalar times a sum of nonnegative quartet variances. -/
theorem xiReciprocalSquareContinuedCauchyOrientationDefect_eq_variance_tsum
    (z : XiContinuedCauchyPoint) :
    xiReciprocalSquareContinuedCauchyOrientationDefect z =
      16 * (z : ℂ).re * (z : ℂ).im *
        ∑' q : XiZeroCopy,
          xiReciprocalSquareCauchyQuartetVariance
            (z : ℂ) (xiSpectralPoint q) := by
  have hquartet := tsum_xiReciprocalSquareCauchyQuartetTerm z
  rw [show (∑' q : XiZeroCopy,
      xiReciprocalSquareCauchyQuartetTerm z q) =
      ∑' q : XiZeroCopy,
        (64 * (z : ℂ).re * (z : ℂ).im) *
          xiReciprocalSquareCauchyQuartetVariance
            (z : ℂ) (xiSpectralPoint q) by
      apply tsum_congr
      exact xiReciprocalSquareCauchyQuartetTerm_eq_variance z,
    tsum_mul_left] at hquartet
  linarith

/-- A quartet variance has zero fibre exactly at a real centered spectral point. -/
theorem xiReciprocalSquareCauchyQuartetVariance_eq_zero_iff
    (z : XiContinuedCauchyPoint) (q : XiZeroCopy) :
    xiReciprocalSquareCauchyQuartetVariance
        (z : ℂ) (xiSpectralPoint q) = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  let a : ℂ := xiSpectralPoint q
  have ha : a ≠ 0 := xiSpectralPoint_ne_zero q
  have hare : a.re ≠ 0 := by
    simpa [a, xiSpectralPoint, mul_re] using
      xi_divisor_support_im_ne_zero q.1
  have haz : a - (z : ℂ) ≠ 0 :=
    xiSpectralPoint_sub_continuedCauchyPoint_ne z q
  have hcaz : (starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_lineConj] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyLineConjEquiv q)
  have hnegaz : -a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect] using
      xiSpectralPoint_sub_continuedCauchyPoint_ne z
        (xiZeroCopyReflectEquiv q)
  have hapz : a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegaz
    rw [show -a - (z : ℂ) = -(a + (z : ℂ)) by ring, h]
    simp
  have hnegcaz : -(starRingEnd ℂ) a - (z : ℂ) ≠ 0 := by
    simpa only [a, xiSpectralPoint_reflect, xiSpectralPoint_lineConj,
      map_neg] using
        xiSpectralPoint_sub_continuedCauchyPoint_ne z
          (xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q))
  have hcapz : (starRingEnd ℂ) a + (z : ℂ) ≠ 0 := by
    intro h
    apply hnegcaz
    rw [show -(starRingEnd ℂ) a - (z : ℂ) =
      -((starRingEnd ℂ) a + (z : ℂ)) by ring, h]
    simp
  have hden :
      Complex.normSq a ^ (2 : ℕ) *
          Complex.normSq (a - (z : ℂ)) *
          Complex.normSq ((starRingEnd ℂ) a - (z : ℂ)) *
          Complex.normSq (a + (z : ℂ)) *
          Complex.normSq ((starRingEnd ℂ) a + (z : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (pow_ne_zero 2 (ne_of_gt (Complex.normSq_pos.mpr ha)))
            (ne_of_gt (Complex.normSq_pos.mpr haz)))
          (ne_of_gt (Complex.normSq_pos.mpr hcaz)))
        (ne_of_gt (Complex.normSq_pos.mpr hapz)))
      (ne_of_gt (Complex.normSq_pos.mpr hcapz))
  have hsum : Complex.normSq a + Complex.normSq (z : ℂ) ≠ 0 := by
    have hapos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    have hznonneg : 0 ≤ Complex.normSq (z : ℂ) := Complex.normSq_nonneg _
    positivity
  constructor
  · intro hzero
    have hnum :
        a.re ^ (2 : ℕ) * a.im ^ (2 : ℕ) *
          (Complex.normSq a + Complex.normSq (z : ℂ)) = 0 := by
      unfold xiReciprocalSquareCauchyQuartetVariance at hzero
      rcases div_eq_zero_iff.mp hzero with hnum | hdenzero
      · exact hnum
      · exact False.elim (hden hdenzero)
    have hsq : a.im ^ (2 : ℕ) = 0 := by
      rcases mul_eq_zero.mp hnum with hprod | hnorm
      · exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hare)
      · exact False.elim (hsum hnorm)
    exact sq_eq_zero_iff.mp hsq
  · intro him
    simp [xiReciprocalSquareCauchyQuartetVariance, him]

/-- Direct rigidity statement behind the one-pole criterion: vanishing at one regular off-axis
pole forces every centered Xi spectral point to be real. -/
theorem xiSpectralPoint_im_eq_zero_of_continuedCauchyOrientationDefect_eq_zero
    (z : XiContinuedCauchyPoint)
    (hzre : (z : ℂ).re ≠ 0) (hzim : (z : ℂ).im ≠ 0)
    (hzero : xiReciprocalSquareContinuedCauchyOrientationDefect z = 0)
    (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have hsum := summable_xiReciprocalSquareCauchyQuartetVariance z hzre hzim
  have htotal :
      (∑' r : XiZeroCopy,
        xiReciprocalSquareCauchyQuartetVariance
          (z : ℂ) (xiSpectralPoint r)) = 0 := by
    have hid :=
      xiReciprocalSquareContinuedCauchyOrientationDefect_eq_variance_tsum z
    have hcoef : 16 * (z : ℂ).re * (z : ℂ).im ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hzre) hzim
    apply (mul_eq_zero.mp ?_).resolve_left hcoef
    calc
      (16 * (z : ℂ).re * (z : ℂ).im) *
            ∑' r : XiZeroCopy,
              xiReciprocalSquareCauchyQuartetVariance
                (z : ℂ) (xiSpectralPoint r) =
          xiReciprocalSquareContinuedCauchyOrientationDefect z := hid.symm
      _ = 0 := hzero
  have htermle :
      xiReciprocalSquareCauchyQuartetVariance
          (z : ℂ) (xiSpectralPoint q) ≤ 0 := by
    rw [← htotal]
    exact hsum.le_tsum q
      (fun r _ => xiReciprocalSquareCauchyQuartetVariance_nonneg z r)
  have hterm :
      xiReciprocalSquareCauchyQuartetVariance
          (z : ℂ) (xiSpectralPoint q) = 0 :=
    le_antisymm htermle
      (xiReciprocalSquareCauchyQuartetVariance_nonneg z q)
  exact (xiReciprocalSquareCauchyQuartetVariance_eq_zero_iff z q).mp hterm

theorem xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_quadraticReal
    (z : XiContinuedCauchyPoint) :
    xiReciprocalSquareContinuedCauchyOrientationDefect z = 0 ↔
      inner ℂ
          (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
          (xiWeilContinuedCauchyLp z) =
        inner ℂ
          (xiWeilContinuedCauchyLp z)
          (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)) := by
  rw [← inner_conj_symm
    (xiWeilContinuedCauchyLp z)
    (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))]
  unfold xiReciprocalSquareContinuedCauchyOrientationDefect
  constructor
  · intro him
    exact (Complex.conj_eq_iff_im.mpr him).symm
  · intro heq
    exact Complex.conj_eq_iff_im.mp heq.symm

/-- **Single-pole criterion.**  At any regular continued-Cauchy pole off both coordinate axes,
one scalar reciprocal-square orientation defect vanishes exactly under RH. -/
theorem xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_riemannHypothesis
    (z : XiContinuedCauchyPoint)
    (hzre : (z : ℂ).re ≠ 0) (hzim : (z : ℂ).im ≠ 0) :
    xiReciprocalSquareContinuedCauchyOrientationDefect z = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him :=
      xiSpectralPoint_im_eq_zero_of_continuedCauchyOrientationDefect_eq_zero
        z hzre hzim hzero q
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simpa using him
  · intro hRH
    exact
      (xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_quadraticReal z).mpr
        ((xiReciprocalSquareOperator_isSelfAdjoint_of_riemannHypothesis hRH).isSymmetric
          (xiWeilContinuedCauchyLp z) (xiWeilContinuedCauchyLp z))

/-- Concrete regular off-axis pole `1/4 + i/4`; regularity uses the existing unconditional
central Xi zero-free slab only to make the source vector well-defined. -/
def xiReciprocalSquareFixedCauchyPole : XiContinuedCauchyPoint := by
  let z : ℂ := (1 / 4 : ℂ) + (1 / 4 : ℂ) * I
  have hzre : z.re = 1 / 4 := by simp [z, mul_re]
  have hzim : z.im = 1 / 4 := by simp [z, mul_im]
  have hregular : XiC z ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_one
    rw [hzre]
    norm_num
  exact ⟨⟨z, hregular⟩,
    ccmContinuedCauchyDomain_of_regular_mem_centeredStrip
      (by rw [hzim]; norm_num) (by rw [hzim]; norm_num) hregular⟩

@[simp] theorem xiReciprocalSquareFixedCauchyPole_re :
    (xiReciprocalSquareFixedCauchyPole : ℂ).re = 1 / 4 := by
  simp [xiReciprocalSquareFixedCauchyPole, mul_re]

@[simp] theorem xiReciprocalSquareFixedCauchyPole_im :
    (xiReciprocalSquareFixedCauchyPole : ℂ).im = 1 / 4 := by
  simp [xiReciprocalSquareFixedCauchyPole, mul_im]

/-- Unconditional one-scalar source proposition at the concrete pole `1/4 + i/4`. -/
def XiReciprocalSquareFixedCauchyOrientationDefectZero : Prop :=
  xiReciprocalSquareContinuedCauchyOrientationDefect
    xiReciprocalSquareFixedCauchyPole = 0

/-- Exact one-scalar RH interface, with no remaining family quantifier or free pole parameter. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis :
    XiReciprocalSquareFixedCauchyOrientationDefectZero ↔ RiemannHypothesis := by
  unfold XiReciprocalSquareFixedCauchyOrientationDefectZero
  apply xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_riemannHypothesis
  · norm_num
  · norm_num

/-- At every regular pole, the orientation defect has the sign of the pole quadrant.  This is an
unconditional consequence of the quartet variance decomposition. -/
theorem xiReciprocalSquareContinuedCauchyOrientationDefect_quadrant_nonneg
    (z : XiContinuedCauchyPoint) :
    0 ≤ (z : ℂ).re * (z : ℂ).im *
      xiReciprocalSquareContinuedCauchyOrientationDefect z := by
  rw [xiReciprocalSquareContinuedCauchyOrientationDefect_eq_variance_tsum]
  have hsum : 0 ≤
      ∑' q : XiZeroCopy,
        xiReciprocalSquareCauchyQuartetVariance
          (z : ℂ) (xiSpectralPoint q) :=
    tsum_nonneg fun q => xiReciprocalSquareCauchyQuartetVariance_nonneg z q
  nlinarith [sq_nonneg ((z : ℂ).re * (z : ℂ).im)]

/-- The concrete first-quadrant defect is unconditionally nonnegative. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_nonneg :
    0 ≤ xiReciprocalSquareContinuedCauchyOrientationDefect
      xiReciprocalSquareFixedCauchyPole := by
  have hquadrant :=
    xiReciprocalSquareContinuedCauchyOrientationDefect_quadrant_nonneg
      xiReciprocalSquareFixedCauchyPole
  norm_num at hquadrant
  exact hquadrant

/-- **Predetermined failure witness.**  The same concrete scalar is strictly positive exactly
when RH fails; no existential choice of a pole or spectral point remains. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_pos_iff_not_riemannHypothesis :
    0 < xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole ↔
      ¬RiemannHypothesis := by
  constructor
  · intro hpos hRH
    have hzero : XiReciprocalSquareFixedCauchyOrientationDefectZero :=
      xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mpr hRH
    exact (ne_of_gt hpos) hzero
  · intro hnotRH
    have hne :
        xiReciprocalSquareContinuedCauchyOrientationDefect
            xiReciprocalSquareFixedCauchyPole ≠ 0 := by
      intro hzero
      exact hnotRH
        (xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mp
          hzero)
    exact lt_of_le_of_ne
      xiReciprocalSquareFixedCauchyOrientationDefect_nonneg hne.symm

/-- A one-sided source-passivity form of the fixed scalar criterion.  Because the opposite sign
is unconditional, nonpositivity forces exact saturation and hence RH. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefect_nonpos_iff_riemannHypothesis :
    xiReciprocalSquareContinuedCauchyOrientationDefect
        xiReciprocalSquareFixedCauchyPole ≤ 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hnonpos
    apply xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mp
    exact le_antisymm hnonpos
      xiReciprocalSquareFixedCauchyOrientationDefect_nonneg
  · intro hRH
    rw [(xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mpr
      hRH)]

end

end RHTower
