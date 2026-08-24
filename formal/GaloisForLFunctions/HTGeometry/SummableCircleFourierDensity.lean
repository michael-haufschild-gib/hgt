import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier
import GaloisForLFunctions.HTGeometry.CircleFourierDensityUniqueness
import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Symmetric densities from summable circle Fourier tails

For a real sequence `a`, this module packages the literal density
`a 0 + 2 * Σ_{n ≥ 0} a (n + 1) Re(z^n)` on the unit circle.  Absolute
summability of the nonconstant coefficients makes the series measurable and
integrable.  Its tail norm gives pointwise two-sided bounds; a strict tail gap
therefore produces a finite strictly positive density measure.

This is the reusable analytic layer for source-defined circle states.  It
contains no reflected-Hankel positivity assertion.
-/

open MeasureTheory Complex Filter Topology Set
open scoped BigOperators ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real even Fourier density determined by a real sequence. -/
def symmetricCircleFourierDensity (a : ℕ → ℝ) (z : Circle) : ℝ :=
  a 0 + 2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re

/-- Absolute summability of the nonconstant coefficients controls the density series at every
circle point. -/
theorem summable_symmetricCircleFourierDensity_terms {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    Summable (fun n : ℕ => a (n + 1) * ((z : ℂ) ^ (n + 1)).re) := by
  refine Summable.of_norm_bounded ha fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |a (n + 1)| * |((z : ℂ) ^ (n + 1)).re|
      ≤ |a (n + 1)| * ‖(z : ℂ) ^ (n + 1)‖ := by
        gcongr
        exact abs_re_le_norm _
    _ = |a (n + 1)| := by
      rw [norm_pow, Circle.norm_coe, one_pow, mul_one]

/-- The nonconstant part of a symmetric circle density is bounded by twice its absolute Fourier
tail. -/
theorem abs_symmetricCircleFourierDensity_sub_head_le {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    |symmetricCircleFourierDensity a z - a 0| ≤
      2 * ∑' n : ℕ, |a (n + 1)| := by
  have hs := summable_symmetricCircleFourierDensity_terms ha z
  have hterm : ∀ n : ℕ,
      ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ≤ |a (n + 1)| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    calc |a (n + 1)| * |((z : ℂ) ^ (n + 1)).re|
        ≤ |a (n + 1)| * ‖(z : ℂ) ^ (n + 1)‖ := by
          gcongr
          exact abs_re_le_norm _
      _ = |a (n + 1)| := by
        rw [norm_pow, Circle.norm_coe, one_pow, mul_one]
  have htsum : ∑' n : ℕ, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ≤
      ∑' n : ℕ, |a (n + 1)| :=
    hs.norm.tsum_le_tsum hterm ha
  rw [symmetricCircleFourierDensity]
  have hrewrite : a 0 + 2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re - a 0 =
      2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re := by
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * ‖∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖
      ≤ 2 * ∑' n : ℕ, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm hs.norm
    _ ≤ 2 * ∑' n : ℕ, |a (n + 1)| := by
      gcongr

/-- Pointwise lower bound from the absolute Fourier tail. -/
theorem symmetricCircleFourierDensity_lower {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    a 0 - 2 * ∑' n : ℕ, |a (n + 1)| ≤ symmetricCircleFourierDensity a z := by
  have h := (abs_le.mp (abs_symmetricCircleFourierDensity_sub_head_le ha z)).1
  linarith

/-- Pointwise upper bound from the absolute Fourier tail. -/
theorem symmetricCircleFourierDensity_upper {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    symmetricCircleFourierDensity a z ≤ a 0 + 2 * ∑' n : ℕ, |a (n + 1)| := by
  have h := (abs_le.mp (abs_symmetricCircleFourierDensity_sub_head_le ha z)).2
  linarith

/-- A strict absolute-tail gap makes the symmetric circle density strictly positive everywhere. -/
theorem symmetricCircleFourierDensity_pos {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hstrict : 2 * ∑' n : ℕ, |a (n + 1)| < a 0) (z : Circle) :
    0 < symmetricCircleFourierDensity a z := by
  have hlower := symmetricCircleFourierDensity_lower ha z
  linarith

/-- The symmetric density is measurable. -/
theorem measurable_symmetricCircleFourierDensity (a : ℕ → ℝ) :
    Measurable (symmetricCircleFourierDensity a) := by
  unfold symmetricCircleFourierDensity
  apply Measurable.add measurable_const
  apply Measurable.mul measurable_const
  apply Measurable.tsum
  intro n
  apply Measurable.mul measurable_const
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  exact (Complex.reCLM.continuous.comp (hcoe.pow (n + 1))).measurable

/-- Uniform integrability bound for the symmetric density. -/
theorem norm_symmetricCircleFourierDensity_le {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    ‖symmetricCircleFourierDensity a z‖ ≤
      |a 0| + 2 * ∑' n : ℕ, |a (n + 1)| := by
  have hbound := abs_symmetricCircleFourierDensity_sub_head_le ha z
  have hfirst : ‖symmetricCircleFourierDensity a z - a 0‖ ≤
      2 * ∑' n : ℕ, |a (n + 1)| := by
    simpa only [Real.norm_eq_abs] using hbound
  have hsecond : ‖a 0‖ = |a 0| := Real.norm_eq_abs _
  calc ‖symmetricCircleFourierDensity a z‖ =
      ‖(symmetricCircleFourierDensity a z - a 0) + a 0‖ := by
        ring_nf
    _ ≤ ‖symmetricCircleFourierDensity a z - a 0‖ + ‖a 0‖ := norm_add_le _ _
    _ ≤ 2 * ∑' n : ℕ, |a (n + 1)| + |a 0| := by
      rw [hsecond]
      exact add_le_add hfirst (le_refl _)
    _ = _ := by ring

/-- The symmetric density is integrable against normalized circle Haar measure. -/
theorem integrable_symmetricCircleFourierDensity {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    Integrable (symmetricCircleFourierDensity a) circleLebesgue := by
  apply Integrable.of_bound
    (measurable_symmetricCircleFourierDensity a).aestronglyMeasurable
    (|a 0| + 2 * ∑' n : ℕ, |a (n + 1)|)
  filter_upwards with z
  exact norm_symmetricCircleFourierDensity_le ha z

/-- The normalized Haar integral of every integer circle monomial. -/
theorem integral_circleLebesgue_coe_zpow (k : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ k ∂circleLebesgue = if k = 0 then 1 else 0 := by
  have hmeas : AEStronglyMeasurable (fun z : Circle => (z : ℂ) ^ k) circleLebesgue :=
    (circleZMonomial_memLp circleLebesgue k).aestronglyMeasurable
  rw [circleLebesgue] at hmeas ⊢
  rw [integral_map
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable hmeas]
  · have hEq : (fun x : AddCircle (1 : ℝ) =>
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x : Circle) : ℂ) ^ k)
        = fun x => fourier k x := by
      funext x
      rw [AddCircle.homeomorphCircle_apply, fourier_apply, AddCircle.toCircle_zsmul]
      exact (Circle.coe_zpow x.toCircle k).symm
    rw [hEq, GaloisForLFunctions.integral_fourier_unitCircleHaar]
  
/-- Every nonconstant multiplicative circle monomial has zero normalized Haar average. -/
theorem integral_circleLebesgue_coe_pow_eq_zero (n : ℕ) (hn : n ≠ 0) :
    ∫ z : Circle, (z : ℂ) ^ n ∂circleLebesgue = 0 := by
  simpa [zpow_natCast, hn] using
    integral_circleLebesgue_coe_zpow (n : ℤ)

/-- Every positive real Fourier mode has zero normalized Haar average. -/
theorem integral_circleLebesgue_re_coe_pow_succ_eq_zero (n : ℕ) :
    ∫ z : Circle, ((z : ℂ) ^ (n + 1)).re ∂circleLebesgue = 0 := by
  have hInt : Integrable (fun z : Circle => (z : ℂ) ^ (n + 1)) circleLebesgue := by
    simpa only [zpow_natCast] using
      (circleZMonomial_memLp circleLebesgue ((n + 1 : ℕ) : ℤ)).integrable (by norm_num)
  change ∫ z : Circle, RCLike.re ((z : ℂ) ^ (n + 1)) ∂circleLebesgue = 0
  rw [integral_re hInt,
    integral_circleLebesgue_coe_pow_eq_zero (n + 1) (Nat.succ_ne_zero n)]
  rfl

/-- Orthogonality of a positive real Fourier mode against a nonnegative circle monomial. -/
theorem integral_re_circle_pow_mul_circle_pow (n k : ℕ) (hn : n ≠ 0) :
    (∫ z : Circle, (((z : ℂ) ^ n).re : ℂ) * (z : ℂ) ^ k ∂circleLebesgue) =
      if n = k then (2 : ℂ)⁻¹ else 0 := by
  have hPow : Integrable (fun z : Circle => (z : ℂ) ^ n) circleLebesgue := by
    simpa only [zpow_natCast] using
      (circleZMonomial_memLp circleLebesgue (n : ℤ)).integrable (by norm_num)
  have hplus : ∫ z : Circle, (z : ℂ) ^ n * (z : ℂ) ^ (k : ℤ) ∂circleLebesgue = 0 := by
    rw [show (fun z : Circle => (z : ℂ) ^ n * (z : ℂ) ^ (k : ℤ)) =
        fun z : Circle => (z : ℂ) ^ ((n : ℤ) + k) by
      funext z
      rw [← zpow_natCast]
      exact (zpow_add₀ (Circle.coe_ne_zero z) _ _).symm,
      integral_circleLebesgue_coe_zpow]
    have hsum : (n : ℤ) + k ≠ 0 := by omega
    rw [if_neg hsum]
  have hminus : ∫ z : Circle, (z : ℂ) ^ n * (z : ℂ) ^ (-(k : ℤ))
      ∂circleLebesgue = if n = k then 1 else 0 := by
    rw [show (fun z : Circle => (z : ℂ) ^ n * (z : ℂ) ^ (-(k : ℤ))) =
        fun z : Circle => (z : ℂ) ^ ((n : ℤ) - k) by
      funext z
      rw [← zpow_natCast]
      convert (zpow_add₀ (Circle.coe_ne_zero z) (n : ℤ) (-(k : ℤ))).symm using 1 <;> ring,
      integral_circleLebesgue_coe_zpow]
    simp only [Int.sub_eq_zero, Int.ofNat_inj]
  calc
    (∫ z : Circle, (((z : ℂ) ^ n).re : ℂ) * (z : ℂ) ^ k ∂circleLebesgue) =
        (2 : ℂ)⁻¹ *
          ((∫ z : Circle, (z : ℂ) ^ n * (z : ℂ) ^ (k : ℤ) ∂circleLebesgue) +
            conj (∫ z : Circle, (z : ℂ) ^ n * (z : ℂ) ^ (-(k : ℤ)) ∂circleLebesgue)) := by
      simpa only [zpow_natCast] using
        integral_re_mul_circle_zpow circleLebesgue hPow (k : ℤ)
    _ = if n = k then (2 : ℂ)⁻¹ else 0 := by
      rw [hplus, hminus]
      by_cases hnk : n = k <;> simp [hnk]

/-- Each nonconstant summand of a symmetric Fourier density is integrable. -/
theorem integrable_symmetricCircleFourierDensity_term (a : ℕ → ℝ) (n : ℕ) :
    Integrable (fun z : Circle => a (n + 1) * ((z : ℂ) ^ (n + 1)).re) circleLebesgue := by
  have hPow : Integrable (fun z : Circle => (z : ℂ) ^ (n + 1)) circleLebesgue := by
    simpa only [zpow_natCast] using
      (circleZMonomial_memLp circleLebesgue ((n + 1 : ℕ) : ℤ)).integrable (by norm_num)
  have hRe : Integrable (fun z : Circle => ((z : ℂ) ^ (n + 1)).re) circleLebesgue := by
    simpa using Complex.reCLM.toContinuousLinearMap.integrable_comp hPow
  exact hRe.const_mul _

/-- Absolute coefficient summability controls the sum of the `L¹` norms of the Fourier tail. -/
theorem summable_integral_norm_symmetricCircleFourierDensity_terms {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    Summable (fun n : ℕ =>
      ∫ z : Circle, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ∂circleLebesgue) := by
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _) ?_ ha
  intro n
  have hpoint : ∀ z : Circle,
      ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ≤ |a (n + 1)| := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    calc |a (n + 1)| * |((z : ℂ) ^ (n + 1)).re|
        ≤ |a (n + 1)| * ‖(z : ℂ) ^ (n + 1)‖ := by
          gcongr
          exact abs_re_le_norm _
      _ = |a (n + 1)| := by
        rw [norm_pow, Circle.norm_coe, one_pow, mul_one]
  calc
    ∫ z : Circle, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ∂circleLebesgue
        ≤ ∫ _ : Circle, |a (n + 1)| ∂circleLebesgue :=
      integral_mono (integrable_symmetricCircleFourierDensity_term a n).norm
        (integrable_const (μ := circleLebesgue) |a (n + 1)|) hpoint
    _ = |a (n + 1)| := by simp

/-- The nonconstant Fourier tail is integrable under absolute coefficient summability. -/
theorem integrable_tsum_symmetricCircleFourierDensity_terms {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    Integrable (fun z : Circle =>
      ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re) circleLebesgue := by
  have hdens := integrable_symmetricCircleFourierDensity ha
  have hhead : Integrable (fun _ : Circle => a 0) circleLebesgue :=
    integrable_const (μ := circleLebesgue) _
  have hdiff := hdens.sub hhead
  change Integrable (fun z : Circle => symmetricCircleFourierDensity a z - a 0)
    circleLebesgue at hdiff
  have htwo : Integrable (fun z : Circle =>
      2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re) circleLebesgue := by
    simpa only [symmetricCircleFourierDensity, add_sub_cancel_left] using hdiff
  have hhalf := htwo.const_mul (1 / 2 : ℝ)
  convert hhalf using 1
  ext z
  ring

/-- The normalized Haar mass of a symmetric Fourier density is its constant coefficient. -/
theorem integral_symmetricCircleFourierDensity {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    ∫ z : Circle, symmetricCircleFourierDensity a z ∂circleLebesgue = a 0 := by
  let f : ℕ → Circle → ℝ := fun n z => a (n + 1) * ((z : ℂ) ^ (n + 1)).re
  have hterms : ∀ n, Integrable (f n) circleLebesgue := fun n =>
    integrable_symmetricCircleFourierDensity_term a n
  have hnorm : Summable (fun n => ∫ z : Circle, ‖f n z‖ ∂circleLebesgue) :=
    summable_integral_norm_symmetricCircleFourierDensity_terms ha
  have htail : Integrable (fun z : Circle => ∑' n : ℕ, f n z) circleLebesgue :=
    integrable_tsum_symmetricCircleFourierDensity_terms ha
  have hswap := (MeasureTheory.integral_tsum_of_summable_integral_norm hterms hnorm).symm
  change ∫ z : Circle, a 0 + 2 * ∑' n : ℕ, f n z ∂circleLebesgue = a 0
  rw [integral_add (integrable_const (μ := circleLebesgue) _) (htail.const_mul 2),
    integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul, hswap]
  have hzero : ∀ n : ℕ, ∫ z : Circle, f n z ∂circleLebesgue = 0 := by
    intro n
    simp only [f]
    rw [integral_const_mul, integral_circleLebesgue_re_coe_pow_succ_eq_zero]
    ring
  rw [show (∑' n : ℕ, ∫ z : Circle, f n z ∂circleLebesgue) = 0 by
    simp_rw [hzero]
    exact tsum_zero]
  ring

/-- Every nonnegative-index Fourier moment of the symmetric density is its defining coefficient. -/
theorem integral_symmetricCircleFourierDensity_mul_coe_pow
    {a : ℕ → ℝ} (ha : Summable fun n : ℕ => |a (n + 1)|) (k : ℕ) :
    (∫ z : Circle, (symmetricCircleFourierDensity a z : ℂ) * (z : ℂ) ^ k
        ∂circleLebesgue) = (a k : ℂ) := by
  let f : ℕ → Circle → ℂ := fun n z =>
    (a (n + 1) : ℂ) * (((z : ℂ) ^ (n + 1)).re : ℂ) * (z : ℂ) ^ k
  have hterms : ∀ n, Integrable (f n) circleLebesgue := by
    intro n
    have hre : Integrable
        (fun z : Circle => (((z : ℂ) ^ (n + 1)).re : ℂ)) circleLebesgue := by
      have hp : Integrable (fun z : Circle => (z : ℂ) ^ (n + 1)) circleLebesgue := by
        simpa only [zpow_natCast] using
          (circleZMonomial_memLp circleLebesgue ((n + 1 : ℕ) : ℤ)).integrable (by norm_num)
      exact Complex.reCLM.toContinuousLinearMap.integrable_comp hp |>.ofReal
    have hscalar := hre.const_mul (a (n + 1) : ℂ)
    exact hscalar.mul_bdd (c := 1)
      (circleZMonomial_memLp circleLebesgue (k : ℤ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simp only [norm_pow, Circle.norm_coe, one_pow, le_refl])
  have hnorm : Summable (fun n => ∫ z : Circle, ‖f n z‖ ∂circleLebesgue) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun z => norm_nonneg _) ?_ ha
    intro n
    calc
      ∫ z : Circle, ‖f n z‖ ∂circleLebesgue ≤
          ∫ _ : Circle, |a (n + 1)| ∂circleLebesgue := by
        apply integral_mono (hterms n).norm
          (integrable_const (μ := circleLebesgue) |a (n + 1)|)
        intro z
        simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
          Circle.norm_coe, one_pow, mul_one]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (Complex.abs_re_le_norm _ |>.trans (by simp))
      _ = |a (n + 1)| := by simp
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hterms hnorm
  have htail : (∫ z : Circle, (∑' n, f n z) ∂circleLebesgue) =
      ∑' n, ∫ z : Circle, f n z ∂circleLebesgue := hswap.symm
  have hheadInt : Integrable (fun z : Circle => (a 0 : ℂ) * (z : ℂ) ^ k)
      circleLebesgue := by
    exact ((circleZMonomial_memLp circleLebesgue (k : ℤ)).integrable (by norm_num)).const_mul _
  have htailInt : Integrable (fun z : Circle => ∑' n, f n z) circleLebesgue :=
    integrable_tsum_of_summable_integral_norm hterms hnorm
  have hpoint (z : Circle) :
      ((∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) * (z : ℂ) ^ k =
        ∑' n, f n z := by
    have hs := summable_symmetricCircleFourierDensity_terms ha z
    have hc := Complex.ofRealCLM.map_tsum hs
    change ((∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) *
        (z : ℂ) ^ k = ∑' n, f n z
    rw [show ((∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) =
        ∑' n : ℕ, ((a (n + 1) * ((z : ℂ) ^ (n + 1)).re : ℝ) : ℂ) by
      exact hc]
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    simp [f]
  rw [show (fun z : Circle => (symmetricCircleFourierDensity a z : ℂ) * (z : ℂ) ^ k) =
      fun z : Circle => (a 0 : ℂ) * (z : ℂ) ^ k + 2 * ∑' n, f n z by
    funext z
    simp only [symmetricCircleFourierDensity, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    rw [add_mul, mul_assoc, hpoint]]
  have hscaled : (∫ z : Circle, 2 * ∑' n, f n z ∂circleLebesgue) =
      2 * ∑' n, ∫ z : Circle, f n z ∂circleLebesgue := by
    rw [integral_const_mul, htail]
  rw [integral_add hheadInt (htailInt.const_mul 2), hscaled]
  have hfint (n : ℕ) :
      (∫ z : Circle, f n z ∂circleLebesgue) =
        if n + 1 = k then (a (n + 1) : ℂ) / 2 else 0 := by
    rw [show f n = fun z : Circle =>
        (a (n + 1) : ℂ) * ((((z : ℂ) ^ (n + 1)).re : ℂ) * (z : ℂ) ^ k) by
      funext z
      simp [f]
      ring]
    rw [integral_const_mul,
      integral_re_circle_pow_mul_circle_pow (n + 1) k (Nat.succ_ne_zero n)]
    by_cases hnk : n + 1 = k <;> simp [hnk, div_eq_mul_inv]
  cases k with
  | zero =>
      have hsum : (∑' n : ℕ, ∫ z : Circle, f n z ∂circleLebesgue) = 0 := by
        simp_rw [hfint]
        simp
      rw [hsum]
      simp
  | succ l =>
      have hsum : (∑' n : ℕ, ∫ z : Circle, f n z ∂circleLebesgue) =
          (a (l + 1) : ℂ) / 2 := by
        rw [tsum_eq_single l]
        · rw [hfint]
          simp
        · intro n hn
          rw [hfint]
          simp only [ite_eq_right_iff]
          intro heq
          exact (hn (by omega)).elim
      rw [integral_const_mul,
        integral_circleLebesgue_coe_pow_eq_zero (l + 1) (Nat.succ_ne_zero l), hsum]
      ring

/-- The finite circle measure having the symmetric Fourier density with respect to Haar. -/
def symmetricCircleFourierDensityMeasure (a : ℕ → ℝ) : Measure Circle :=
  circleLebesgue.withDensity fun z => ENNReal.ofReal (symmetricCircleFourierDensity a z)

/-- If the symmetric density is nonnegative, its positive measure recovers every defining
nonnegative-index Fourier coefficient. -/
theorem integral_coe_pow_symmetricCircleFourierDensityMeasure
    {a : ℕ → ℝ} (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hpos : ∀ z : Circle, 0 ≤ symmetricCircleFourierDensity a z) (k : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ k ∂symmetricCircleFourierDensityMeasure a) = (a k : ℂ) := by
  have hfourier := realDensity_fourier_eq_pos_sub_neg circleLebesgue
    (integrable_symmetricCircleFourierDensity ha) (k : ℤ)
  have hposMeasure : realPosDensityMeasure circleLebesgue
      (symmetricCircleFourierDensity a) = symmetricCircleFourierDensityMeasure a := rfl
  have hnegMeasure : realNegDensityMeasure circleLebesgue
      (symmetricCircleFourierDensity a) = 0 := by
    rw [realNegDensityMeasure]
    have hzero : (fun z : Circle => ENNReal.ofReal (-symmetricCircleFourierDensity a z)) = 0 := by
      funext z
      simp [hpos z]
    rw [hzero, withDensity_zero]
  rw [hposMeasure, hnegMeasure, integral_zero_measure, sub_zero] at hfourier
  simpa only [zpow_natCast] using hfourier.trans
    (integral_symmetricCircleFourierDensity_mul_coe_pow ha k)

/-- Dividing a positive symmetric density by its positive head produces the normalized moment
sequence `a k / a 0`. -/
theorem integral_coe_pow_normalized_symmetricCircleFourierDensityMeasure
    {a : ℕ → ℝ} (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hhead : 0 < a 0)
    (hpos : ∀ z : Circle, 0 ≤ symmetricCircleFourierDensity a z) (k : ℕ) :
    (∫ z : Circle, (z : ℂ) ^ k ∂circleLebesgue.withDensity
      (fun z => ENNReal.ofReal (symmetricCircleFourierDensity a z / a 0))) =
        (a k : ℂ) / (a 0 : ℂ) := by
  let d : Circle → ℝ := fun z => symmetricCircleFourierDensity a z / a 0
  have hdInt : Integrable d circleLebesgue := by
    exact (integrable_symmetricCircleFourierDensity ha).div_const (a 0)
  have hdpos : ∀ z, 0 ≤ d z := fun z => div_nonneg (hpos z) hhead.le
  have hfourier := realDensity_fourier_eq_pos_sub_neg circleLebesgue hdInt (k : ℤ)
  have hposMeasure : realPosDensityMeasure circleLebesgue d =
      circleLebesgue.withDensity
        (fun z => ENNReal.ofReal (symmetricCircleFourierDensity a z / a 0)) := rfl
  have hnegMeasure : realNegDensityMeasure circleLebesgue d = 0 := by
    rw [realNegDensityMeasure]
    have hzero : (fun z : Circle => ENNReal.ofReal (-d z)) = 0 := by
      funext z
      simp [hdpos z]
    rw [hzero, withDensity_zero]
  rw [hposMeasure, hnegMeasure, integral_zero_measure, sub_zero] at hfourier
  have hright : (∫ z : Circle, (d z : ℂ) * (z : ℂ) ^ (k : ℤ) ∂circleLebesgue) =
      (a k : ℂ) / (a 0 : ℂ) := by
    rw [show (fun z : Circle => (d z : ℂ) * (z : ℂ) ^ (k : ℤ)) =
        fun z => (a 0 : ℂ)⁻¹ *
          ((symmetricCircleFourierDensity a z : ℂ) * (z : ℂ) ^ k) by
      funext z
      simp only [d, zpow_natCast]
      push_cast
      field_simp [hhead.ne']]
    rw [integral_const_mul, integral_symmetricCircleFourierDensity_mul_coe_pow ha k]
    simp only [div_eq_mul_inv]
    ring
  simpa only [zpow_natCast] using hfourier.trans hright

/-- Absolute summability ensures that the symmetric density measure is finite. -/
theorem symmetricCircleFourierDensityMeasure_finite {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    IsFiniteMeasure (symmetricCircleFourierDensityMeasure a) := by
  unfold symmetricCircleFourierDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_symmetricCircleFourierDensity ha).hasFiniteIntegral

/-- A nonnegative symmetric density of constant coefficient one defines a circle probability
measure. -/
theorem isProbabilityMeasure_symmetricCircleFourierDensityMeasure {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hpos : ∀ z : Circle, 0 ≤ symmetricCircleFourierDensity a z)
    (hhead : a 0 = 1) :
    IsProbabilityMeasure (symmetricCircleFourierDensityMeasure a) := by
  rw [isProbabilityMeasure_iff, symmetricCircleFourierDensityMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hmass := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_symmetricCircleFourierDensity ha) (Eventually.of_forall hpos)
  rw [integral_symmetricCircleFourierDensity ha, hhead] at hmass
  simpa using hmass.symm

/-- A strict Fourier-tail gap and unit constant coefficient give an explicit circle probability
carrier. -/
theorem isProbabilityMeasure_symmetricCircleFourierDensityMeasure_of_tail_gap {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hgap : 2 * ∑' n : ℕ, |a (n + 1)| < a 0)
    (hhead : a 0 = 1) :
    IsProbabilityMeasure (symmetricCircleFourierDensityMeasure a) := by
  apply isProbabilityMeasure_symmetricCircleFourierDensityMeasure ha _ hhead
  intro z
  exact (symmetricCircleFourierDensity_pos ha hgap z).le

end

end GaloisForLFunctions.HTGeometry
