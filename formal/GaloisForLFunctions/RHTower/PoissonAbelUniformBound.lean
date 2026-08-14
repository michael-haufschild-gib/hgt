import GaloisForLFunctions.RHTower.PoissonAbelBoundary
import GaloisForLFunctions.RHTower.PoissonMuntzAbelMeanDefect

/-!
# The Abel–Poisson average is bounded by the boundary datum, uniformly in the radius

The Abel-weighted bilateral Fourier average of a boundary datum is exactly its Poisson integral.
The Poisson kernel is nonnegative with total mass `2π` on the symmetric period, so the average
never exceeds the supremum of the datum — with a bound that does not depend on the Abel radius.

This is the domination an interchange of the Abel limit with an outer integration needs: the
Abel-regularized family is uniformly bounded, not merely convergent.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral Filter Topology
open scoped FourierTransform

namespace RHTower

/-- The Poisson integrand of a bounded interval-integrable datum is interval integrable. -/
theorem intervalIntegrable_poissonKer_mul {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume (-Real.pi) Real.pi) {r : ℝ} (hr : |r| < 1) :
    IntervalIntegrable (fun t : ℝ => GaloisForLFunctions.HTGeometry.poissonKer r t * φ t)
      volume (-Real.pi) Real.pi :=
  hφ.continuousOn_mul
    (GaloisForLFunctions.HTGeometry.poissonKer_continuous hr).continuousOn

/-- **The Abel–Poisson average is dominated by the datum, uniformly in the radius.** -/
theorem norm_poissonAbelFourierAverage_le {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume (-Real.pi) Real.pi)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {M : ℝ} (hM : ∀ t : ℝ, |φ t| ≤ M) :
    ‖poissonAbelFourierAverage φ r‖ ≤ M := by
  have hrabs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hker := GaloisForLFunctions.HTGeometry.poissonKer_nonneg hr0 hr1
  have hint := intervalIntegrable_poissonKer_mul hφ hrabs
  have hintM : IntervalIntegrable
      (fun t : ℝ => GaloisForLFunctions.HTGeometry.poissonKer r t * M)
      volume (-Real.pi) Real.pi :=
    ((GaloisForLFunctions.HTGeometry.poissonKer_continuous hrabs).intervalIntegrable
      (-Real.pi) Real.pi).mul_const M
  have habs : |∫ t in (-Real.pi)..Real.pi,
      GaloisForLFunctions.HTGeometry.poissonKer r t * φ t|
      ≤ ∫ t in (-Real.pi)..Real.pi,
        GaloisForLFunctions.HTGeometry.poissonKer r t * M := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hpi) ?_
    refine intervalIntegral.integral_mono_on hpi hint.abs hintM (fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (hker t)]
    exact mul_le_mul_of_nonneg_left (hM t) (hker t)
  have hval : (∫ t in (-Real.pi)..Real.pi,
      GaloisForLFunctions.HTGeometry.poissonKer r t * M) = 2 * Real.pi * M := by
    rw [intervalIntegral.integral_mul_const,
      GaloisForLFunctions.HTGeometry.poissonKer_integral_symm hr0 hr1]
  rw [poissonAbelFourierAverage_eq_poissonIntegral hφ hr0 hr1, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpi0))]
  rw [hval] at habs
  calc (2 * Real.pi)⁻¹ * |∫ t in (-Real.pi)..Real.pi,
        GaloisForLFunctions.HTGeometry.poissonKer r t * φ t|
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) :=
        mul_le_mul_of_nonneg_left habs (le_of_lt (inv_pos.mpr hpi0))
    _ = M := by field_simp

/-! ### The Abel-regularized radial source is uniformly bounded -/

/-- A bounded source supported in `[-L, L]` has a scaled periodization bounded by the number of
lattice points that can meet its support. -/
theorem abs_poissonMuntzScaledPeriodization_le {f : ℝ → ℝ} {L a Cf : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hvan : ∀ y : ℝ, L < |y| → f y = 0) (hb : ∀ y : ℝ, |f y| ≤ Cf) (x : ℝ) :
    |poissonMuntzScaledPeriodization f a x| ≤ (2 * a * L + 1) * Cf := by
  classical
  have hCf : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hb 0)
  have haL : (0 : ℝ) ≤ a * L := by positivity
  set S : Finset ℤ := Finset.Icc ⌈-x - a * L⌉ ⌊-x + a * L⌋ with hS
  have hzero : ∀ k : ℤ, k ∉ S → f ((x + (k : ℝ)) / a) = 0 := by
    intro k hk
    refine hvan _ ?_
    have habs : a * L < |x + (k : ℝ)| := by
      rw [hS, Finset.mem_Icc, not_and_or] at hk
      rcases hk with h | h
      · have hk' : (k : ℝ) < -x - a * L := Int.lt_ceil.mp (not_le.mp h)
        have hneg : x + (k : ℝ) < 0 := by linarith
        rw [abs_of_neg hneg]
        linarith
      · have hk' : -x + a * L < (k : ℝ) := Int.floor_lt.mp (not_le.mp h)
        have hpos : (0 : ℝ) < x + (k : ℝ) := by linarith
        rw [abs_of_pos hpos]
        linarith
    rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha]
    linarith [habs]
  have hcard : (S.card : ℝ) ≤ 2 * a * L + 1 := by
    rw [hS, Int.card_Icc]
    have hmax : (((⌊-x + a * L⌋ + 1 - ⌈-x - a * L⌉).toNat : ℕ) : ℝ)
        = max ((⌊-x + a * L⌋ + 1 - ⌈-x - a * L⌉ : ℤ) : ℝ) 0 := by
      rw [← Int.cast_natCast, Int.toNat_eq_max]
      push_cast
      rfl
    rw [hmax]
    refine max_le ?_ (by linarith)
    have h1 : ((⌊-x + a * L⌋ : ℤ) : ℝ) ≤ -x + a * L := Int.floor_le _
    have h2 : -x - a * L ≤ ((⌈-x - a * L⌉ : ℤ) : ℝ) := Int.le_ceil _
    push_cast
    linarith
  rw [poissonMuntzScaledPeriodization, GaloisForLFunctions.HTGeometry.realL1Periodization,
    tsum_eq_sum hzero]
  calc |∑ k ∈ S, f ((x + (k : ℝ)) / a)| ≤ ∑ k ∈ S, |f ((x + (k : ℝ)) / a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, Cf := Finset.sum_le_sum fun k _ => hb _
    _ = (S.card : ℝ) * Cf := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * a * L + 1) * Cf := mul_le_mul_of_nonneg_right hcard hCf

/-- The angular datum inherits the periodization bound. -/
theorem abs_poissonMuntzAngularDatum_le {f : ℝ → ℝ} {L a Cf : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hvan : ∀ y : ℝ, L < |y| → f y = 0) (hb : ∀ y : ℝ, |f y| ≤ Cf) (t : ℝ) :
    |poissonMuntzAngularDatum f a t| ≤ (2 * a * L + 1) * Cf :=
  abs_poissonMuntzScaledPeriodization_le ha hL hvan hb _

/-- **The square-root normalized Abel sum is bounded by the datum, uniformly in the radius.** -/
theorem norm_sqrt_mul_poissonMuntzAbelSum_le {f : ℝ → ℝ} (hf : Integrable f)
    (heven : Function.Even f) {a : ℝ} (ha : 0 < a) (hmean : ∫ x : ℝ, f x = 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {M : ℝ}
    (hM : ∀ t : ℝ, |poissonMuntzAngularDatum f a t| ≤ M) :
    ‖(Real.sqrt a : ℂ) * poissonMuntzAbelSum f a r‖ ≤ M / (2 * Real.sqrt a) := by
  have hzero : 𝓕 (fun x => (f x : ℂ)) 0 = 0 := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    have hcoe : (∫ x : ℝ, (f x : ℂ)) = (((∫ x : ℝ, f x) : ℝ) : ℂ) :=
      integral_ofReal (X := ℝ) (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    rw [hcoe, hmean]
    rfl
  have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hac : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hbase := poissonMuntzAbelSum_eq_meanDefect hf heven ha hr0 hr1
  rw [hzero, mul_zero, sub_zero] at hbase
  have habel := norm_poissonAbelFourierAverage_le
    (intervalIntegrable_poissonMuntzAngularDatum hf ha) hr0 hr1 hM
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  rw [hbase, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsa]
  have hden : ‖(2 : ℂ) * (a : ℂ)‖ = 2 * a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    norm_num
  rw [hden]
  have hkey : Real.sqrt a *
      (‖poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r‖ / (2 * a))
      = ‖poissonAbelFourierAverage (poissonMuntzAngularDatum f a) r‖ / (2 * Real.sqrt a) := by
    have h2a : (2 : ℝ) * a ≠ 0 := by positivity
    have h2s : (2 : ℝ) * Real.sqrt a ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt ha.le]
    ring
  rw [hkey]
  gcongr

/-- **The uniform domination.**  For a bounded compactly supported zero-mean even source the
square-root normalized Abel sum is bounded by a constant depending only on the aperture and the
support — never on the Abel radius. -/
theorem norm_sqrt_mul_poissonMuntzAbelSum_le_of_bounded {f : ℝ → ℝ} (hf : Integrable f)
    (heven : Function.Even f) {L a Cf : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hvan : ∀ y : ℝ, L < |y| → f y = 0) (hb : ∀ y : ℝ, |f y| ≤ Cf)
    (hmean : ∫ x : ℝ, f x = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖(Real.sqrt a : ℂ) * poissonMuntzAbelSum f a r‖
      ≤ (2 * a * L + 1) * Cf / (2 * Real.sqrt a) :=
  norm_sqrt_mul_poissonMuntzAbelSum_le hf heven ha hmean hr0 hr1
    (fun t => abs_poissonMuntzAngularDatum_le ha hL hvan hb t)

end RHTower
