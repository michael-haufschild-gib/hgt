import GaloisForLFunctions.RHTower.SteinhausEulerLocalMeanSq
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# A measurable spatial envelope for finite Steinhaus Euler products

BAG C20.9. Cover the canonical critical-line discs by one rectangle. The local
planar bound gives simultaneous pointwise domination by an explicit nonnegative
integral. Joint measurability and Tonelli turn the exact Euler second moment and
strip comparison into a squared-partition expectation bound. No measurability of
an uncountable supremum is assumed.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- A fixed rectangle covers all canonical discs over a unit vertical segment. -/
def steinhausEulerSpatialRectangle (N : ℕ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Icc (1 / 2 - steinhausEulerSpatialRadius N) (1 / 2 + steinhausEulerSpatialRadius N) ×ˢ
      Icc (-steinhausEulerSpatialRadius N) (1 + steinhausEulerSpatialRadius N))

theorem measurableSet_steinhausEulerSpatialRectangle (N : ℕ) :
    MeasurableSet (steinhausEulerSpatialRectangle N) :=
  (measurableSet_Icc.prod measurableSet_Icc).preimage
    Complex.measurableEquivRealProd.measurable

theorem ball_subset_steinhausEulerSpatialRectangle (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    Metric.ball ((1 / 2 : ℂ) + (t : ℂ) * I) (steinhausEulerSpatialRadius N) ⊆
      steinhausEulerSpatialRectangle N := by
  intro z hz
  have hn : ‖z - ((1 / 2 : ℂ) + (t : ℂ) * I)‖ < steinhausEulerSpatialRadius N := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - ((1 / 2 : ℂ) + (t : ℂ) * I))).trans_lt hn
  have him := (Complex.abs_im_le_norm (z - ((1 / 2 : ℂ) + (t : ℂ) * I))).trans_lt hn
  norm_num at hre him
  rw [abs_lt] at hre him
  change (1 / 2 - steinhausEulerSpatialRadius N ≤ z.re ∧
      z.re ≤ 1 / 2 + steinhausEulerSpatialRadius N) ∧
    (-steinhausEulerSpatialRadius N ≤ z.im ∧ z.im ≤ 1 + steinhausEulerSpatialRadius N)
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩,
    ⟨by linarith [him.1, ht.1], by linarith [him.2, ht.2]⟩⟩

theorem volume_steinhausEulerSpatialRectangle {N : ℕ} (hN : 3 ≤ N) :
    volume (steinhausEulerSpatialRectangle N) =
      ENNReal.ofReal (2 * steinhausEulerSpatialRadius N * (1 + 2 * steinhausEulerSpatialRadius N)) := by
  unfold steinhausEulerSpatialRectangle
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  have hr := steinhausEulerSpatialRadius_pos hN
  rw [show (1 / 2 + steinhausEulerSpatialRadius N) - (1 / 2 - steinhausEulerSpatialRadius N) =
      2 * steinhausEulerSpatialRadius N by ring,
    show (1 + steinhausEulerSpatialRadius N) - -steinhausEulerSpatialRadius N =
      1 + 2 * steinhausEulerSpatialRadius N by ring,
    ← ENNReal.ofReal_mul (by positivity)]

theorem measurable_steinhausFiniteEulerProduct_joint (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Measurable (fun x : Omega × ℂ => steinhausFiniteEulerProduct P x.2 x.1) := by
  unfold steinhausFiniteEulerProduct steinhausEulerPrimeTerm
  apply Finset.measurable_prod
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  have hd : Differentiable ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (Or.inl hp0)
  exact (measurable_const.sub (((measurable_X p).comp measurable_fst).mul
    (hd.continuous.measurable.comp measurable_snd))).inv

theorem lintegral_norm_sq_steinhausFiniteEulerProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (∫⁻ ω, ENNReal.ofReal (‖steinhausFiniteEulerProduct P s ω‖ ^ 2) ∂steinhausMeasure) =
      ENNReal.ofReal (steinhausEulerPartition P s.re) := by
  have heq := integral_norm_sq_steinhausFiniteEulerProduct P hP hs
  have hi : Integrable (fun ω => ‖steinhausFiniteEulerProduct P s ω‖ ^ 2) steinhausMeasure :=
    Integrable.of_integral_ne_zero (heq.trans_ne (steinhausEulerPartition_pos P hP hs).ne')
  rw [← heq, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]

/-- Explicit spatial domination, without an uncountable supremum. -/
def steinhausEulerSpatialEnvelope (N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹) *
    ∫⁻ z in steinhausEulerSpatialRectangle N,
      ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N) z ω‖ ^ 2)

private theorem measurable_spatial_integrand (N : ℕ) :
    Measurable (fun x : Omega × ℂ =>
      ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N) x.2 x.1‖ ^ 2)) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_steinhausFiniteEulerProduct_joint _
      (fun _ hp => (Nat.mem_primesBelow.mp hp).2)).norm.pow_const 2)

theorem measurable_steinhausEulerSpatialEnvelope (N : ℕ) :
    Measurable (steinhausEulerSpatialEnvelope N) :=
  ((measurable_spatial_integrand N).lintegral_prod_right').const_mul _

private theorem ofReal_integral_norm_sq_le (F : ℂ → ℂ) (μ : Measure ℂ) :
    ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂μ := by
  by_cases hi : Integrable (fun z => ‖F z‖ ^ 2) μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).le
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

theorem norm_sq_le_steinhausEulerSpatialEnvelope {N : ℕ} (hN : 3 ≤ N)
    (ω : Omega) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N)
      ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ 2) ≤ steinhausEulerSpatialEnvelope N ω := by
  have hr := steinhausEulerSpatialRadius_pos hN
  have ha : 0 < Real.pi * steinhausEulerSpatialRadius N ^ 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (norm_sq_steinhausFiniteEulerProduct_spatial_ball hN ω t) (inv_nonneg.mpr ha.le)
  have hcancel : (Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹ *
      (Real.pi * steinhausEulerSpatialRadius N ^ 2 *
        ‖steinhausFiniteEulerProduct (Nat.primesBelow N) ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ 2) =
      ‖steinhausFiniteEulerProduct (Nat.primesBelow N) ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ 2 := by
    field_simp [ne_of_gt hr]
  rw [hcancel] at hm
  apply (ENNReal.ofReal_le_ofReal hm).trans
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
  exact mul_le_mul_right ((ofReal_integral_norm_sq_le _ _).trans
    (lintegral_mono_set (ball_subset_steinhausEulerSpatialRectangle N ht))) _

private theorem spatial_envelope_scalar_bound {N : ℕ} (hN : 3 ≤ N) :
    (Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹ *
        (steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) *
        (2 * steinhausEulerSpatialRadius N * (1 + 2 * steinhausEulerSpatialRadius N)) ≤
      (128 * steinhausEulerSpatialMomentConstant / Real.pi) *
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2) ^ 2 := by
  have hr := steinhausEulerSpatialRadius_pos hN
  have hrle := steinhausEulerSpatialRadius_le hN
  have hC := steinhausEulerSpatialMomentConstant_pos
  have hM := steinhausEulerPartition_pos (Nat.primesBelow N)
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlog : 0 < 1 + Real.log (N : ℝ) := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have := Real.log_nonneg hn
    linarith
  have harea : 2 * steinhausEulerSpatialRadius N * (1 + 2 * steinhausEulerSpatialRadius N) ≤
      4 * steinhausEulerSpatialRadius N := by
    have := mul_le_mul_of_nonneg_left hrle hr.le
    nlinarith
  have hcost := one_add_log_le_two_mul_steinhausEulerPartition_half (show 1 ≤ N by omega)
  calc
    _ ≤ (Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹ *
        (steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) *
        (4 * steinhausEulerSpatialRadius N) :=
      mul_le_mul_of_nonneg_left harea (by positivity)
    _ = (64 * steinhausEulerSpatialMomentConstant / Real.pi) * (1 + Real.log N) *
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2) := by
      unfold steinhausEulerSpatialRadius
      field_simp
      ring
    _ ≤ (64 * steinhausEulerSpatialMomentConstant / Real.pi) *
        (2 * steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) *
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by positivity)) hM.le
    _ = _ := by ring

/-- The explicit envelope has the critical squared-partition expectation bound. -/
theorem lintegral_steinhausEulerSpatialEnvelope_le {N : ℕ} (hN : 3 ≤ N) :
    (∫⁻ ω, steinhausEulerSpatialEnvelope N ω ∂steinhausMeasure) ≤
      ENNReal.ofReal ((128 * steinhausEulerSpatialMomentConstant / Real.pi) *
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2) ^ 2) := by
  have hr := steinhausEulerSpatialRadius_pos hN
  have hC := steinhausEulerSpatialMomentConstant_pos
  have hM := steinhausEulerPartition_pos (Nat.primesBelow N)
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hm (z : ℂ) (hz : z ∈ steinhausEulerSpatialRectangle N) :
      (∫⁻ ω, ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N) z ω‖ ^ 2)
        ∂steinhausMeasure) ≤
      ENNReal.ofReal (steinhausEulerSpatialMomentConstant *
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) := by
    have hre : 1 / 2 - steinhausEulerSpatialRadius N ≤ z.re := hz.1.1
    have hz0 : 0 < z.re := by have := steinhausEulerSpatialRadius_le hN; linarith
    rw [lintegral_norm_sq_steinhausFiniteEulerProduct _
      (fun _ hp => (Nat.mem_primesBelow.mp hp).2) hz0]
    exact ENNReal.ofReal_le_ofReal (steinhausEulerPartition_le_spatial hN hre)
  unfold steinhausEulerSpatialEnvelope
  rw [lintegral_const_mul _ ((measurable_spatial_integrand N).lintegral_prod_right'),
    lintegral_lintegral_swap (measurable_spatial_integrand N).aemeasurable]
  calc
    _ ≤ ENNReal.ofReal ((Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹) *
        ∫⁻ _z in steinhausEulerSpatialRectangle N,
          ENNReal.ofReal (steinhausEulerSpatialMomentConstant *
            steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_steinhausEulerSpatialRectangle N)] with z hz
      exact hm z hz
    _ = ENNReal.ofReal ((Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹ *
        (steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) *
        (2 * steinhausEulerSpatialRadius N * (1 + 2 * steinhausEulerSpatialRadius N))) := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_steinhausEulerSpatialRectangle hN,
        ENNReal.ofReal_mul (p := (Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹ *
          (steinhausEulerSpatialMomentConstant * steinhausEulerPartition (Nat.primesBelow N) (1 / 2)))
          (by positivity),
        ENNReal.ofReal_mul (p := (Real.pi * steinhausEulerSpatialRadius N ^ 2)⁻¹) (by positivity)]
      simp only [mul_assoc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (spatial_envelope_scalar_bound hN)

end RHTower
