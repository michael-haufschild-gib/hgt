import GaloisForLFunctions.RHTower.SuzukiGramDominationRepair
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Suzuki's oriented-primitive repair on the actual `L²(-a,a)` source class

Suzuki (2022), Theorem 4.2, applies to arbitrary `L²(-a,a)` sources.  Finite point sources are
not dense in that space, so the finite Gram factorization alone does not repair the printed
entrywise-kernel comparison.  This file constructs the exact Bochner integral

`P φ x = ∫ t in [-a,a], φ(t) e_t(x) dt`

for a genuine `L²` representative and proves its support and integrability directly on the product
measure.  Subsequent theorems identify Suzuki's divided-exponential transform with the angular
Fourier transform of `P φ` and derive the two form-level estimates needed in Theorem 4.2.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Joint measurability of Suzuki's directed-interval feature. -/
theorem measurable_suzukiOrientedSegment_uncurry :
    Measurable (Function.uncurry suzukiOrientedSegment) := by
  have hrepr : Function.uncurry suzukiOrientedSegment = fun p : ℝ × ℝ =>
      if 0 ≤ p.1 then
        if 0 < p.2 ∧ p.2 ≤ p.1 then (1 : ℂ) else 0
      else if p.1 < p.2 ∧ p.2 ≤ 0 then (-1 : ℂ) else 0 := by
    funext p
    rcases p with ⟨t, x⟩
    simp only [Function.uncurry_apply_pair]
    by_cases ht : 0 ≤ t
    · simp [suzukiOrientedSegment, ht, Set.indicator, Set.mem_Ioc]
    · simp [suzukiOrientedSegment, ht, Set.indicator, Set.mem_Ioc]
      split_ifs <;> simp_all
  rw [hrepr]
  apply Measurable.ite
  · exact measurableSet_le measurable_const measurable_fst
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    · exact measurable_const
    · exact measurable_const
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    · exact measurable_const
    · exact measurable_const

/-- Actual oriented primitive attached to a source on `[-a,a]`. -/
def suzukiOrientedPrimitive (a : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Icc (-a) a, φ t * suzukiOrientedSegment t x

theorem norm_suzukiOrientedSegment_le_indicator_Icc {a t x : ℝ}
    (ha : 0 ≤ a) (ht : t ∈ Icc (-a) a) :
    ‖suzukiOrientedSegment t x‖ ≤
      (Icc (-a) a).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx]
    by_cases ht0 : 0 ≤ t
    · simp [suzukiOrientedSegment, ht0, Set.indicator]
      split_ifs <;> norm_num
    · simp [suzukiOrientedSegment, ht0, Set.indicator]
      split_ifs <;> norm_num
  · rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha ht hx, norm_zero]
    simp [Set.indicator, hx]

/-- Product-measure integrability behind all Fubini interchanges for the actual source map. -/
theorem integrable_suzukiOrientedPrimitive_joint {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : Integrable φ (volume.restrict (Icc (-a) a))) :
    Integrable (Function.uncurry (fun t x => φ t * suzukiOrientedSegment t x))
      ((volume.restrict (Icc (-a) a)).prod volume) := by
  let χ : ℝ → ℝ := (Icc (-a) a).indicator (fun _ => (1 : ℝ))
  have hχ : Integrable χ := by
    exact (MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)).integrable_indicator
        measurableSet_Icc
  have hmajor : Integrable (fun p : ℝ × ℝ => ‖φ p.1‖ * χ p.2)
      ((volume.restrict (Icc (-a) a)).prod volume) := hφ.norm.mul_prod hχ
  have hmeasφ : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1)
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun t x => φ t * suzukiOrientedSegment t x))
      ((volume.restrict (Icc (-a) a)).prod volume) :=
    hmeasφ.mul measurable_suzukiOrientedSegment_uncurry.aestronglyMeasurable
  apply hmajor.mono' hmeas
  have ht : ∀ᵐ t ∂volume.restrict (Icc (-a) a), t ∈ Icc (-a) a :=
    ae_restrict_mem measurableSet_Icc
  have htp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ).restrict (Icc (-a) a))
    (ν := (volume : Measure ℝ))).ae ht
  filter_upwards [htp] with p hp
  rcases p with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair, norm_mul, χ]
  exact mul_le_mul_of_nonneg_left
    (norm_suzukiOrientedSegment_le_indicator_Icc ha hp) (norm_nonneg (φ t))

/-- An `L²(-a,a)` source is integrable on its finite interval. -/
theorem integrableOn_Icc_of_memLp_two {a : ℝ} {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable φ (volume.restrict (Icc (-a) a)) := by
  let μ : Measure ℝ := volume.restrict (Icc (-a) a)
  have hμ : μ Set.univ < ⊤ := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk hμ
  exact hφ.integrable (by norm_num)

/-- The actual oriented primitive is `L¹` on the physical line. -/
theorem integrable_suzukiOrientedPrimitive {a : ℝ} (ha : 0 ≤ a)
    {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Icc (-a) a))) :
    Integrable (suzukiOrientedPrimitive a φ) := by
  have hjoint := integrable_suzukiOrientedPrimitive_joint ha
    (integrableOn_Icc_of_memLp_two hφ)
  exact hjoint.integral_prod_right

/-- The actual oriented primitive is supported in `[-a,a]`. -/
theorem suzukiOrientedPrimitive_eq_zero_of_not_mem_Icc {a x : ℝ} (ha : 0 ≤ a)
    (φ : ℝ → ℂ) (hx : x ∉ Icc (-a) a) :
    suzukiOrientedPrimitive a φ x = 0 := by
  unfold suzukiOrientedPrimitive
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha ht hx, mul_zero]
  rfl

end RHTower

end
