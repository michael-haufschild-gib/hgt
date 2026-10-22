import GaloisForLFunctions.RHTower.Deninger.DeningerL1Norm
import GaloisForLFunctions.RHTower.Deninger.DeningerTestL2Scale

/-!
# The counting measure on the space of places

The space of places is discrete, so its Borel structure is the discrete one and the counting
measure is finite on compact — that is, finite — sets and positive on nonempty open sets.  The
test space therefore embeds injectively into `L²` of the counting measure.

* `DeningerPlace` measure instances : discrete Borel structure, counting measure finite on
  compacts and positive on opens.
* `deningerPlaceToL2_injective` : **the test space of places embeds in `L²`.**
-/

namespace RHTower

open MeasureTheory NumberField

open scoped ENNReal

section PlaceMeasure

variable (K : Type*) [Field K] [NumberField K]

instance : MeasurableSpace (DeningerPlace K) := ⊤

instance : MeasurableSingletonClass (DeningerPlace K) := ⟨fun _ => trivial⟩

instance : BorelSpace (DeningerPlace K) := ⟨borel_eq_top_of_discrete.symm⟩

instance : IsFiniteMeasureOnCompacts (Measure.count : Measure (DeningerPlace K)) := by
  constructor
  intro s hs
  rw [Measure.count_apply_finite s hs.finite_of_discrete]
  exact ENNReal.natCast_lt_top _

instance : (Measure.count : Measure (DeningerPlace K)).IsOpenPosMeasure := by
  constructor
  intro U _ hne
  exact Measure.count_ne_zero hne

/-- **The test space of places embeds injectively into `L²` of the counting measure.** -/
theorem deningerPlaceToL2_injective :
    Function.Injective (deningerTestToL2 (Measure.count : Measure (DeningerPlace K))) :=
  deningerTestToL2_injective _

theorem deningerPlace_tsum_enorm (g : DeningerTestSpace (DeningerPlace K)) :
    ∑' v, ‖(g : DeningerPlace K → ℝ) v‖ₑ
      = ENNReal.ofReal (deningerL1Seminorm K g) := by
  classical
  have hfin : (Function.support ((g : DeningerPlace K → ℝ))).Finite := g.2.2.finite_of_discrete
  have habs := deningerPlaceAbs_finite_support K g
  have htsum : ∑' v, ‖(g : DeningerPlace K → ℝ) v‖ₑ
      = ∑ v ∈ hfin.toFinset, ‖(g : DeningerPlace K → ℝ) v‖ₑ := by
    refine tsum_eq_sum fun v hv => ?_
    have hzero : (g : DeningerPlace K → ℝ) v = 0 := by
      by_contra hne
      exact hv (hfin.mem_toFinset.mpr hne)
    rw [hzero]
    simp
  have hfinsum : deningerL1Seminorm K g = ∑ v ∈ hfin.toFinset, |(g : DeningerPlace K → ℝ) v| := by
    rw [deningerL1Seminorm_apply]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro v hv
    have hne : (g : DeningerPlace K → ℝ) v ≠ 0 := by
      intro hzero
      apply hv
      show |(g : DeningerPlace K → ℝ) v| = 0
      rw [hzero, abs_zero]
    rw [Set.Finite.coe_toFinset]
    exact hne
  rw [htsum, hfinsum, ENNReal.ofReal_sum_of_nonneg (fun v _ => abs_nonneg _)]
  exact Finset.sum_congr rfl fun v _ => Real.enorm_eq_ofReal_abs _

/-- **The `L²` norm is at most the `ℓ¹` norm** on the test space of places. -/
theorem deningerPlaceToL2_norm_le (g : DeningerTestSpace (DeningerPlace K)) :
    ‖deningerTestToL2 (Measure.count : Measure (DeningerPlace K)) g‖
      ≤ 1 * deningerL1Seminorm K g := by
  rw [one_mul, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal (apply_nonneg _ g) ?_
  have hcongr : eLpNorm ((deningerTestToL2 (Measure.count : Measure (DeningerPlace K)) g :
        Lp ℝ 2 Measure.count) : DeningerPlace K → ℝ) 2 Measure.count
      = eLpNorm ((g : DeningerPlace K → ℝ)) 2 Measure.count :=
    eLpNorm_congr_ae (deningerTestToL2_coeFn _ g)
  rw [hcongr, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), lintegral_count]
  set S : ℝ≥0∞ := ∑' v, ‖(g : DeningerPlace K → ℝ) v‖ₑ with hS
  have hpow : ∀ v, ‖(g : DeningerPlace K → ℝ) v‖ₑ ^ ((2 : ℝ≥0∞).toReal)
      ≤ ‖(g : DeningerPlace K → ℝ) v‖ₑ * S := by
    intro v
    have hle : ‖(g : DeningerPlace K → ℝ) v‖ₑ ≤ S := ENNReal.le_tsum v
    have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
    rw [h2, ENNReal.rpow_natCast, pow_two]
    exact mul_le_mul_right hle _
  have hbound : ∑' v, ‖(g : DeningerPlace K → ℝ) v‖ₑ ^ ((2 : ℝ≥0∞).toReal) ≤ S * S := by
    refine le_trans (ENNReal.tsum_le_tsum hpow) (le_of_eq ?_)
    exact ENNReal.tsum_mul_right
  have hhalf : (S * S) ^ (1 / (2 : ℝ≥0∞).toReal) = S := by
    have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h2, ← pow_two, ← ENNReal.rpow_natCast S 2, ← ENNReal.rpow_mul]
    norm_num
  calc (∑' v, ‖(g : DeningerPlace K → ℝ) v‖ₑ ^ ((2 : ℝ≥0∞).toReal))
        ^ (1 / (2 : ℝ≥0∞).toReal)
      ≤ (S * S) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        refine ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = S := hhalf
    _ = ENNReal.ofReal (deningerL1Seminorm K g) := deningerPlace_tsum_enorm K g

end PlaceMeasure

end RHTower
