import GaloisForLFunctions.BiScaleUncertainty.PhysicalAffineAction
import GaloisForLFunctions.BiScaleUncertainty.SuccessorSequenceHilbert

/-!
# Antiperiodic rigidity through translated cell analysis

Actual square-summable cell coefficients rule out every nonzero antiperiodic
physical velocity. This classifies equality in the translation and affine
commutator energy bounds without a periodic-integrability premise.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem traceData_succ_neg_zero (w : TraceData) (h : ∀ k, w (k+1) = -w k) : w = 0 := by
  have he (n : ℕ) : (w n)^2 = (w 0)^2 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [h]
        nlinarith only [ih]
  have hs : Summable (fun k => (w k)^2) := by
    simpa only [Real.inner_apply, pow_two] using lp.summable_inner (𝕜 := ℝ) w w
  have ht : Tendsto (fun _ : ℕ => (w 0)^2) atTop (𝓝 0) := by
    simpa only [he] using hs.tendsto_atTop_zero
  have hz : (w 0)^2 = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  apply lp.ext
  funext k
  change w k = 0
  exact sq_eq_zero_iff.mp ((he k).trans hz)

theorem unitCellAnalysis_translation_one (q : Velocity) :
    unitCellAnalysis (physicalTranslation 1 q) = sequenceLeftShift ℝ (unitCellAnalysis q) := by
  apply lp.ext
  funext k
  rw [sequenceLeftShift_apply, unitCellAnalysis_apply, unitCellAnalysis_apply,
    primitive_physicalTranslation, primitive_physicalTranslation]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem unitCellAnalysis_antiperiodic_zero (q : Velocity) (h : physicalTranslation 1 q = -q) :
    unitCellAnalysis q = 0 := by
  have he : sequenceLeftShift ℝ (unitCellAnalysis q) = -unitCellAnalysis q := by
    rw [← unitCellAnalysis_translation_one, h, map_neg]
  apply traceData_succ_neg_zero
  intro k
  have hk := congrArg (fun w : TraceData => w k) he
  simpa only [sequenceLeftShift_apply, lp.coeFn_neg, Pi.neg_apply] using hk

theorem physicalTranslation_one_antiperiodic_zero (q : Velocity)
    (h : physicalTranslation 1 q = -q) : q = 0 := by
  have hz (b : ℝ) : unitCellAnalysis (physicalTranslation b q) = 0 := by
    apply unitCellAnalysis_antiperiodic_zero
    rw [physicalTranslation_comm, h, map_neg]
  have hc (b : ℝ) : primitive q (b+1)-primitive q b = 0 := by
    have he := congrArg (fun w : TraceData => w 0) (hz b)
    simpa [unitCellAnalysis_apply, primitive_physicalTranslation, add_comm] using he
  have h1 : primitive q 1 = 0 := by
    simpa only [zero_add, primitive_at_zero, sub_zero] using hc 0
  apply primitive_injective
  funext t
  have ht := congrArg (fun r : Velocity => primitive r t) h
  rw [primitive_physicalTranslation, primitive_neg_velocity] at ht
  rw [primitive_zero_velocity]
  linarith only [ht, hc t, h1]

theorem physicalTranslation_antiperiodic_iff (c : ℝ) (q : Velocity) :
    physicalTranslation c q = -q ↔ q = 0 := by
  constructor
  · intro h
    by_cases hc : c = 0
    · apply primitive_injective
      funext t
      have ht := congrArg (fun r : Velocity => primitive r t) h
      rw [hc, physicalTranslation_zero, primitive_neg_velocity] at ht
      rw [primitive_zero_velocity]
      linarith only [ht]
    · have hr : physicalTranslation 1 (physicalDilation c q) = -physicalDilation c q := by
        rw [physicalTranslation_dilation, mul_one, h, map_neg]
      have hz := physicalTranslation_one_antiperiodic_zero (physicalDilation c q) hr
      have he := physicalDilation_energy c q
      rw [hz, norm_zero, zero_pow (by decide)] at he
      have hq : ‖q‖^2 = 0 := (mul_eq_zero.mp he.symm).resolve_left (abs_ne_zero.mpr hc)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
  · intro h
    simp [h]

theorem physicalTranslation_maximal_energy_iff (c : ℝ) (q : Velocity) :
    ‖physicalTranslation c q-q‖^2 = 4*‖q‖^2 ↔ q = 0 := by
  constructor
  · intro h
    have hp := physicalTranslation_parallelogram c q
    have hz : ‖physicalTranslation c q+q‖^2 = 0 := by linarith only [hp, h]
    have hs : physicalTranslation c q+q = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact (physicalTranslation_antiperiodic_iff c q).mp (eq_neg_iff_add_eq_zero.mpr hs)
  · intro h
    simp [h]

theorem physicalAffineCommutator_maximal_energy_iff (a b : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b q‖^2 = 4*|a| * ‖q‖^2 ↔ a = 0 ∨ q = 0 := by
  constructor
  · intro h
    have hd := physicalAffineCommutator_defect a b q
    have hz : |a| * ‖physicalTranslation (b*(a-1)) q+q‖^2 = 0 := by linarith only [hd, h]
    rcases mul_eq_zero.mp hz with ha | hq
    · exact Or.inl (abs_eq_zero.mp ha)
    · have hs := norm_eq_zero.mp (sq_eq_zero_iff.mp hq)
      exact Or.inr ((physicalTranslation_antiperiodic_iff _ q).mp
        (eq_neg_iff_add_eq_zero.mpr hs))
  · rintro (rfl | rfl)
    · simp [physicalAffineCommutator_apply, physicalDilation_zero]
    · simp

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
