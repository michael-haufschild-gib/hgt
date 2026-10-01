import GaloisForLFunctions.RHTower.CompactDiscMeanSqEnvelope
import GaloisForLFunctions.RHTower.SteinhausFiniteAffineTargetMass
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Complex Set Metric Finset
open scoped ENNReal
noncomputable section
namespace RHTower

/-- A fixed outer-disc energy threshold yields a measurable simultaneous inner-disc
fluctuation event with half the actual tilted mass and its exact original-law cost. -/
theorem exists_steinhausCompactAffineFluctuation_threshold
    (c : ℂ) {r ρ ε : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {n : ℕ} (m : Fin n → ℂ), (∀ i, ‖m i‖ ≤ 1 / 2) →
      ∀ a : Fin n → ℂ → ℂ, (∀ i, Differentiable ℂ (a i)) →
      (∀ z ∈ ball c ρ, (∑ i, ‖a i z‖ ^ 2) ≤ δ) →
      ∃ E : Set (Fin n → ℝ), MeasurableSet E ∧
        ENNReal.ofReal (1 / 2 : ℝ) ≤ steinhausFiniteAffineMeasure m E ∧
        (1 / 4 : ℝ) * Real.exp (-(2 * ∑ i, ‖m i‖ ^ 2)) ≤
          (steinhausFinitePhaseMeasure n).real E ∧
        ∀ x ∈ E, ∀ z ∈ closedBall c r,
          ‖steinhausFiniteCenteredSum m (fun i => a i z) x‖ < ε := by
  have hgap : 0 < ρ - r := sub_pos.mpr hrρ
  let δ : ℝ := ε ^ 2 * (ρ - r) ^ 2 / (2 * ρ ^ 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n m hm a ha henergy
  letI := isProbabilityMeasure_steinhausFiniteAffineMeasure hm
  let F : (Fin n → ℝ) → ℂ → ℂ := fun x z => steinhausFiniteCenteredSum m (fun i => a i z) x
  have hFd (x : Fin n → ℝ) : Differentiable ℂ (F x) := by
    change Differentiable ℂ (fun z => ∑ i, steinhausFiniteCenteredPhase m i x * a i z)
    apply Differentiable.fun_sum
    intro i _
    exact (ha i).const_mul _
  have hFm : Measurable (fun q : (Fin n → ℝ) × ℂ => F q.1 q.2) := by
    apply Continuous.measurable
    change Continuous (fun q : (Fin n → ℝ) × ℂ => ∑ i,
      steinhausFiniteCenteredPhase m i q.1 • a i q.2)
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_steinhausFiniteCenteredPhase m i).comp continuous_fst).smul
        ((ha i).continuous.comp continuous_snd))
  have hpoint (z : ℂ) (hz : z ∈ ball c ρ) :
      (∫⁻ x, ENNReal.ofReal (‖F x z‖ ^ 2) ∂steinhausFiniteAffineMeasure m) ≤ ENNReal.ofReal δ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_sq_steinhausFiniteCenteredSum hm (fun i => a i z))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      ((integral_norm_sq_steinhausFiniteCenteredSum_le hm _).trans (henergy z hz))
  let G := compactDiscMeanSqEnvelope F c r ρ
  have hGm : Measurable G := measurable_compactDiscMeanSqEnvelope F hFm c r ρ
  have hvol : volume (ball c ρ) = ENNReal.ofReal (ρ ^ 2 * Real.pi) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul (sq_nonneg ρ), ENNReal.ofReal_pow hρ.le,
      ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hmean : (∫⁻ x, G x ∂steinhausFiniteAffineMeasure m) ≤ ENNReal.ofReal (ε ^ 2 / 2) := by
    refine (lintegral_compactDiscMeanSqEnvelope_le (steinhausFiniteAffineMeasure m)
      F hFm c r ρ δ hpoint).trans_eq ?_
    rw [hvol, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.pi * (ρ - r) ^ 2)⁻¹),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.pi * (ρ - r) ^ 2)⁻¹ * δ)]
    congr 1
    dsimp only [δ]
    field_simp [Real.pi_ne_zero, hgap.ne', hρ.ne']
  let E := {x | G x < ENNReal.ofReal (ε ^ 2)}
  have hEm : MeasurableSet E := measurableSet_lt hGm measurable_const
  have heps2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hbad : steinhausFiniteAffineMeasure m {x | ENNReal.ofReal (ε ^ 2) ≤ G x} ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ (∫⁻ x, G x ∂steinhausFiniteAffineMeasure m) / ENNReal.ofReal (ε ^ 2) :=
        meas_ge_le_lintegral_div hGm.aemeasurable
          (ENNReal.ofReal_ne_zero_iff.mpr heps2) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε ^ 2 / 2) / ENNReal.ofReal (ε ^ 2) :=
        ENNReal.div_le_div_right hmean _
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos heps2]
        congr 1
        field_simp [hε.ne']
  have hcomp : Eᶜ = {x | ENNReal.ofReal (ε ^ 2) ≤ G x} := by
    ext x
    simp only [E, mem_compl_iff, mem_setOf_eq, not_lt]
  have hsum := measureReal_add_measureReal_compl (μ := steinhausFiniteAffineMeasure m) hEm
  rw [hcomp, probReal_univ] at hsum
  have hbadR : (steinhausFiniteAffineMeasure m).real
      {x | ENNReal.ofReal (ε ^ 2) ≤ G x} ≤ 1 / 2 := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤ steinhausFiniteAffineMeasure m E := by
    have hreal : (1 / 2 : ℝ) ≤ (steinhausFiniteAffineMeasure m).real E := by linarith
    have h := ENNReal.ofReal_le_ofReal hreal
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  refine ⟨E, hEm, hhalf, measureReal_event_ge_steinhausFiniteAffineCost hm hEm hhalf, ?_⟩
  intro x hx z hz
  have hdom := norm_sq_le_compactDiscMeanSqEnvelope F hFd c hrρ x hz
  have hsquare : ‖F x z‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff heps2).mp (hdom.trans_lt hx)
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsquare

end RHTower
