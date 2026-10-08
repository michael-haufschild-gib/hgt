import GaloisForLFunctions.RHTower.WeilPaperSpectralCoercivity
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Compact spectral completion with an explicit pole-compensated budget

The proved logarithmic moment bound yields a uniform spectral tail bound.
Prokhorov then gives a compact closure of each budgeted family of actual native
spectral probabilities. No integrability or tightness premise is added.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The exact compensated energy budget supplied by gamma coercivity. -/
def paperPoleCompensatedEnergy (c : NormalizedMixture) : ℝ :=
  energy c.1 - paperMixturePole c.1 + (10 + Real.log 4)

theorem paperPoleCompensatedEnergy_nonneg (c : NormalizedMixture) :
    0 ≤ paperPoleCompensatedEnergy c :=
  (paperSpectralLogMoment_nonneg c).trans (paperSpectralLogMoment_le_pole_compensated_energy c)

theorem paperSpectralLogWeight_eq (ξ : ℝ) :
    paperSpectralLogWeight ξ = Real.log (2 + (2 * Real.pi) * |ξ|) := by
  simp [paperSpectralLogWeight, abs_mul, abs_of_pos Real.pi_pos]

theorem paperSpectralLogWeight_pos (ξ : ℝ) : 0 < paperSpectralLogWeight ξ := by
  rw [paperSpectralLogWeight_eq]
  apply Real.log_pos
  have h := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) (abs_nonneg ξ)
  linarith

/-- The spectral cost tends to infinity with frequency. -/
theorem tendsto_paperSpectralLogWeight_atTop :
    Tendsto paperSpectralLogWeight atTop atTop := by
  have hlin : Tendsto (fun r : ℝ => 2 + (2 * Real.pi) * r) atTop atTop :=
    tendsto_atTop_add_const_left atTop 2
      (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
  apply (Real.tendsto_log_atTop.comp hlin).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simp only [Function.comp_def, paperSpectralLogWeight_eq, abs_of_nonneg hr]

/-- An actual native law has a quantitative logarithmic tail bound at every nonnegative radius. -/
theorem spectralProbability_tail_le_pole_compensated_energy
    (c : NormalizedMixture) (R : ℝ≥0) :
    (spectralProbability c : Measure ℝ) {ξ : ℝ | (R : ℝ) < ‖ξ‖} ≤
      ENNReal.ofReal (paperPoleCompensatedEnergy c / paperSpectralLogWeight R) := by
  have hW := paperSpectralLogWeight_pos (R : ℝ)
  have hm := ((integrable_paperSpectralLogWeight c).div_const
    (paperSpectralLogWeight R)).measure_le_integral
      (Filter.Eventually.of_forall fun ξ =>
        div_nonneg (paperSpectralLogWeight_nonneg ξ) hW.le)
      (s := {ξ : ℝ | (R : ℝ) < ‖ξ‖}) (by
        intro ξ hξ
        apply (le_div_iff₀ hW).mpr
        rw [one_mul, paperSpectralLogWeight_eq, paperSpectralLogWeight_eq,
          abs_of_nonneg R.coe_nonneg]
        apply Real.log_le_log (by positivity)
        have hξ' : (R : ℝ) ≤ |ξ| := le_of_lt hξ
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hξ' (by positivity : 0 ≤ 2 * Real.pi)))
  rw [integral_div] at hm
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (paperSpectralLogMoment_le_pole_compensated_energy c) hW.le

/-- The actual normalized native spectral laws satisfying a given compensated budget. -/
def paperPoleCompensatedSpectralLaws (B : ℝ) : Set (ProbabilityMeasure ℝ) :=
  spectralProbability '' {c : NormalizedMixture | paperPoleCompensatedEnergy c ≤ B}

/-- Every compensated budget gives uniform tightness of the actual native spectral laws. -/
theorem isTight_paperPoleCompensatedSpectralLaws (B : ℝ) :
    IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) |
      μ ∈ paperPoleCompensatedSpectralLaws B} := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  have hreal : Tendsto (fun r : ℝ => B / paperSpectralLogWeight r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_paperSpectralLogWeight_atTop
  have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal (B / paperSpectralLogWeight r))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  refine iSup_le fun μ => iSup_le fun hμ => ?_
  rcases hμ with ⟨ν, hν, rfl⟩
  rcases hν with ⟨c, hc, rfl⟩
  apply (spectralProbability_tail_le_pole_compensated_energy c ⟨r, hr⟩).trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hc (paperSpectralLogWeight_pos r).le

/-- A bounded compensated-energy family has compact closure in the real spectral topology. -/
theorem isCompact_closure_paperPoleCompensatedSpectralLaws (B : ℝ) :
    IsCompact (closure (paperPoleCompensatedSpectralLaws B)) :=
  isCompact_closure_of_isTightMeasureSet (isTight_paperPoleCompensatedSpectralLaws B)

/-- The actual compact completion of a compensated-energy spectral family. -/
abbrev PaperPoleCompensatedCompletion (B : ℝ) := closure (paperPoleCompensatedSpectralLaws B)

instance instCompactSpacePaperPoleCompensatedCompletion (B : ℝ) :
    CompactSpace (PaperPoleCompensatedCompletion B) :=
  isCompact_iff_compactSpace.mp (isCompact_closure_paperPoleCompensatedSpectralLaws B)

end RHTower.WeilWorkPBAP
