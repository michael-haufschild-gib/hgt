import GaloisForLFunctions.HTGeometry.FokasLenellsPhaseDistance
import GaloisForLFunctions.RHTower.FokasLenellsOperatorPhaseUnitary

/-!
# Cauchy compression and the raw scattering phase

Cauchy compression preserves the raw phase's maximal operator separation.
The exact phase used to conjugate the regularized jump has the same raw
time evolution, with the sign dictated by the existing stagger convention.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The paper's signed Cauchy operator composed with the actual raw time evolution. -/
def cauchyEvolution (t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (evolution t).toContinuousLinearEquiv.toContinuousLinearMap

/-- This is the existing Cauchy L-infinity representation of the actual phase class. -/
theorem cauchyEvolution_eq_cauchyLinftyMultiplier (t : ℝ) :
    cauchyEvolution t = cauchyLinftyMultiplier (phaseLinfty t) := by
  rw [cauchyEvolution, evolution_eq_lineLinftyMultiplier, cauchyLinftyMultiplier_apply]

/-- Cauchy compression leaves the raw phase's operator norm equal to one. -/
theorem norm_cauchyEvolution (t : ℝ) : ‖cauchyEvolution t‖ = 1 := by
  rw [cauchyEvolution_eq_cauchyLinftyMultiplier, norm_cauchyLinftyMultiplier, norm_phaseLinfty]

/-- Every two distinct compressed raw evolutions remain exactly two apart in operator norm. -/
theorem norm_cauchyEvolution_sub (s t : ℝ) :
    ‖cauchyEvolution s - cauchyEvolution t‖ = if s = t then 0 else 2 := by
  rw [cauchyEvolution_eq_cauchyLinftyMultiplier, cauchyEvolution_eq_cauchyLinftyMultiplier,
    ← map_sub, norm_cauchyLinftyMultiplier, norm_phaseLinfty_sub]

/-- Each compressed raw vector orbit is continuous. -/
theorem continuous_cauchyEvolution_apply (u : SoninL2) :
    Continuous (fun t => cauchyEvolution t u) :=
  negativeCauchy.continuous.comp (continuous_evolution_apply u)

/-- Cauchy compression does not repair operator-norm discontinuity of the raw phase. -/
theorem cauchyEvolution_not_operator_continuousAt (t : ℝ) :
    ¬ ContinuousAt cauchyEvolution t := by
  intro hc
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  have hn : t + δ/2 ≠ t := by linarith
  have hd : dist (t + δ/2) t < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith : 0 < δ/2)]
    linarith
  have hb := h hd
  rw [dist_eq_norm, norm_cauchyEvolution_sub, if_neg hn] at hb
  norm_num at hb

/-- The actual jump phase factors into a fixed spatial phase and the raw time phase with its checked sign. -/
theorem directPhaseSymbol_raw_time_factor (t x z : ℝ) :
    directPhaseSymbol t x z = directPhaseSymbol 0 x z * phase (-t) z := by
  by_cases hz : z = 0
  · subst z
    simp [directPhaseSymbol, FDNLS.staggerPhase, phase]
  · have hc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    unfold directPhaseSymbol FDNLS.staggerPhase phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring

/-- The unitary conjugating the actual jump carries precisely the raw time evolution. -/
theorem directPhaseUnitary_raw_time_factor (t x : ℝ) (u : SoninL2) :
    directPhaseUnitary t x u = directPhaseUnitary 0 x (evolution (-t) u) := by
  apply Lp.ext
  filter_upwards [directPhaseUnitary_ae t x u, directPhaseUnitary_ae 0 x (evolution (-t) u),
    evolution_ae (-t) u] with z h0 h1 h2
  rw [h0, h1, h2, directPhaseSymbol_raw_time_factor, mul_assoc]

/-- The actual phase conjugacy has continuous vector orbits at every spatial parameter. -/
theorem continuous_directPhaseUnitary_time_apply (x : ℝ) (u : SoninL2) :
    Continuous (fun t => directPhaseUnitary t x u) := by
  have h := (directPhaseUnitary 0 x).continuous.comp
    ((continuous_evolution_apply u).comp continuous_neg)
  exact h.congr fun t => (directPhaseUnitary_raw_time_factor t x u).symm

/-- The actual phase conjugacy is still maximally separated in operator norm at distinct times. -/
theorem norm_directPhaseUnitary_time_sub (x s t : ℝ) :
    ‖(directPhaseUnitary s x).toContinuousLinearEquiv.toContinuousLinearMap -
      (directPhaseUnitary t x).toContinuousLinearEquiv.toContinuousLinearMap‖ =
      if s = t then 0 else 2 := by
  have he : (directPhaseUnitary s x).toContinuousLinearEquiv.toContinuousLinearMap -
      (directPhaseUnitary t x).toContinuousLinearEquiv.toContinuousLinearMap =
      (directPhaseUnitary 0 x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((evolution (-s)).toContinuousLinearEquiv.toContinuousLinearMap -
        (evolution (-t)).toContinuousLinearEquiv.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro u
    change directPhaseUnitary s x u - directPhaseUnitary t x u =
      directPhaseUnitary 0 x (evolution (-s) u - evolution (-t) u)
    rw [map_sub, directPhaseUnitary_raw_time_factor s x u,
      directPhaseUnitary_raw_time_factor t x u]
  rw [he]
  have hn : ‖(directPhaseUnitary 0 x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((evolution (-s)).toContinuousLinearEquiv.toContinuousLinearMap -
        (evolution (-t)).toContinuousLinearEquiv.toContinuousLinearMap)‖ =
      ‖(evolution (-s)).toContinuousLinearEquiv.toContinuousLinearMap -
        (evolution (-t)).toContinuousLinearEquiv.toContinuousLinearMap‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      change ‖directPhaseUnitary 0 x _‖ ≤ _
      rw [(directPhaseUnitary 0 x).norm_map]
      exact ContinuousLinearMap.le_opNorm _ u
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      have hb := ((directPhaseUnitary 0 x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((evolution (-s)).toContinuousLinearEquiv.toContinuousLinearMap -
          (evolution (-t)).toContinuousLinearEquiv.toContinuousLinearMap)).le_opNorm u
      change ‖directPhaseUnitary 0 x _‖ ≤ _ at hb
      rwa [(directPhaseUnitary 0 x).norm_map] at hb
  rw [hn, norm_evolution_sub]
  simp only [neg_inj]

/-- The actual phase conjugacy is nowhere continuous in operator norm, even though the conjugated jump is Lipschitz. -/
theorem directPhaseUnitary_not_operator_time_continuousAt (x t : ℝ) :
    ¬ ContinuousAt (fun s => (directPhaseUnitary s x).toContinuousLinearEquiv.toContinuousLinearMap) t := by
  intro hc
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  have hn : t + δ/2 ≠ t := by linarith
  have hd : dist (t + δ/2) t < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith : 0 < δ/2)]
    linarith
  have hb := h hd
  rw [dist_eq_norm, norm_directPhaseUnitary_time_sub, if_neg hn] at hb
  norm_num at hb

end
end RHTower.FokasLenells
