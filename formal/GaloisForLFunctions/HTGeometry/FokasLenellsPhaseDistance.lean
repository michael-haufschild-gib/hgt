import GaloisForLFunctions.HTGeometry.LinftyMultiplicationNorm
import GaloisForLFunctions.HTGeometry.L2DominatedContinuity
import GaloisForLFunctions.HTGeometry.FokasLenellsSingularPhase
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Maximal operator distances of the raw singular phase

The actual time unitary from the paper is represented by its ordinary
L-infinity phase. A nonzero spectral point attains a phase difference of two
for every distinct pair of times; local continuity makes this visible to
L-infinity and hence to the full L2 operator norm and Cauchy compression.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The paper's raw singular time phase as an ordinary L-infinity class. -/
def phaseLinfty (t : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (measurable_phase t).aestronglyMeasurable 1
    (.of_forall fun z => (norm_phase t z).le)).toLp _

/-- The actual phase is retained almost everywhere. -/
theorem phaseLinfty_ae (t : ℝ) : (phaseLinfty t : ℝ → ℂ) =ᵐ[volume] phase t :=
  (memLp_top_of_bound (measurable_phase t).aestronglyMeasurable 1
    (.of_forall fun z => (norm_phase t z).le)).coeFn_toLp

/-- The actual raw evolution is exactly multiplication by its L-infinity phase class. -/
theorem evolution_eq_lineLinftyMultiplier (t : ℝ) :
    (evolution t).toContinuousLinearEquiv.toContinuousLinearMap = lineLinftyMultiplier (phaseLinfty t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [evolution_ae t u, lineLinftyMultiplier_ae (phaseLinfty t) u,
    phaseLinfty_ae t] with z h0 h1 h2
  change (evolution t u) z = (lineLinftyMultiplier (phaseLinfty t) u) z
  rw [h0, h1, h2]

private theorem local_symbol_norm_le_linfty
    (g : Lp ℂ ∞ (volume : Measure ℝ)) (φ : ℝ → ℂ) (z : ℝ)
    (hg : (g : ℝ → ℂ) =ᵐ[volume] φ) (hc : ContinuousAt φ z) : ‖φ z‖ ≤ ‖g‖ := by
  have hbound : ∀ᵐ y ∂volume, ‖φ y‖ ≤ ‖g‖ := by
    have h := ae_le_lpNorm_exponent_top (Lp.memLp g)
    rw [← toReal_eLpNorm (Lp.memLp g).1, ← Lp.norm_def] at h
    filter_upwards [h, hg] with y hb he
    rwa [he] at hb
  by_contra hn
  have hlt : ‖g‖ < ‖φ z‖ := lt_of_not_ge hn
  have hnhood : {y : ℝ | ‖g‖ < ‖φ y‖} ∈ 𝓝 z :=
    hc.norm.eventually (isOpen_Ioi.mem_nhds hlt)
  have hp := Measure.measure_pos_of_mem_nhds volume hnhood
  have hz : volume {y : ℝ | ‖g‖ < ‖φ y‖} = 0 := by
    have h := hbound.mono fun y hy => not_lt.mpr hy
    simpa only [ae_iff, not_not] using h
  exact hp.ne' hz

private theorem continuousAt_phase (t z : ℝ) (hz : z ≠ 0) :
    ContinuousAt (phase t) z := by
  unfold phase
  fun_prop (disch := positivity)

private theorem phase_half_turn (d : ℝ) (hd : d ≠ 0) :
    phase d (d / (2 * Real.pi)) = -1 := by
  have he : d / (2 * (d / (2 * Real.pi))) = Real.pi := by
    field_simp
  rw [phase, he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

private theorem phase_sub_half_turn (s t : ℝ) (h : s ≠ t) :
    ‖phase s ((s-t)/(2*Real.pi)) - phase t ((s-t)/(2*Real.pi))‖ = 2 := by
  let z := (s-t)/(2*Real.pi)
  have he : phase s z = -phase t z := by
    have hp := phase_add (s-t) t z
    rw [sub_add_cancel, show phase (s-t) z = -1 from phase_half_turn (s-t) (sub_ne_zero.mpr h)] at hp
    simpa using hp
  change ‖phase s z - phase t z‖ = 2
  rw [he, sub_eq_add_neg, ← neg_add, norm_neg, ← two_smul ℝ, norm_smul, norm_phase]
  norm_num

/-- The raw phase class has exactly unit essential-supremum norm. -/
theorem norm_phaseLinfty (t : ℝ) : ‖phaseLinfty t‖ = 1 := by
  apply le_antisymm
  · rw [Lp.norm_def, eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [phaseLinfty_ae t] with z hz
    rw [hz, norm_phase]
  · have hb := local_symbol_norm_le_linfty (phaseLinfty t) (phase t) 1 (phaseLinfty_ae t)
      (continuousAt_phase t 1 one_ne_zero)
    rwa [norm_phase] at hb

/-- Every actual raw evolution operator has norm one. -/
theorem norm_evolution_operator (t : ℝ) :
    ‖(evolution t).toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 := by
  rw [evolution_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier, norm_phaseLinfty]

/-- Distinct raw phase classes are exactly two apart in L-infinity; equal times have distance zero. -/
theorem norm_phaseLinfty_sub (s t : ℝ) :
    ‖phaseLinfty s - phaseLinfty t‖ = if s = t then 0 else 2 := by
  by_cases h : s = t
  · subst t
    simp
  rw [if_neg h]
  have hae : (phaseLinfty s - phaseLinfty t : Lp ℂ ∞ (volume : Measure ℝ)) =ᵐ[volume]
      fun z => phase s z - phase t z := by
    filter_upwards [Lp.coeFn_sub (phaseLinfty s) (phaseLinfty t), phaseLinfty_ae s,
      phaseLinfty_ae t] with z h0 h1 h2
    simpa only [Pi.sub_apply, h1, h2] using h0
  apply le_antisymm
  · rw [Lp.norm_def, eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [hae] with z hz
    rw [hz]
    exact (norm_sub_le _ _).trans (by rw [norm_phase, norm_phase]; norm_num)
  · have hz : (s-t)/(2*Real.pi) ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr h) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have hb := local_symbol_norm_le_linfty (phaseLinfty s - phaseLinfty t)
      (fun z => phase s z - phase t z) ((s-t)/(2*Real.pi)) hae
      ((continuousAt_phase s _ hz).sub (continuousAt_phase t _ hz))
    rwa [phase_sub_half_turn s t h] at hb

/-- The raw unitary evolution has maximal pairwise operator distance at all distinct times. -/
theorem norm_evolution_sub (s t : ℝ) :
    ‖(evolution s).toContinuousLinearEquiv.toContinuousLinearMap - (evolution t).toContinuousLinearEquiv.toContinuousLinearMap‖ =
      if s = t then 0 else 2 := by
  rw [evolution_eq_lineLinftyMultiplier, evolution_eq_lineLinftyMultiplier,
    ← map_sub, norm_lineLinftyMultiplier, norm_phaseLinfty_sub]

/-- Each actual raw singular-phase orbit is continuous on the L2 carrier. -/
theorem continuous_evolution_apply (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun t => evolution t u) := by
  have hf (t : ℝ) : MemLp (fun z => phase t z * u z) 2 volume :=
    (memLp_phase_iff t 2 (u : ℝ → ℂ)).2 (Lp.memLp u)
  have he (t : ℝ) : evolution t u = (hf t).toLp _ := by
    apply Lp.ext
    exact (evolution_ae t u).trans (hf t).coeFn_toLp.symm
  simp_rw [he]
  apply continuous_toLp_two_of_dominated volume _ hf (fun z => ‖u z‖) (Lp.memLp u).norm
  · intro t
    exact .of_forall fun z => by rw [norm_mul, norm_phase, one_mul]
  · apply Eventually.of_forall
    intro z
    unfold phase
    fun_prop

/-- Despite continuous vector orbits, the raw evolution is nowhere continuous in operator norm. -/
theorem evolution_not_operator_continuousAt (t : ℝ) :
    ¬ ContinuousAt (fun s => (evolution s).toContinuousLinearEquiv.toContinuousLinearMap) t := by
  intro hc
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  have hn : t + δ/2 ≠ t := by linarith
  have hd : dist (t + δ/2) t < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith : 0 < δ/2)]
    linarith
  have hb := h hd
  rw [dist_eq_norm, norm_evolution_sub, if_neg hn] at hb
  norm_num at hb

/-- An explicit strongly continuous family whose operator-norm distances are always maximal off the diagonal. -/
theorem evolution_strong_continuity_maximal_norm_separation :
    (∀ u : Lp ℂ 2 (volume : Measure ℝ), Continuous (fun t => evolution t u)) ∧
    (∀ s t : ℝ, ‖(evolution s).toContinuousLinearEquiv.toContinuousLinearMap -
      (evolution t).toContinuousLinearEquiv.toContinuousLinearMap‖ = if s = t then 0 else 2) ∧
    (∀ t : ℝ, ¬ ContinuousAt (fun s =>
      (evolution s).toContinuousLinearEquiv.toContinuousLinearMap) t) :=
  ⟨continuous_evolution_apply, norm_evolution_sub, evolution_not_operator_continuousAt⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
