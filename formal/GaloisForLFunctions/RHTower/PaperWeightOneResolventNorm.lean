import GaloisForLFunctions.RHTower.PaperWeightOneResolventRigidity
import GaloisForLFunctions.HTGeometry.CircleSymbolGroupCStar

/-!
# Exact compact gap and continuous squared-mass response

Every actual Clifford-square resolvent at `i` has norm and essential norm exactly one.
Differences nevertheless shrink at most as fast as the squared-mass difference. The compact
ideal therefore retains exact mass information at arbitrarily small operator-norm scales.
-/

namespace RHTower

noncomputable section
open MeasureTheory Complex Filter
open GaloisForLFunctions.HTGeometry
open scoped ENNReal Topology

/-- The self-adjoint resolvent estimate has unit bound at `i`. -/
theorem paperWeightOneResolvent_norm_le_one (a : ℝ) :
    ‖paperWeightOneResolvent a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [paperWeightOneResolvent, resolventCLM_apply, Complex.I_im, abs_one,
    inv_one, one_mul] using
    norm_resolventLinear_le (weightOneSpectralSquare_isSelfAdjoint a) (z := I) (by simp) f

/-- The unit bound is attained in operator norm, for every real mass. -/
theorem paperWeightOneResolvent_norm (a : ℝ) :
    ‖paperWeightOneResolvent a‖ = 1 := by
  apply le_antisymm (paperWeightOneResolvent_norm_le_one a)
  have hc : Continuous (fun x : ℝ => ((weightOneSpectralSquareEnergy a x : ℂ) - I)⁻¹) := by
    apply Continuous.inv₀
    · apply Continuous.sub _ continuous_const
      apply Complex.continuous_ofReal.comp
      unfold weightOneSpectralSquareEnergy
      fun_prop
    · intro x
      exact realEnergy_sub_nonreal_ne_zero _ (by simp)
  have h := le_norm_lpBoundedMulCLM
    (((Complex.measurable_ofReal.comp (measurable_weightOneSpectralSquareEnergy a)).sub
      measurable_const).inv)
    (inv_nonneg.mpr (abs_nonneg I.im))
    (fun x => norm_realEnergy_resolventSymbol_le (weightOneSpectralSquareEnergy a x)
      (z := I) (by simp)) (hc.continuousAt (x := a / (2 * Real.pi)))
  rw [← maximalRealL2Mul_resolvent_eq_multiplier volume
    (measurable_weightOneSpectralSquareEnergy a) (z := I) (by simp)] at h
  change ‖((weightOneSpectralSquareEnergy a (a / (2 * Real.pi)) : ℂ) - I)⁻¹‖ ≤
    ‖paperWeightOneResolvent a‖ at h
  have he : weightOneSpectralSquareEnergy a (a / (2 * Real.pi)) = 0 := by
    unfold weightOneSpectralSquareEnergy
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [he, Complex.ofReal_zero, zero_sub, norm_inv, norm_neg, Complex.norm_I,
    inv_one] using h

/-- Every native resolvent remains exactly distance one from the compact ideal. -/
theorem paperWeightOneResolvent_compact_gap (a : ℝ) :
    compactIdealDistance (paperWeightOneResolvent a) = 1 := by
  rw [paperWeightOneResolvent_compactIdealDistance, paperWeightOneResolvent_norm]

/-- No finite-rank or compact correction can beat the exact unit gap. -/
theorem paperWeightOneResolvent_norm_sub_compact_ge_one (a : ℝ)
    (K : compactOperatorStarAlgebra SoninL2) :
    1 ≤ ‖paperWeightOneResolvent a - K.1‖ := by
  rw [← paperWeightOneResolvent_norm a]
  exact paperModulationCommutant_norm_le_sub_compact
    ⟨_, paperWeightOneResolvent_mem_commutant a⟩ K

/-- Resolvent changes are controlled by the exact squared-mass difference. -/
theorem paperWeightOneResolvent_norm_sub_le (a b : ℝ) :
    ‖paperWeightOneResolvent a - paperWeightOneResolvent b‖ ≤ |a^2 - b^2| := by
  rw [paperWeightOneResolvent_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hprod : ‖paperWeightOneResolvent a * paperWeightOneResolvent b‖ ≤ 1 := by
    simpa only [paperWeightOneResolvent_norm, one_mul] using
      norm_mul_le (paperWeightOneResolvent a) (paperWeightOneResolvent b)
  calc
    |b^2 - a^2| * ‖paperWeightOneResolvent a * paperWeightOneResolvent b‖ ≤
        |b^2 - a^2| * 1 := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = |a^2 - b^2| := by rw [mul_one, abs_sub_comm]

/-- The actual resolvent family is continuous in operator norm. -/
theorem continuous_paperWeightOneResolvent : Continuous paperWeightOneResolvent := by
  rw [continuous_iff_continuousAt]
  intro a
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hc : Continuous (fun b : ℝ => b^2) := continuous_id.pow 2
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := a)) ε hε
  refine ⟨δ, hδ, fun b hb => ?_⟩
  rw [dist_eq_norm]
  exact (paperWeightOneResolvent_norm_sub_le b a).trans_lt
    (by simpa only [Real.dist_eq] using hd hb)

/-- A zero essential distance recovers precisely the squared mass. -/
theorem paperWeightOneResolvent_compact_distance_eq_zero_iff (a b : ℝ) :
    compactIdealDistance (paperWeightOneResolvent a - paperWeightOneResolvent b) = 0 ↔
      a^2 = b^2 := by
  rw [paperWeightOneResolvent_compactIdealDistance_sub, norm_eq_zero, sub_eq_zero,
    paperWeightOneResolvent_eq_iff]

/-- Nonzero mass corrections can vanish in operator norm along an explicit sequence. -/
theorem paperWeightOneResolvent_small_mass_tendsto :
    Tendsto (fun n : ℕ => paperWeightOneResolvent (1 / ((n : ℝ) + 1)) -
      paperWeightOneResolvent 0) atTop (𝓝 0) := by
  have h := (continuous_paperWeightOneResolvent.tendsto 0).comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Function.comp_def, sub_self] using h.sub_const (paperWeightOneResolvent 0)

/-- Every term of that vanishing correction sequence still has infinite ideal cost. -/
theorem paperWeightOneResolvent_small_mass_traceCost (n : ℕ) :
    compactOperatorTraceCost SoninL2
      (paperWeightOneResolvent (1 / ((n : ℝ) + 1)) - paperWeightOneResolvent 0) = ∞ := by
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  simp [paperWeightOneResolvent_difference_traceCost, hn]

end
end RHTower
