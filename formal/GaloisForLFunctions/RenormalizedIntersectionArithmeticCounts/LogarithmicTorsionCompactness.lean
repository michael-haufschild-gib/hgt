import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicTorsionCompletion

/-!
# Compactness of logarithmic torsion

Strictly decreasing logarithmic exponent gives a compact inclusion that preserves
the original arithmetic coefficients. The torsion form factors through each
smaller admissible exponent, so its Hilbert representative is compact.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HeightHomotopyArithmeticCounts HTGeometry.LpDiagonal

/-- The coordinate multiplier preserving arithmetic coefficients when logarithmic weight decreases. -/
def logProbeWeightFactor (α β : ℝ) (n : ℕ) : ℝ :=
  (logConductor (n+1))^((β-α)/2)

theorem logProbeWeightFactor_norm_le (α β : ℝ) (h : β ≤ α) (n : ℕ) :
    ‖(logProbeWeightFactor α β n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  change |(logConductor (n+1))^((β-α)/2)| ≤ 1
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [one_le_logConductor (n+1)]) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_logConductor (n+1))
    (by linarith only [h])

/-- Natural inclusion of logarithmically weighted arithmetic probes. -/
def logarithmicProbeInclusion (α β : ℝ) (h : β ≤ α) : LogarithmicProbe →L[ℝ] LogarithmicProbe :=
  probeRealPart.comp
    (((lpDiag (fun n => (logProbeWeightFactor α β n : ℂ)) 1 zero_le_one
      (logProbeWeightFactor_norm_le α β h)).restrictScalars ℝ).comp probeComplexify)

theorem logarithmicProbeInclusion_apply (α β : ℝ) (h : β ≤ α) (u : LogarithmicProbe) (n : ℕ) :
    logarithmicProbeInclusion α β h u n=logProbeWeightFactor α β n*u n := by
  change ((logProbeWeightFactor α β n : ℂ)*(u n : ℂ)).re = _
  simp only [←Complex.ofReal_mul,Complex.ofReal_re]

/-- Inclusion changes the normalization and retains the original coefficient sequence. -/
theorem logarithmicProbeInclusion_coefficients (α β : ℝ) (h : β ≤ α) (u : LogarithmicProbe) :
    logProbeCoefficients β (logarithmicProbeInclusion α β h u)=logProbeCoefficients α u := by
  funext n
  cases n with
  | zero => simp only [logProbeCoefficients,probeCoefficients_zero,zero_div]
  | succ n =>
    simp only [logProbeCoefficients,probeCoefficients_succ,neg_zero,zero_div,Real.rpow_zero,mul_one,
      logarithmicProbeInclusion_apply,logProbeWeightFactor,logProbeWeight]
    have hn : 0 < logConductor (n+1) := lt_of_lt_of_le zero_lt_one (one_le_logConductor (n+1))
    rw [div_eq_mul_inv,div_eq_mul_inv,←Real.rpow_neg hn.le,←Real.rpow_neg hn.le]
    calc _ = u n*((logConductor (n+1))^((β-α)/2)*(logConductor (n+1))^(-(β/2))) := by ring
         _ = _ := by
          rw [←Real.rpow_add hn,show (β-α)/2 + -(β/2) = -(α/2) by ring]

/-- A strict decrease of logarithmic exponent gives a compact inclusion. -/
theorem logarithmicProbeInclusion_compact (α β : ℝ) (h : β < α) :
    IsCompactOperator (logarithmicProbeInclusion α β h.le) := by
  have ht : Tendsto (fun n : ℕ => ‖(logProbeWeightFactor α β n : ℂ)‖) cofinite (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hl : Tendsto (fun n : ℕ => logConductor (n+1)) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (Real.tendsto_log_atTop.comp hn)
    have hh := (tendsto_rpow_neg_atTop (show 0 < (α-β)/2 by linarith only [h])).comp hl
    rw [Nat.cofinite_eq_atTop]
    convert hh using 1
    funext n
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |(logConductor (n+1))^((β-α)/2)|=(logConductor (n+1))^(-((α-β)/2))
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [one_le_logConductor (n+1)]) _),
      show (β-α)/2 = -((α-β)/2) by ring]
  have hc := isCompactOperator_lpDiag (fun n => (logProbeWeightFactor α β n : ℂ)) 1 zero_le_one
    (logProbeWeightFactor_norm_le α β h.le) ht
  exact (hc.comp_clm probeComplexify).clm_comp probeRealPart

/-- Restrict continuous functionals along logarithmic inclusion. -/
def logarithmicProbeDualPrecomp (α β : ℝ) (h : β ≤ α) :
    (LogarithmicProbe →L[ℝ] ℝ) →L[ℝ] (LogarithmicProbe →L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ (LogarithmicProbe →L[ℝ] ℝ)
    (logarithmicProbeInclusion α β h)).comp
      (ContinuousLinearMap.compL ℝ LogarithmicProbe LogarithmicProbe ℝ)

/-- The full arithmetic pairing factors through each smaller admissible logarithmic weight. -/
theorem logarithmicTorsionForm_factor (α β : ℝ) (hα : 2 < α) (hβ : 2 < β) (h : β ≤ α) :
    logarithmicTorsionForm α hα = (logarithmicProbeDualPrecomp α β h).comp
      ((logarithmicTorsionForm β hβ).comp (logarithmicProbeInclusion α β h)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change logarithmicTorsionForm α hα u v = logarithmicTorsionForm β hβ
    (logarithmicProbeInclusion α β h u) (logarithmicProbeInclusion α β h v)
  rw [logarithmicTorsionForm_apply,logarithmicTorsionForm_apply,
    logarithmicProbeInclusion_coefficients,logarithmicProbeInclusion_coefficients]

/-- The original logarithmic torsion form is compact into the continuous dual. -/
theorem logarithmicTorsionForm_compact (α : ℝ) (hα : 2 < α) :
    IsCompactOperator (logarithmicTorsionForm α hα) := by
  have hβ : 2 < (α+2)/2 := by linarith only [hα]
  have h : (α+2)/2 < α := by linarith only [hα]
  rw [logarithmicTorsionForm_factor α ((α+2)/2) hα hβ h.le]
  exact ((logarithmicProbeInclusion_compact α ((α+2)/2) h).clm_comp
    (logarithmicTorsionForm ((α+2)/2) hβ)).clm_comp (logarithmicProbeDualPrecomp α ((α+2)/2) h.le)

/-- Every admissible logarithmic exponent gives a compact self-adjoint torsion operator. -/
theorem logarithmicTorsionOperator_compact (α : ℝ) (hα : 2 < α) :
    IsCompactOperator (logarithmicTorsionOperator α hα) :=
  (logarithmicTorsionForm_compact α hα).continuous_comp
    (InnerProductSpace.toDual ℝ LogarithmicProbe).symm.continuous

#print axioms logarithmicProbeInclusion_coefficients
#print axioms logarithmicProbeInclusion_compact
#print axioms logarithmicTorsionForm_factor
#print axioms logarithmicTorsionForm_compact
#print axioms logarithmicTorsionOperator_compact
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
