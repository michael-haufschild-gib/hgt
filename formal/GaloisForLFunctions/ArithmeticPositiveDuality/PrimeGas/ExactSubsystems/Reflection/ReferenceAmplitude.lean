import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Marginal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalResidueState

/-! # The heat amplitude relative to the measured equilibrium boundary state -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology InverseSpectrum.ShellMixing
open _root_.HTGeometry (finiteGibbsPartition finiteGibbsPartition_pos finiteGibbsStateWeight)

/-- Square of the reference amplitude is the measured equilibrium odds against vacuum. -/
theorem boundary_reference_odds {ι κ : Type*} [Fintype ι] (χ : ℕ+ → Circle)
    {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) (i : ι) :
    Tendsto (fun β => marginal χ β a b i / marginal χ β a b (factorVacuum h)) atPartitionPole
      (𝓝 (‖heat (1/2) (a i)‖^2)) := by
  letI : Nonempty ι := ⟨i⟩
  have hr (β : TraceTemperature) :
      marginal χ β a b i / marginal χ β a b (factorVacuum h) = Real.exp (-β.val*energy (a i)) := by
    rw [marginal_eq_gibbs χ β h,marginal_eq_gibbs χ β h]
    simp only [finiteGibbsStateWeight,factorVacuum_label h,show energy 1 = 0 by simp [energy],
      mul_zero,Real.exp_zero]
    field_simp [(finiteGibbsPartition_pos β.val (fun j => energy (a j))).ne']
  have hval : ‖heat (1/2) (a i)‖^2 = Real.exp (-(1:ℝ)*energy (a i)) := by
    rw [norm_heat,sq,← Real.exp_add]
    congr 1
    rw [show (1/2:ℂ).re = 1/2 by norm_num]
    ring
  have ht : Tendsto (fun β : TraceTemperature => β.val) atPartitionPole (𝓝 (1:ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hc : Continuous (fun t : ℝ => Real.exp (-t*energy (a i))) := (continuous_id.neg.mul_const _).rexp
  simp only [hr,hval]
  exact (hc.tendsto 1).comp ht

/-- Heat coefficient divided by the square root of the pole-state odds. -/
def relativeCoefficient (s : ℂ) (n : ℕ+) := heat (s-1/2) n

theorem relativeCoefficient_eq_ratio (s : ℂ) (n : ℕ+) :
    relativeCoefficient s n = heat s n / heat (1/2) n := by
  have hn : heat (1/2) n ≠ 0 := Complex.exp_ne_zero _
  apply (eq_div_iff hn).mpr
  rw [relativeCoefficient,← heat_add,sub_add_cancel]

#print axioms boundary_reference_odds
#print axioms relativeCoefficient_eq_ratio

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
