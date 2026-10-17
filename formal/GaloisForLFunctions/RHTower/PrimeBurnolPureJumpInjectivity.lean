import GaloisForLFunctions.RHTower.PrimeBurnolLevyEvolution

/-! Infinite jump activity is injective: bounded cutoff inverses recover the identity strongly. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
namespace BurnolLevyData
variable (D : BurnolLevyData)

/-- A bounded backward cutoff cancels exactly the large-jump part of the full evolution. -/
theorem tailEvolution_factor (n : ℕ) (t : ℝ≥0) :
    (D.tailSymbol n).evolution t = D.finiteEvolution n (-(t : ℝ)) * D.withoutDrift.evolution t := by
  apply primeBurnol_operator_ext
  intro p
  have hp : 0 ≤ (Real.log (p : ℝ) : ℂ).re :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  rw [BurnolAccretiveSymbol.evolution_prime, mul_apply_eq_comp,
    D.withoutDrift.evolution_prime, map_smul, D.finiteEvolution_prime,
    smul_smul, ← Complex.exp_add]
  apply congrArg (fun z : ℂ => Complex.exp z • primeLogCriticalLaplaceFeatureL2 p)
  simp only [tailSymbol_apply, withoutDrift_exponent, Complex.ofReal_neg, neg_neg]
  rw [levyLaplaceJump_split D.control hp n]
  ring

theorem tendsto_tailEvolution_identity (t : ℝ≥0) (f : BurnolHalfLineL2) :
    Tendsto (fun n => (D.tailSymbol n).evolution t f) atTop (𝓝 f) := by
  apply tendsto_primeBurnol_contractions (S := (1 : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2))
    (fun n => (D.tailSymbol n).norm_evolution_le t)
    (by simpa only [D.symbol.evolution_zero] using D.symbol.norm_evolution_le 0)
  intro p
  have hp : 0 ≤ (Real.log (p : ℝ) : ℂ).re :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  have hj := tendsto_levyLaplaceSmallControl_zero D.control hp
  have he : Tendsto
      (fun n => Complex.exp (-((t : ℝ) : ℂ) *
        levyLaplaceJump (levySmallControl D.control n) (Real.log (p : ℝ)))) atTop
      (𝓝 (1 : ℂ)) := by
    simpa only [mul_zero, Complex.exp_zero, Function.comp_apply] using!
      Complex.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := -((t : ℝ) : ℂ))).mul hj)
  simpa [BurnolAccretiveSymbol.evolution_prime, BurnolAccretiveSymbol.evolutionFn] using!
    he.smul (tendsto_const_nhds (x := (primeLogCriticalLaplaceFeatureL2 p : BurnolHalfLineL2)))

theorem withoutDrift_evolution_eq_zero_iff (t : ℝ≥0) (f : BurnolHalfLineL2) :
    D.withoutDrift.evolution t f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have he (n : ℕ) : (D.tailSymbol n).evolution t f = 0 := by
      rw [D.tailEvolution_factor, mul_apply_eq_comp, hf, map_zero]
    have hlim : Tendsto (fun n => (D.tailSymbol n).evolution t f) atTop (𝓝 (0 : BurnolHalfLineL2)) := by
      simpa only [he] using (tendsto_const_nhds (x := (0 : BurnolHalfLineL2)))
    exact tendsto_nhds_unique (D.tendsto_tailEvolution_identity t f) hlim
  · rintro rfl
    exact map_zero _

/-- No nonzero physical vector is lost to pure jumps, even with infinite total jump mass. -/
theorem withoutDrift_evolution_injective (t : ℝ≥0) :
    Function.Injective (D.withoutDrift.evolution t) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (D.withoutDrift_evolution_eq_zero_iff t (f - g)).mp
  rw [map_sub, hfg, sub_self]

theorem evolution_eq_zero_iff_shift (t : ℝ≥0) (f : BurnolHalfLineL2) :
    D.evolution t f = 0 ↔ burnolWeightedShift (D.drift * t) f = 0 := by
  rw [D.evolution_factor, mul_apply_eq_comp, D.withoutDrift_evolution_eq_zero_iff]

end BurnolLevyData
end RHTower
