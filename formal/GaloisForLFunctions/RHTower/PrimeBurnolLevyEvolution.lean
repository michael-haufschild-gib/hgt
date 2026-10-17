import GaloisForLFunctions.RHTower.PrimeBurnolLevySymbol

/-! Positive physical evolution obtained from finite jump cutoffs on the same carrier. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

theorem tendsto_primeBurnol_contractions
    {T : ℕ → BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2}
    {S : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2}
    (hT : ∀ n, ‖T n‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hp : ∀ p : Nat.Primes,
      Tendsto (fun n => T n (primeLogCriticalLaplaceFeatureL2 p)) atTop
        (𝓝 (S (primeLogCriticalLaplaceFeatureL2 p)))) (f : BurnolHalfLineL2) :
    Tendsto (fun n => T n f) atTop (𝓝 (S f)) := by
  apply tendsto_of_dense_of_uniform_bound (C := 1) zero_le_one
    (Eventually.of_forall hT) hS dense_primeLogCriticalLaplaceFeature_span
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨p, rfl⟩ := hv; exact hp p
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : BurnolHalfLineL2)))
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul c x hx ih => simpa only [map_smul] using (tendsto_const_nhds (x := c)).smul ih

theorem burnolWeightedShift_prime (h : ℝ≥0) (p : Nat.Primes) :
    burnolWeightedShift h (primeLogCriticalLaplaceFeatureL2 p) =
      Complex.exp (-((h : ℝ) : ℂ) * (Real.log (p : ℝ) : ℂ)) •
        primeLogCriticalLaplaceFeatureL2 p := by
  apply (primeBurnol_eigenvalue_iff _ p _).mpr
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  simpa only [primeBurnolRawFeature, burnolComplexFeature_ofReal, burnolRateFeature, Nat.cast_zero, zero_add,
    one_mul, mul_one, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
    mul_comm, neg_mul] using burnolWeightedShift_depthFeature h ⟨Real.log (p : ℝ), hp⟩ 0

namespace BurnolLevyData
variable (D : BurnolLevyData)

theorem finiteJumpData_rate (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((D.finiteJumpData n).rate x : ℂ) =
      -(((D.killing : ℝ) : ℂ) + levyLaplaceJump (levyLargeControl D.control n) x) := by
  have hj : ((∫ h : ℝ≥0, Real.exp (-(x * (h : ℝ))) - 1
      ∂levyFiniteJumpMeasure D.control n : ℝ) : ℂ) =
      -levyLaplaceJump (levyLargeControl D.control n) x := by
    rw [← integral_complex_ofReal, ← integral_levyFiniteJumpMeasure,
      ← integral_neg]
    apply integral_congr_ae
    refine Eventually.of_forall fun h => ?_
    simp only [Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_one, neg_mul]
    ring
  rw [(D.finiteJumpData n).rate_eq_jump_integral hx]
  change ((-(D.killing : ℝ) + ∫ h : ℝ≥0, Real.exp (-(x * (h : ℝ))) - 1
    ∂levyFiniteJumpMeasure D.control n : ℝ) : ℂ) = _
  rw [Complex.ofReal_add, Complex.ofReal_neg, hj]
  ring

def finiteEvolution (n : ℕ) (t : ℝ) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  burnolEvolution (D.finiteJumpData n).generator t

theorem finiteEvolution_prime (n : ℕ) (t : ℝ) (p : Nat.Primes) :
    D.finiteEvolution n t (primeLogCriticalLaplaceFeatureL2 p) =
      Complex.exp (-(t : ℂ) * (((D.killing : ℝ) : ℂ) +
        levyLaplaceJump (levyLargeControl D.control n) (Real.log (p : ℝ)))) •
          primeLogCriticalLaplaceFeatureL2 p := by
  have hp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  simpa only [finiteEvolution, D.finiteJumpData_rate n hp, mul_neg, neg_mul] using
    burnolEvolution_prime (D.finiteJumpData n).generator
      (fun p => ((D.finiteJumpData n).rate (Real.log (p : ℝ)) : ℂ))
      (D.finiteJumpData n).generator_prime t p

theorem tendsto_finiteEvolution (t : ℝ≥0) (f : BurnolHalfLineL2) :
    Tendsto (fun n => D.finiteEvolution n t f) atTop (𝓝 (D.withoutDrift.evolution t f)) := by
  apply tendsto_primeBurnol_contractions (T := fun n => D.finiteEvolution n t)
    (fun n => (D.finiteJumpData n).evolution_contraction t.coe_nonneg)
    (D.withoutDrift.norm_evolution_le t)
  intro p
  have hp : 0 ≤ (Real.log (p : ℝ) : ℂ).re :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
  have hj := tendsto_levyLaplaceLargeControl D.control hp
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := -((t : ℝ) : ℂ))).mul
      ((tendsto_const_nhds (x := ((D.killing : ℝ) : ℂ))).add hj))
  simpa only [D.finiteEvolution_prime, D.withoutDrift.evolution_prime,
    D.withoutDrift_exponent, Function.comp_apply] using!
    he.smul (tendsto_const_nhds (x := (primeLogCriticalLaplaceFeatureL2 p : BurnolHalfLineL2)))

theorem withoutDrift_evolution_positive (t : ℝ≥0) :
    BurnolPreservesNonnegativity (D.withoutDrift.evolution t) := by
  intro f hf
  exact le_of_tendsto (α := OrderDual BurnolHalfLineL2) (D.tendsto_finiteEvolution t f)
    (Eventually.of_forall fun n => (D.finiteJumpData n).evolution_positive t.coe_nonneg f hf)

/-- Drift is the literal left shift; jump activity contributes an independent factor. -/
theorem evolution_factor (t : ℝ≥0) :
    D.evolution t = D.withoutDrift.evolution t * burnolWeightedShift (D.drift * t) := by
  apply primeBurnol_operator_ext
  intro p
  rw [D.evolution_prime, mul_apply_eq_comp, burnolWeightedShift_prime, map_smul,
    D.withoutDrift.evolution_prime, smul_smul, ← Complex.exp_add]
  apply congrArg (fun z : ℂ => Complex.exp z • primeLogCriticalLaplaceFeatureL2 p)
  simp only [exponent, withoutDrift, NNReal.coe_zero, Complex.ofReal_zero,
    zero_mul, add_zero, NNReal.coe_mul, Complex.ofReal_mul]
  ring

theorem evolution_positive (t : ℝ≥0) : BurnolPreservesNonnegativity (D.evolution t) := by
  intro f hf
  rw [D.evolution_factor, mul_apply_eq_comp]
  exact D.withoutDrift_evolution_positive t _ (burnolWeightedShift_nonneg _ hf)

end BurnolLevyData
end RHTower
