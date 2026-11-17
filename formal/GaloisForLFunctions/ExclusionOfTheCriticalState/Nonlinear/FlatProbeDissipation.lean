import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexPotential
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheGammaPairingInLevyForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaContractions

/-!
# Flat convex tests of actual finite probe profiles

The flat gradient from arXiv:2611.08616 preserves the full half-line energy
domain for every finite signed combination of admissible probes. Its mixed
Gamma jump energy lies between the transformed and original energies.
The transform and its complement also split the original jump energy
contractively. Every domain condition is proved for the explicit profile.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower
noncomputable section

/-- A finite signed probe profile with automatically admissible exponents. -/
def probeSum (p c : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, c i * probe (5 + |p i|) u

/-- Full Gamma, exponential-weight and physical integrability hold for every coefficient vector. -/
theorem probeSum_domain (p c : ℕ → ℝ) (n : ℕ) :
    CriticalHalfLineEnergyDomain (probeSum p c n) := by
  induction n with
  | zero =>
    have h := (criticalHalfLineEnergyDomain_probe (p := 5) (by norm_num)).const_mul 0
    have he : probeSum p c 0 = fun _ => 0 := by
      funext u
      simp only [probeSum, Finset.range_zero, Finset.sum_empty]
    rw [he]
    simpa only [zero_mul] using h
  | succ n ih =>
    have hp : 4 < 5 + |p n| := by linarith only [abs_nonneg (p n)]
    have h := ih.add_const_mul (criticalHalfLineEnergyDomain_probe hp) (c n)
    have he : probeSum p c (n + 1) =
        fun u => probeSum p c n u + c n * probe (5 + |p n|) u := by
      funext u
      exact Finset.sum_range_succ _ _
    rw [he]
    exact h

/-- The flat nonlinear test is in the actual energy domain, not merely a formal test class. -/
theorem transformed_probeSum_domain (p c : ℕ → ℝ) (n : ℕ) :
    CriticalHalfLineEnergyDomain (gradient ∘ probeSum p c n) :=
  (probeSum_domain p c n).comp_contraction gradient_contraction gradient_zero

theorem complement_probeSum_domain (p c : ℕ → ℝ) (n : ℕ) :
    CriticalHalfLineEnergyDomain (fun u => probeSum p c n u - gradient (probeSum p c n u)) := by
  have h := (probeSum_domain p c n).add_const_mul (transformed_probeSum_domain p c n) (-1)
  simpa only [Function.comp_apply, neg_one_mul, sub_eq_add_neg] using h

/-- Both pointwise jump inequalities remain valid after integration in the profile variable. -/
theorem integrated_jump_bounds (p c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (∫ u, (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x))) ^ 2) ≤
      (∫ u, (probeSum p c n u - probeSum p c n (u + x)) *
        (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x)))) ∧
    (∫ u, (probeSum p c n u - probeSum p c n (u + x)) *
        (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x)))) ≤
      ∫ u, (probeSum p c n u - probeSum p c n (u + x)) ^ 2 := by
  have hf := (probeSum_domain p c n).memLp_real
  have ht := (transformed_probeSum_domain p c n).memLp_real
  have hdf := hf.sub (memLp_two_shift hf x)
  have hdt := ht.sub (memLp_two_shift ht x)
  have hi := integrable_mul_of_memLp hdf hdt
  constructor
  · exact integral_mono (integrable_sq_of_memLp hdt) hi fun u => (jump_bounds _ _).1
  · exact integral_mono hi (integrable_sq_of_memLp hdf) fun u => (jump_bounds _ _).2

/-- The actual mixed jump integrand is absolutely integrable. -/
theorem integrableOn_flat_probe_dissipation (p c : ℕ → ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u,
      (probeSum p c n u - probeSum p c n (u + x)) *
        (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x)))) (Ioi 0) := by
  have hf := (probeSum_domain p c n).meas
  have ht := gradient_contraction.continuous.measurable
  have hm : Measurable (fun q : ℝ × ℝ =>
      (probeSum p c n q.2 - probeSum p c n (q.2 + q.1)) *
        (gradient (probeSum p c n q.2) - gradient (probeSum p c n (q.2 + q.1)))) := by
    fun_prop
  refine (probeSum_domain p c n).integrableOn_levyIntegrand.mono'
    (measurable_archLevyDensity.aestronglyMeasurable.mul
      hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hnonneg : 0 ≤ ∫ u, (probeSum p c n u - probeSum p c n (u + x)) *
      (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x))) :=
    integral_nonneg fun u => (sq_nonneg _).trans (jump_bounds _ _).1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos hx).le hnonneg)]
  exact mul_le_mul_of_nonneg_left (integrated_jump_bounds p c n x).2
    (archLevyDensity_pos hx).le

/-- The flat mixed pairing is sandwiched between two genuine finite Gamma jump energies. -/
theorem levy_bounds (p c : ℕ → ℝ) (n : ℕ) :
    levyEnergy (gradient ∘ probeSum p c n) ≤
      levyMixed (probeSum p c n) (gradient ∘ probeSum p c n) ∧
    levyMixed (probeSum p c n) (gradient ∘ probeSum p c n) ≤ levyEnergy (probeSum p c n) := by
  have hi := integrableOn_flat_probe_dissipation p c n
  constructor
  · apply integral_mono_ae (transformed_probeSum_domain p c n).integrableOn_levyIntegrand hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_left (integrated_jump_bounds p c n x).1
      (archLevyDensity_pos hx).le
  · apply integral_mono_ae hi (probeSum_domain p c n).integrableOn_levyIntegrand
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_le_mul_of_nonneg_left (integrated_jump_bounds p c n x).2
      (archLevyDensity_pos hx).le

/-- Splitting into the flat transform and its complement cannot increase total jump energy. -/
theorem complementary_levy_bound (p c : ℕ → ℝ) (n : ℕ) :
    levyEnergy (gradient ∘ probeSum p c n) +
      levyEnergy (fun u => probeSum p c n u - gradient (probeSum p c n u)) ≤
        levyEnergy (probeSum p c n) := by
  have hF := probeSum_domain p c n
  have hT := transformed_probeSum_domain p c n
  have hC := complement_probeSum_domain p c n
  unfold levyEnergy
  rw [← integral_add hT.integrableOn_levyIntegrand hC.integrableOn_levyIntegrand]
  apply integral_mono_ae
    (hT.integrableOn_levyIntegrand.add hC.integrableOn_levyIntegrand) hF.integrableOn_levyIntegrand
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hiT := integrable_sq_of_memLp (hT.memLp_real.sub (memLp_two_shift hT.memLp_real x))
  have hiC := integrable_sq_of_memLp (hC.memLp_real.sub (memLp_two_shift hC.memLp_real x))
  have hiF := integrable_sq_of_memLp (hF.memLp_real.sub (memLp_two_shift hF.memLp_real x))
  simp only [Pi.sub_apply, Function.comp_apply] at hiT hiC hiF
  have hinner :
      (∫ u, (gradient (probeSum p c n u) - gradient (probeSum p c n (u + x))) ^ 2) +
        (∫ u, ((probeSum p c n u - gradient (probeSum p c n u)) -
          (probeSum p c n (u + x) - gradient (probeSum p c n (u + x)))) ^ 2) ≤
        ∫ u, (probeSum p c n u - probeSum p c n (u + x)) ^ 2 := by
    rw [← integral_add hiT hiC]
    exact integral_mono (hiT.add hiC) hiF fun u => complementary_jump_bound _ _
  dsimp only [Function.comp_apply, Pi.add_apply]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left hinner (archLevyDensity_pos hx).le

#print axioms probeSum_domain
#print axioms transformed_probeSum_domain
#print axioms levy_bounds
#print axioms complementary_levy_bound

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
