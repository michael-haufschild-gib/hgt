import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Vacuum

/-! # Forward-time evolution obtained by projecting onto no emitted particles -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open ModeCapacities
open scoped NNReal

def evolution (A : Response) (t : ℝ≥0) : Gas →L[ℂ] Gas :=
  if ht : 0 < (t:ℝ) then vacuum A ⟨t,ht⟩ else ContinuousLinearMap.id ℂ Gas

def survivalAmplitude (A : Response) (n : ℕ+) (t : ℝ≥0) :=
  A.val (Real.exp (-(t:ℝ) * energy n))

theorem evolution_apply (A : Response) (t : ℝ≥0) (f : Gas) (n : ℕ+) :
    evolution A t f n = survivalAmplitude A n t * f n := by
  by_cases ht : 0 < (t:ℝ)
  · rw [evolution, dif_pos ht, vacuum_apply, survivalAmplitude]
  · have eqn := le_antisymm (not_lt.mp ht) t.property
    rw [evolution, dif_neg ht, survivalAmplitude, eqn, neg_zero, zero_mul, Real.exp_zero,
      response_at_one, one_mul, ContinuousLinearMap.id_apply]

theorem survival_zero (A : Response) (n : ℕ+) : survivalAmplitude A n 0 = 1 := by
  simp only [survivalAmplitude, NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero, response_at_one]

theorem survival_ne (A : Response) (n : ℕ+) (t : ℝ≥0) : survivalAmplitude A n t ≠ 0 := by
  intro h
  have mass := A.property.2 _ (survival_share t.property n)
  change ‖survivalAmplitude A n t‖ ^ 2 = _ at mass
  rw [h, norm_zero, zero_pow two_ne_zero] at mass
  exact (Real.exp_pos _).ne mass

theorem survival_add (A : Response) (n : ℕ+) (t u : ℝ≥0) :
    survivalAmplitude A n (t+u) = survivalAmplitude A n t * survivalAmplitude A n u := by
  simp only [survivalAmplitude, NNReal.coe_add, neg_add, add_mul, Real.exp_add]
  exact A.property.1 _ (survival_share t.property n) _ (survival_share u.property n)

theorem evolution_add (A : Response) (t u : ℝ≥0) :
    evolution A (t+u) = evolution A t ∘L evolution A u := by
  ext f n
  simp only [ContinuousLinearMap.comp_apply, evolution_apply, survival_add, mul_assoc]

#print axioms evolution_apply
#print axioms evolution_add

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
