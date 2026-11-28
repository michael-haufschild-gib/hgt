import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling.Recursion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Profiles

/-! # The prime profiles realize every choice of elementary weights -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling

open ArithmeticFunction ModeCapacities

theorem prime_value (u : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : profile u p=u p := by
  simpa [divided] using prime_power u hp 1

private theorem scale_two (n : ℕ+) : twistFactor (fun _ => (2:ℝ)) n=2^(cardFactors n.val) := by
  rw [twistFactor,Finset.prod_pow_eq_pow_sum,cardFactors_eq_sum_factorization]
  simp only [Finsupp.sum,Nat.support_factorization]

/-- Two independent copies double the capacity of every occupied prime. -/
theorem profile_law (u : ℕ → ℝ) : law (profile u) := by
  intro n
  by_cases h : n=0
  · subst n
    simp
  let m : ℕ+ := ⟨n,Nat.pos_of_ne_zero h⟩
  have twice : u+u=(fun _ => (2:ℝ))*u := funext fun i => (two_mul (u i)).symm
  rw [profile_add,twice]
  exact (twist_profile _ u m).trans (congrArg (fun a => a*profile u n) (scale_two m))

#print axioms prime_value
#print axioms profile_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling
