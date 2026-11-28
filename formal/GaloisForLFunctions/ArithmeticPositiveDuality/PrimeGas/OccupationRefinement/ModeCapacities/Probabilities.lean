import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Profiles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Probabilities

/-! # Conditional probabilities for channels with prime-dependent capacities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open Finset

def branch (u v : ℕ → ℝ) (a b : ℕ) := profile u a * profile v b / profile (u+v) (a*b)

theorem branch_pos {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (a b : ℕ+) :
    0<branch u v a.val b.val :=
  div_pos (mul_pos (profile_pos hu a) (profile_pos hv b)) (profile_pos (positive_add hu hv) (a*b))

theorem branch_sum {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (n : ℕ+) :
    ∑ d ∈ n.val.divisorsAntidiagonal, branch u v d.1 d.2=1 := by
  calc
    _ = (∑ d ∈ n.val.divisorsAntidiagonal, profile u d.1*profile v d.2)/profile (u+v) n.val := by
      rw [sum_div]
      exact sum_congr rfl fun d hd => by rw [branch,(Nat.mem_divisorsAntidiagonal.mp hd).1]
    _ = 1 := by rw [←ArithmeticFunction.mul_apply,profile_add,div_self (profile_pos (positive_add hu hv) n).ne']

/-- A common change of capacity units at each prime leaves every share invariant. -/
theorem branch_rescale (g u v : ℕ → ℝ) (hg : positive g) (a b : ℕ+) :
    branch (g*u) (g*v) a.val b.val=branch u v a.val b.val := by
  change profile (g*u) a.val * profile (g*v) b.val / profile (g*u+g*v) (a*b).val = _
  rw [←mul_add,twist_profile g u a,twist_profile g v b,twist_profile g (u+v) (a*b),twist_mul]
  rw [show twistFactor g a*profile u a.val*(twistFactor g b*profile v b.val) =
    (twistFactor g a*twistFactor g b)*(profile u a.val*profile v b.val) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero (twist_pos hg a).ne' (twist_pos hg b).ne')

theorem branch_on_ray (u v : ℕ → ℝ) (p : Nat.Primes) (j k : ℕ) :
    branch u v (p.val^j) (p.val^k) = probability (u p.val) (v p.val) (p.val^j) (p.val^k) := by
  rw [branch,probability,←pow_add]
  simp only [prime_power _ p.property,weight_prime_pow _ _ _ p.property,Pi.add_apply]

#print axioms branch_sum
#print axioms branch_rescale
#print axioms branch_on_ray

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
