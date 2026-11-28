import GaloisForLFunctions.RHTower.Sieve.LocalEulerConstruction

/-! # Real capacity profiles for independent prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

open Finset
open RHTower.Sieve (localEuler localEuler_isMultiplicative localEuler_prime_pow)

def divided (u : ℝ) (k : ℕ) := u^k/(k.factorial:ℝ)

/-- Multiplicative extension of the divided powers on every prime ray. -/
def weight (u : ℝ) := localEuler fun _ k => divided u k

theorem weight_one (u : ℝ) : weight u 1=1 := RHTower.Sieve.localEuler_one _

theorem weight_prime_pow (u : ℝ) (p k : ℕ) (hp : p.Prime) :
    weight u (p^k)=divided u k := by
  have h := localEuler_prime_pow (fun _ j => divided u j) (⟨p,hp⟩ : Nat.Primes) k
  change weight u (p^k) = if k=0 then 1 else divided u k at h
  rcases eq_or_ne k 0 with rfl|hk
  · simpa [divided] using h
  · simpa only [if_neg hk] using h

theorem weight_pos (u : ℝ) (hu : 0<u) (n : ℕ+) : 0<weight u n.val := by
  change 0 < if n.val=0 then 0 else _
  rw [if_neg n.ne_zero]
  exact Finset.prod_pos fun p _ => div_pos (pow_pos hu _) (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem choose_quotient {k j : ℕ} (h : j≤k) :
    (k.choose j:ℝ)/(k.factorial:ℝ) = 1/((j.factorial:ℝ)*((k-j).factorial:ℝ)) := by
  have nz (a : ℕ) : (a.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  apply (div_eq_div_iff (nz k) (mul_ne_zero (nz j) (nz (k-j)))).mpr
  rw [one_mul,←mul_assoc]
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h

/-- The local convolution is the binomial theorem divided by the total factorial. -/
theorem divided_add (u v : ℝ) (k : ℕ) :
    (∑ j ∈ range (k+1), divided u j * divided v (k-j))=divided (u+v) k := by
  change _ = (u+v)^k/(k.factorial:ℝ)
  rw [add_pow,Finset.sum_div]
  refine sum_congr rfl fun j hj => ?_
  have h : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [mul_div_assoc,choose_quotient h]
  rw [divided,divided,div_mul_div_comm,mul_one_div]

/-- Capacities add under Dirichlet convolution on the entire integer spectrum. -/
theorem weight_add (u v : ℝ) : weight u * weight v=weight (u+v) := by
  have mult (a : ℝ) : (weight a).IsMultiplicative := localEuler_isMultiplicative _
  apply ((mult u).mul (mult v)).eq_iff_eq_on_prime_powers _ _ (mult (u+v)) |>.mpr
  intro p k hp
  rw [RHTower.DampedMobius.mul_apply_prime_pow _ _ hp]
  simp only [weight_prime_pow _ _ _ hp,divided_add]

#print axioms weight_prime_pow
#print axioms weight_pos
#print axioms divided_add
#print axioms weight_add

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
