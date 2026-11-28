import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Profiles

/-! # Dirichlet composition with different capacities at different primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open Finset RHTower.Sieve

/-- A capacity is specified independently at every prime. Values at nonprimes
do not enter the profile. -/
def positive (u : ℕ → ℝ) := ∀ p : Nat.Primes, 0<u p.val

def profile (u : ℕ → ℝ) := localEuler fun p k => divided (u p) k

theorem prime_power (u : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    profile u (p^k)=divided (u p) k := by
  have h := localEuler_prime_pow (fun q j => divided (u q) j) (⟨p,hp⟩ : Nat.Primes) k
  change profile u (p^k) = if k=0 then 1 else divided (u p) k at h
  rcases eq_or_ne k 0 with rfl|hk
  · simpa [divided] using h
  · simpa only [if_neg hk] using h

theorem profile_add (u v : ℕ → ℝ) : profile u * profile v=profile (u+v) := by
  have mult (f : ℕ → ℝ) : (profile f).IsMultiplicative := localEuler_isMultiplicative _
  apply ((mult u).mul (mult v)).eq_iff_eq_on_prime_powers _ _ (mult (u+v)) |>.mpr
  intro p k hp
  rw [RHTower.DampedMobius.mul_apply_prime_pow _ _ hp]
  simp only [prime_power _ hp,divided_add,Pi.add_apply]

theorem positive_add {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) : positive (u+v) :=
  fun p => add_pos (hu p) (hv p)

theorem profile_pos {u : ℕ → ℝ} (hu : positive u) (n : ℕ+) : 0<profile u n.val := by
  change 0 < if n.val=0 then 0 else _
  rw [if_neg n.ne_zero]
  exact prod_pos fun p hp =>
    div_pos (pow_pos (hu ⟨p,Nat.prime_of_mem_primeFactors hp⟩) _) (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem profile_one (u : ℕ → ℝ) : profile u 1=1 := localEuler_one _

/-- The factor remaining after multiplying each elementary capacity by a
prime-dependent weight g. -/
def twistFactor (g : ℕ → ℝ) (n : ℕ+) := ∏ p ∈ n.val.primeFactors, (g p)^(n.val.factorization p)

theorem twist_mul (g : ℕ → ℝ) (a b : ℕ+) : twistFactor g (a*b)=twistFactor g a*twistFactor g b := by
  have h (m : ℕ+) : twistFactor g m=m.val.factorization.prod (fun p k => (g p)^k) := by
    simp only [twistFactor,Finsupp.prod,Nat.support_factorization]
  rw [h,h,h,PNat.mul_coe,Nat.factorization_mul a.ne_zero b.ne_zero]
  exact Finsupp.prod_add_index' (fun p => pow_zero (g p)) (fun p i j => pow_add (g p) i j)

theorem twist_pos {g : ℕ → ℝ} (hg : positive g) (n : ℕ+) : 0<twistFactor g n :=
  prod_pos fun p hp => pow_pos (hg ⟨p,Nat.prime_of_mem_primeFactors hp⟩) _

theorem twist_profile (g u : ℕ → ℝ) (n : ℕ+) :
    profile (g*u) n.val=twistFactor g n*profile u n.val := by
  change (if n.val=0 then 0 else _) = _ * (if n.val=0 then 0 else _)
  simp only [if_neg n.ne_zero,twistFactor,←prod_mul_distrib]
  refine prod_congr rfl fun p _ => ?_
  rw [Pi.mul_apply,divided,divided,mul_pow,mul_div_assoc]

#print axioms profile_add
#print axioms profile_pos
#print axioms twist_profile

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
