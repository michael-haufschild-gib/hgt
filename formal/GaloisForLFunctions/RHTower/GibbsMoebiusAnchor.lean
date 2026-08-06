import Mathlib
import GaloisForLFunctions.RHTower.GibbsParityVortex

/-!
# The gas at the parity point is the Möbius–Laplace current

The alternating sign `(-1)^{|T|}` carried by the gas at activity `-1` is the Möbius
function of the corresponding squarefree integer: for a finite set `S` of distinct primes
with product `m`, the configurations `T ⊆ S` are exactly the divisors of `m`, and

  `P_S(-1, x) = ∑_{d ∣ m} μ(d)·e^{-d x}`.

This identifies the parity value of the abstract gas with the genuine finite Möbius–Laplace
current, so every statement proved about the parity point is a statement about Möbius sums.
-/

namespace RHTower.GibbsGas

open ArithmeticFunction

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes {T : Finset ℕ} (h : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine (Nat.squarefree_mul ?_).mpr
      ⟨(h a (Finset.mem_insert_self a s)).squarefree,
        ih (fun p hp => h p (Finset.mem_insert_of_mem hp))⟩
    refine Nat.Coprime.prod_right (fun i hi => ?_)
    exact (Nat.coprime_primes (h a (Finset.mem_insert_self a s))
      (h i (Finset.mem_insert_of_mem hi))).mpr (by rintro rfl; exact ha hi)

/-- A product of distinct primes has exactly `|T|` prime factors with multiplicity. -/
theorem cardFactors_prod_primes {T : Finset ℕ} (h : ∀ p ∈ T, p.Prime) :
    cardFactors (∏ p ∈ T, p) = T.card := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hprime := h a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hne : (∏ p ∈ s, p) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      exact (hs p hp).pos.ne'
    rw [Finset.prod_insert ha, cardFactors_mul hprime.pos.ne' hne,
      cardFactors_apply_prime hprime, ih hs, Finset.card_insert_of_notMem ha]
    omega

/-- **The alternating sign is the Möbius function.** -/
theorem moebius_prod_primes {T : Finset ℕ} (h : ∀ p ∈ T, p.Prime) :
    (moebius (∏ p ∈ T, p) : ℤ) = (-1) ^ T.card := by
  rw [moebius_apply_of_squarefree (squarefree_prod_primes h), cardFactors_prod_primes h]

/-- The gas at the parity point, written with Möbius weights over configurations. -/
theorem gibbs_parity_eq_moebius_powerset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x : ℝ) :
    gibbsDiag S x (-1)
      = ∑ T ∈ S.powerset,
          ((moebius (∏ p ∈ T, p) : ℤ) : ℝ) * Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) := by
  rw [gibbsDiag]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_powerset] at hT
  rw [moebius_prod_primes (fun p hp => hS p (hT hp))]
  push_cast
  ring

/-- **The gas at the parity point is the Möbius–Laplace current of `m = ∏ S`.** -/
theorem gibbs_parity_eq_moebius_divisors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x : ℝ) :
    gibbsDiag S x (-1)
      = ∑ d ∈ (∏ p ∈ S, p).divisors,
          ((moebius d : ℤ) : ℝ) * Real.exp (-(x * (d : ℝ))) := by
  classical
  have hm : Squarefree (∏ p ∈ S, p) := squarefree_prod_primes hS
  have hm0 : (∏ p ∈ S, p) ≠ 0 := hm.ne_zero
  rw [gibbs_parity_eq_moebius_powerset S hS x]
  refine Finset.sum_nbij' (fun T => ∏ p ∈ T, p) (fun d => d.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Nat.mem_divisors]
    exact ⟨Finset.prod_dvd_prod_of_subset _ _ _ hT, hm0⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Finset.mem_powerset]
    intro p hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hpm : p ∣ ∏ q ∈ S, q := hpd.trans hd.1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : p ∈ (∏ q ∈ S, q).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hpm, hm0⟩
    rwa [Nat.primeFactors_prod hS] at this
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact Nat.primeFactors_prod (fun p hp => hS p (hT hp))
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hd.1)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    congr 1
    push_cast
    rfl

end RHTower.GibbsGas
