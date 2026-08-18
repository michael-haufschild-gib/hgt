import GaloisForLFunctions.RHTower.Sieve.RoughPairSieve
import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# The sieve density of the shifted pair is the true root count

The density used by the shifted-pair sieve is the multiplicative function whose value at a prime is
the number of residues the pair must avoid.  On a squarefree modulus that product **is** the number
of roots of `r(r + d) = 0`, by the Chinese remainder theorem — which the corpus already proves in
`RHTower/ReducedFrequencyMobiusAliasCollapse`.

Identifying the two is what makes the Selberg remainder small: the sieve's expected density is the
actual density of the sifted set, not merely a majorant.
-/

namespace RHTower.Sieve

open Finset

/-- The local root count is the local class count. -/
theorem rootCountTotal_prime_eq (d : ℕ) {p : ℕ} (hp : p.Prime) :
    ((quadraticCongruenceRootCountTotal p (d : ℤ) : ℕ) : ℝ) = pairClassCount d p := by
  rw [quadraticCongruenceRootCountTotal_prime hp, pairClassCount]
  have hiff : ((p : ℤ) ∣ (d : ℤ)) ↔ p ∣ d := Int.natCast_dvd_natCast
  by_cases hd : p ∣ d
  · rw [if_pos (hiff.2 hd), if_pos hd]
    norm_num
  · rw [if_neg (fun hc => hd (hiff.1 hc)), if_neg hd]
    norm_num

/-- **On a squarefree modulus the class-count product is the true root count.** -/
theorem rootCountTotal_eq_pairClassCount_prod {e : ℕ} (hsq : Squarefree e) (d : ℕ) :
    ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ)
      = ∏ p ∈ e.primeFactors, pairClassCount d p := by
  classical
  have he0 : e ≠ 0 := hsq.ne_zero
  have hprod : ∏ p ∈ e.primeFactors, p = e := Nat.prod_primeFactors_of_squarefree hsq
  have hpair : ((e.primeFactors : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hne
  have hnz : ∀ n ∈ e.primeFactors, n ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hstep := quadraticCongruenceRootCountTotal_prod e.primeFactors hpair hnz (d : ℤ)
  rw [hprod] at hstep
  rw [hstep]
  push_cast
  refine Finset.prod_congr rfl fun p hp => ?_
  exact rootCountTotal_prime_eq d (Nat.prime_of_mem_primeFactors hp)

/-- **The sieve density is the root density on squarefree moduli.** -/
theorem pairNu_eq_rootDensity {e : ℕ} (hsq : Squarefree e) (d : ℕ) :
    pairNu d e = ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ) / (e : ℝ) := by
  have he0 : e ≠ 0 := hsq.ne_zero
  rw [rootCountTotal_eq_pairClassCount_prod hsq d]
  simp [pairNu, ArithmeticFunction.prodPrimeFactors_apply he0]

/-! ## The residue description of the root set -/

/-- **The roots of `r(r+d) ≡ 0` are the residues below the modulus satisfying the divisibility.** -/
theorem card_rootResidues_eq {e : ℕ} (he : 0 < e) (d : ℕ) :
    (((Finset.range e).filter (fun r => e ∣ r * (r + d))).card)
      = quadraticCongruenceRootCountTotal e (d : ℤ) := by
  classical
  haveI : NeZero e := ⟨he.ne'⟩
  rw [quadraticCongruenceRootCountTotal_of_ne_zero he.ne', quadraticCongruenceRootCount]
  have hinst : @Fintype.card (quadraticCongruenceRoots e (d : ℤ))
      (quadraticCongruenceRootsFintype e (d : ℤ))
      = (Finset.univ.filter (fun x : ZMod e => x * (x + ((d : ℤ) : ZMod e)) = 0)).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.refl _)
  rw [hinst]
  refine Finset.card_nbij' (fun r => (r : ZMod e)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcast : ((r * (r + d) : ℕ) : ZMod e) = (r : ZMod e) * ((r : ZMod e) + ((d : ℤ) : ZMod e)) := by
      push_cast
      ring
    rw [← hcast]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hr.2
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    have hcast : ((x.val * (x.val + d) : ℕ) : ZMod e)
        = (x.val : ZMod e) * ((x.val : ZMod e) + ((d : ℤ) : ZMod e)) := by
      push_cast
      ring
    rw [hcast, ZMod.natCast_zmod_val]
    exact hx.2
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    exact ZMod.val_cast_of_lt hr.1
  · intro x _
    exact ZMod.natCast_zmod_val x

end RHTower.Sieve
