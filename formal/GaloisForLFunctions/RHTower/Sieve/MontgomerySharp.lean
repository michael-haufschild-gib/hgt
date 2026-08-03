import GaloisForLFunctions.RHTower.Sieve.FareySharpSet

/-!
# Montgomery's sieve inequality with the sharp constant

At a prime denominator the Farey fibre already consists of proper fractions — a numerator coprime to
a prime and at most it is strictly less than it — so restricting to the proper Farey set costs
nothing at primes.  Feeding the sharp large sieve into the argument of `MontgomeryInequality.lean`
therefore replaces its constant without touching the combinatorial half:

`|A| ∑_{p ∈ P} (p - c_p)/c_p ≤ Q² + 4πN`,

the classical `N + Q²` in place of `N + Q²(1 + log(Q²/2+1))`.
-/

namespace RHTower.Sieve

open Finset

/-- At a prime denominator the Farey fibre is already proper. -/
theorem properFareySet_fibre_prime {p : ℕ} (hp : p.Prime) {Q : ℕ} :
    (properFareySet Q).filter (fun x => x.2 = p)
      = (fareySet Q).filter (fun x => x.2 = p) := by
  ext x
  simp only [Finset.mem_filter, mem_properFareySet]
  constructor
  · rintro ⟨⟨hx, _⟩, hx2⟩
    exact ⟨hx, hx2⟩
  · rintro ⟨hx, hx2⟩
    refine ⟨⟨hx, ?_⟩, hx2⟩
    obtain ⟨_, _, hle, hcop⟩ := mem_fareySet.mp hx
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at hcop
      have hone : x.2 = 1 := by
        have hg := hcop
        rwa [Nat.Coprime, Nat.gcd_self] at hg
      rw [hx2] at hone
      exact hp.one_lt.ne' hone

/-- **Montgomery's sieve inequality with the sharp constant.** -/
theorem montgomery_sieve_sharp (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)
      ≤ (Q : ℝ) ^ 2 + 4 * Real.pi * (N : ℝ) := by
  classical
  have hlow : ∀ p ∈ P,
      (A.card : ℝ) ^ 2
          * (((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ))
        ≤ ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
            ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ 2 := by
    intro p hp
    obtain ⟨hprime, hpQ⟩ := hP p hp
    have hc : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    have hmont := occupied_mul_sum_nonzero_ge hprime.pos A
    rw [← sum_fareySet_fibre_eq hprime hpQ A, ← properFareySet_fibre_prime hprime (Q := Q)] at hmont
    rw [mul_div_assoc', div_le_iff₀ hc]
    linarith [hmont, mul_comm ((occupiedClasses p A).card : ℝ)
      (∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ 2)]
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint
      (fun p => (properFareySet Q).filter (fun x => x.2 = p)) := by
    intro p _ p' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have hsub : P.biUnion (fun p => (properFareySet Q).filter (fun x => x.2 = p))
      ⊆ properFareySet Q := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨p, _, hxp⟩ := hx
    exact (Finset.mem_filter.mp hxp).1
  have hfibres : ∑ p ∈ P, ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ 2
      ≤ ∑ x ∈ properFareySet Q,
          ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ 2 := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hbig := largeSieve_set_properFarey N hN hQ A hA
  have hcardpos : (0 : ℝ) < (A.card : ℝ) := by
    have := Finset.card_pos.mpr hAne
    exact_mod_cast this
  have hchain : (A.card : ℝ) ^ 2 * ∑ p ∈ P,
      ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + 4 * Real.pi * (N : ℝ)) * (A.card : ℝ) := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hlow) (le_trans hfibres hbig)
  refine le_of_mul_le_mul_right ?_ hcardpos
  calc ((A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ))
        * (A.card : ℝ)
      = (A.card : ℝ) ^ 2 * ∑ p ∈ P,
          ((p : ℝ) - ((occupiedClasses p A).card : ℝ))
            / ((occupiedClasses p A).card : ℝ) := by ring
    _ ≤ ((Q : ℝ) ^ 2 + 4 * Real.pi * (N : ℝ)) * (A.card : ℝ) := hchain

end RHTower.Sieve
