import GaloisForLFunctions.RHTower.Sieve.PrimeFibre

/-!
# Montgomery's sieve inequality

The two halves finally meet.  For a set `A ⊆ [0, N)` and a family `P` of primes at most `Q`, the
lower bound of `MontgomerySieve.lean` at each `p ∈ P` and the large sieve of
`IndicatorExpSum.lean` over the whole Farey set of order `Q` give

`|A| ∑_{p ∈ P} (p - c_p) / c_p ≤ N + Q²(1 + log(Q²/2 + 1))`,

where `c_p` is the number of residue classes modulo `p` that `A` meets.  A set that omits many
classes modulo many primes is therefore small.

The fibres of the Farey set above distinct primes are disjoint, so the per-prime lower bounds add
without loss; that disjointness is the only global input.
-/

namespace RHTower.Sieve

open Finset

/-- A nonempty set meets at least one residue class. -/
theorem occupiedClasses_card_pos {p : ℕ} (hp : 0 < p) {A : Finset ℕ} (hA : A.Nonempty) :
    0 < (occupiedClasses p A).card := by
  classical
  obtain ⟨n, hn⟩ := hA
  have hmem : n % p ∈ occupiedClasses p A := by
    rw [occupiedClasses, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    have hn' : n ∈ A.filter (fun m => m % p = n % p) := Finset.mem_filter.mpr ⟨hn, rfl⟩
    have hcard : 0 < (A.filter (fun m => m % p = n % p)).card := Finset.card_pos.mpr ⟨n, hn'⟩
    simp only [residueCount]
    omega
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- **Montgomery's sieve inequality.** -/
theorem montgomery_sieve (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hAne : A.Nonempty)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)
      ≤ (N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1)) := by
  classical
  -- each prime contributes at least its deficiency
  have hlow : ∀ p ∈ P,
      (A.card : ℝ) ^ (2 : ℕ)
          * (((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ))
        ≤ ∑ x ∈ (fareySet Q).filter (fun x => x.2 = p),
            ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    intro p hp
    obtain ⟨hprime, hpQ⟩ := hP p hp
    have hc : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    have hmont := occupied_mul_sum_nonzero_ge hprime.pos A
    rw [← sum_fareySet_fibre_eq hprime hpQ A] at hmont
    rw [mul_div_assoc', div_le_iff₀ hc]
    linarith [hmont, mul_comm ((occupiedClasses p A).card : ℝ)
      (∑ x ∈ (fareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ))]
  -- the fibres above distinct primes are disjoint pieces of the Farey set
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint
      (fun p => (fareySet Q).filter (fun x => x.2 = p)) := by
    intro p _ p' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have hsub : P.biUnion (fun p => (fareySet Q).filter (fun x => x.2 = p)) ⊆ fareySet Q := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨p, _, hxp⟩ := hx
    exact (Finset.mem_filter.mp hxp).1
  have hfibres : ∑ p ∈ P, ∑ x ∈ (fareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ)
      ≤ ∑ x ∈ fareySet Q, ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hbig := largeSieve_set_fareySet N hQ A hA
  -- assemble and divide by the cardinality
  have hcardpos : (0 : ℝ) < (A.card : ℝ) := by
    have := Finset.card_pos.mpr hAne
    exact_mod_cast this
  have hchain : (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
      ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1))) * (A.card : ℝ) := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hlow) (le_trans hfibres hbig)
  refine le_of_mul_le_mul_right ?_ hcardpos
  calc ((A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ))
        * (A.card : ℝ)
      = (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
          ((p : ℝ) - ((occupiedClasses p A).card : ℝ))
            / ((occupiedClasses p A).card : ℝ) := by ring
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1))) * (A.card : ℝ) :=
        hchain

end RHTower.Sieve
