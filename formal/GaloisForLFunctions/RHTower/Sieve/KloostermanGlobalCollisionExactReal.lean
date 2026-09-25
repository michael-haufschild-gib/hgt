import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionOrientation

/-!
# Exact real-source global Kloosterman collision energy

For pairwise-coprime positive clocks, every cross-frequency fibre is precisely its
reverse-neg orientation pair. Conjugation-fixed weights and source coefficients give
the same coefficient to both orientations. The finite collision energy is therefore
exactly twice the sum of squared tuple coefficients, hence exactly a separable
positive sum of local unit-Fourier energies. No cross-modulus spectral cancellation
is hidden in this collision carrier for real source data.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem exact_two_fiber_energy
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ν : α → β) (flip : α → α) (a : α → ℂ)
    (hν : ∀ p, ν (flip p) = ν p)
    (hne : ∀ p, flip p ≠ p)
    (ha : ∀ p, a (flip p) = a p)
    (hcard : ∀ p, (Finset.univ.filter fun u : α => ν p = ν u).card = 2) :
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) =
      2 * ∑ p : α, Complex.normSq (a p) := by
  classical
  have hpoint : ∀ z : β,
      Complex.normSq (∑ p : α, if ν p = z then a p else 0) =
        2 * ∑ p : α, if ν p = z then Complex.normSq (a p) else 0 := by
    intro z
    let S : Finset α := Finset.univ.filter fun p => ν p = z
    by_cases hS : S.Nonempty
    · obtain ⟨p, hp⟩ := hS
      have hpz : ν p = z := (Finset.mem_filter.mp hp).2
      have hfpz : ν (flip p) = z := (hν p).trans hpz
      have hmemflip : flip p ∈ S := by simp [S, hfpz]
      have hcardS : S.card = 2 := by
        have hfilter : (Finset.univ.filter fun u : α => ν p = ν u) = S := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
          rw [hpz]
          exact eq_comm
        rw [← hfilter]
        exact hcard p
      have hpaircard : ({p, flip p} : Finset α).card = 2 :=
        Finset.card_pair ((hne p).symm)
      have hsub : ({p, flip p} : Finset α) ⊆ S := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hp
        · exact hmemflip
      have hSeq : S = {p, flip p} := by
        symm
        apply Finset.eq_of_subset_of_card_le hsub
        omega
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      change Complex.normSq (∑ u ∈ S, a u) =
        2 * ∑ u ∈ S, Complex.normSq (a u)
      rw [hSeq, Finset.sum_pair ((hne p).symm), Finset.sum_pair ((hne p).symm), ha]
      rw [← two_mul, Complex.normSq_mul]
      norm_num; ring
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      change Complex.normSq (∑ u ∈ S, a u) =
        2 * ∑ u ∈ S, Complex.normSq (a u)
      simp [hEmpty]
  calc
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) =
        ∑ z : β, 2 * ∑ p : α,
          if ν p = z then Complex.normSq (a p) else 0 :=
      Finset.sum_congr rfl (fun z _ => hpoint z)
    _ = 2 * ∑ p : α, Complex.normSq (a p) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Fintype.sum_congr
      intro p
      simp

/-- With real source data, every forced orientation pair adds constructively. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_eq_two_crossTuple_of_real
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (hw : ∀ q, star (w q) = w q)
    (hb : ∀ n ∈ B, star (b n) = b n) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b =
      2 * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p) := by
  unfold kloostermanGlobalFrequencyCollisionEnergy
  simp_rw [kloostermanGlobalFrequencyCoefficient_eq_crossTupleSum, Complex.sq_norm]
  exact exact_two_fiber_energy
    (kloostermanLiteralCrossTupleFrequency Q)
    (kloostermanGlobalCrossTupleReverseNeg)
    (kloostermanGlobalCrossTupleCoefficient Q w B b)
    (kloostermanLiteralCrossTupleFrequency_reverseNeg Q)
    (kloostermanGlobalCrossTupleReverseNeg_ne)
    (kloostermanGlobalCrossTupleCoefficient_reverseNeg_eq_of_star_fixed Q w B b hw hb)
    (card_filter_kloostermanLiteralCrossTupleFrequency_eq_two Q hpair hpos)

theorem kloostermanGlobalFrequencyCollisionEnergy_eq_localFourierProducts_of_real
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (hw : ∀ q, star (w q) = w q)
    (hb : ∀ n ∈ B, star (b n) = b n) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b =
      2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q) * Complex.normSq (w r)) *
          (∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq (kloostermanSourceFourier (q + 1) B b x)) *
          ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (kloostermanSourceFourier (r + 1) B b y) := by
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_two_crossTuple_of_real
    Q hpair hpos w B b hw hb,
    sum_normSq_kloostermanGlobalCrossTupleCoefficient_eq]

/-- The source-faithful prime-clock family needs no external coprimality or reality premise. -/
theorem kloostermanPrimeGlobalCollisionEnergy_eq_localFourierProducts
    (P : Finset Nat.Primes) (w b : ℕ → ℝ) (B : Finset ℕ) :
    kloostermanGlobalFrequencyCollisionEnergy
        (kloostermanPrimeIndexSet (P.image Subtype.val))
        (fun q => (w q : ℂ)) B (fun n => (b n : ℂ)) =
      2 * ∑ q ∈ kloostermanPrimeIndexSet (P.image Subtype.val),
        ∑ r ∈ (kloostermanPrimeIndexSet (P.image Subtype.val)).erase q,
          (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
            (∑ x : (ZMod (q + 1))ˣ,
              Complex.normSq
                (kloostermanSourceFourier (q + 1) B (fun n => (b n : ℂ)) x)) *
            ∑ y : (ZMod (r + 1))ˣ,
              Complex.normSq
                (kloostermanSourceFourier (r + 1) B (fun n => (b n : ℂ)) y) := by
  have hprime : ∀ p ∈ P.image Subtype.val, p.Prime := by
    intro p hp
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hp
    exact p.property
  exact kloostermanGlobalFrequencyCollisionEnergy_eq_localFourierProducts_of_real
    (kloostermanPrimeIndexSet (P.image Subtype.val))
    (kloostermanPrimeIndexSet_pairwise_coprime _ hprime)
    (kloostermanPrimeIndexSet_pos _ hprime)
    (fun q => (w q : ℂ)) B (fun n => (b n : ℂ))
    (by intro q; simp) (by intro n hn; simp)

end
end RHTower.Sieve
