import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerLayerSupport

/-!
# Future-prime support of Euler-deletion reverse tails

Every nonzero Möbius-residue summand surviving in a chronological history layer
contains a prime not yet represented by that layer's clock. Thus the EDQ
covariance problem has no old-prime-only tail contribution.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction

namespace RHTower.DeletionResidueMartingale

attribute [local instance] Classical.propDecidable

/-- A residue already resolved by the lower chronological clock is invisible to its next
history layer. -/
theorem historyLayer_residueVec_eq_zero_of_dvd_clock
    (l d : ℕ) (hd : d ∣ clock l) :
    historyLayer l (residueVec d) = 0 :=
  historyLayer_apply_eq_zero_of_mem l (residueVec d) (residueVec_mem_of_dvd hd)

/-- A nonzero Möbius residue that survives a history layer has a genuinely future prime factor.
This is the exact arithmetic support condition for every active reverse-tail term. -/
theorem exists_future_prime_of_moebius_ne_zero_and_historyLayer_residueVec_ne_zero
    {l d : ℕ} (hmu : moebius d ≠ 0)
    (hlayer : historyLayer l (residueVec d) ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ l < p := by
  have hsq : Squarefree d := moebius_ne_zero_iff_squarefree.mp hmu
  have hnot : ¬ d ∣ clock l := by
    intro hd
    exact hlayer (historyLayer_residueVec_eq_zero_of_dvd_clock l d hd)
  obtain ⟨q, hqpow, hqd, hqgt⟩ :=
    exists_primePow_dvd_of_not_dvd_clock hsq.ne_zero hnot
  have hqsq : Squarefree q := hsq.squarefree_of_dvd hqd
  exact ⟨q, Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hqsq, hqpow⟩, hqd, hqgt⟩

/-- Every nonzero scalar summand of the literal EDQ reverse tail carries a prime strictly beyond
the lower history clock. -/
theorem exists_future_prime_of_nonzero_historyLayer_moebius_term
    {l d : ℕ}
    (hterm : ((moebius d : ℤ) : ℝ) • historyLayer l (residueVec d) ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ l < p := by
  have hmuR : ((moebius d : ℤ) : ℝ) ≠ 0 := by
    intro hzero
    apply hterm
    rw [hzero, zero_smul]
  have hmu : moebius d ≠ 0 := by
    exact_mod_cast hmuR
  have hlayer : historyLayer l (residueVec d) ≠ 0 := by
    intro hzero
    apply hterm
    rw [hzero, smul_zero]
  exact exists_future_prime_of_moebius_ne_zero_and_historyLayer_residueVec_ne_zero
    hmu hlayer

/-- The complete reverse tail can be filtered exactly to moduli not already dividing the lower
clock. This removes all old-prime-only terms before any square or estimate is formed. -/
theorem historyLayer_predictableDrift_eq_reverse_tail_filter_not_dvd_clock
    (l N : ℕ) :
    historyLayer l (predictableDrift N) =
      ∑ i ∈ (range N).filter (fun i => l < i ∧ ¬ (i + 1 ∣ clock l)),
        ((moebius (i + 1) : ℤ) : ℝ) • historyLayer l (residueVec (i + 1)) := by
  rw [historyLayer_predictableDrift_eq_reverse_tail, sum_filter]
  apply sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · by_cases hd : i + 1 ∣ clock l
    · have hinactive : ¬ (l < i ∧ ¬ (i + 1 ∣ clock l)) := fun h => h.2 hd
      rw [if_pos hli, if_neg hinactive,
        historyLayer_residueVec_eq_zero_of_dvd_clock l (i + 1) hd, smul_zero]
    · rw [if_pos hli, if_pos ⟨hli, hd⟩]
  · rw [if_neg hli, if_neg (not_and_of_not_left _ hli)]

/-- Prime-frontier form of the complete reverse tail. Before any quadratic estimate, every
surviving term is indexed by a squarefree modulus with a prime factor strictly newer than the
layer. All old-prime-only composite moduli cancel exactly in the history projection. -/
theorem historyLayer_predictableDrift_eq_reverse_tail_filter_future_prime
    (l N : ℕ) :
    historyLayer l (predictableDrift N) =
      ∑ i ∈ (range N).filter (fun i => l < i ∧
        ∃ p : ℕ, p.Prime ∧ p ∣ i + 1 ∧ l < p),
        ((moebius (i + 1) : ℤ) : ℝ) • historyLayer l (residueVec (i + 1)) := by
  classical
  rw [historyLayer_predictableDrift_eq_reverse_tail, sum_filter]
  apply sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · by_cases hfuture : ∃ p : ℕ, p.Prime ∧ p ∣ i + 1 ∧ l < p
    · rw [if_pos hli, if_pos ⟨hli, hfuture⟩]
    · have hzero : ((moebius (i + 1 : ℕ) : ℤ) : ℝ) •
          historyLayer l (residueVec (i + 1)) = 0 := by
        by_contra hnonzero
        exact hfuture
          (exists_future_prime_of_nonzero_historyLayer_moebius_term hnonzero)
      have hinactive : ¬ (l < i ∧ ∃ p : ℕ, p.Prime ∧ p ∣ i + 1 ∧ l < p) :=
        fun h => hfuture h.2
      rw [if_pos hli, if_neg hinactive, hzero]
  · rw [if_neg hli, if_neg (not_and_of_not_left _ hli)]

/-- A modulus at most `N` whose divisor lies beyond `l` equals that divisor once `l` lies in
the upper half of the cutoff. -/
theorem eq_of_le_two_mul_layer_of_dvd_of_gt
    {l N d p : ℕ} (hN : N ≤ 2 * l) (hdN : d ≤ N) (hdpos : 0 < d)
    (hpd : p ∣ d) (hlp : l < p) :
    d = p := by
  obtain ⟨k, hdk⟩ := hpd
  have hkpos : 0 < k := by
    by_contra hkzero
    have hkzero' : k = 0 := Nat.eq_zero_of_not_pos hkzero
    simp [hdk, hkzero'] at hdpos
  by_cases hk : k = 1
  · rw [hdk, hk, mul_one]
  · have htwo : 2 ≤ k := by omega
    have hmul : p * 2 ≤ p * k := Nat.mul_le_mul_left p htwo
    have hlt : p * k < p * 2 := by
      calc
        p * k = d := hdk.symm
        _ ≤ N := hdN
        _ ≤ 2 * l := hN
        _ < 2 * p := (Nat.mul_lt_mul_left Nat.two_pos).mpr hlp
        _ = p * 2 := Nat.mul_comm _ _
    exact (not_lt_of_ge hmul hlt).elim

/-- In an upper-half layer, every nonzero literal Möbius tail term is indexed by a prime. -/
theorem moebius_historyLayer_term_eq_zero_of_upper_half_of_not_prime
    {l N i : ℕ} (hN : N ≤ 2 * l) (hi : i ∈ range N)
    (hnotprime : ¬ (i + 1).Prime) :
    ((moebius (i + 1) : ℤ) : ℝ) • historyLayer l (residueVec (i + 1)) = 0 := by
  by_contra hterm
  obtain ⟨p, hp, hpd, hlp⟩ :=
    exists_future_prime_of_nonzero_historyLayer_moebius_term hterm
  have hdN : i + 1 ≤ N := Nat.succ_le_iff.mpr (mem_range.mp hi)
  have heq : i + 1 = p := eq_of_le_two_mul_layer_of_dvd_of_gt
    hN hdN (by omega) hpd hlp
  apply hnotprime
  simpa [heq] using hp

/-- Upper-half prime-tail form of EDQ. Once `N ≤ 2l`, all composite reverse-tail moduli vanish
before the layer square; after `p = i + 1`, the full signed tail is over primes in
`(l + 1, N]`. -/
theorem historyLayer_predictableDrift_eq_reverse_tail_filter_prime_of_upper_half
    (l N : ℕ) (hN : N ≤ 2 * l) :
    historyLayer l (predictableDrift N) =
      ∑ i ∈ (range N).filter (fun i => l < i ∧ (i + 1).Prime),
        ((moebius (i + 1) : ℤ) : ℝ) • historyLayer l (residueVec (i + 1)) := by
  rw [historyLayer_predictableDrift_eq_reverse_tail, sum_filter]
  apply sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · by_cases hp : (i + 1).Prime
    · rw [if_pos hli, if_pos ⟨hli, hp⟩]
    · have hzero := moebius_historyLayer_term_eq_zero_of_upper_half_of_not_prime
        hN hi hp
      have hinactive : ¬ (l < i ∧ (i + 1).Prime) := fun h => hp h.2
      rw [if_pos hli, if_neg hinactive, hzero]
  · have hinactive : ¬ (l < i ∧ (i + 1).Prime) := fun h => hli h.1
    rw [if_neg hli, if_neg hinactive]

end RHTower.DeletionResidueMartingale
