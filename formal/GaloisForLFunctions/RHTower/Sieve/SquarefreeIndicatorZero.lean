import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicator

/-!
# The divisor sum vanishes at a non-squarefree argument

If `n` is not squarefree, fix a prime `p` with `p² ∣ n`.  On the squarefree `d` with `d² ∣ n` the map

`d ↦ d/p` if `p ∣ d`,  `d ↦ dp` otherwise

is an involution, and it reverses the sign of `μ`.  Hence the sum cancels in pairs:

`∑_{d² ∣ n} μ(d) = 0`.

The step that makes the map well defined is that `d² ∣ n` and `p² ∣ n` with `p ∤ d` give
`d²p² ∣ n` by coprimality — no factorisation of `n` is needed, and the square part of `n` is never
constructed.

With `SquarefreeIndicator` this completes the identity `μ²(n) = ∑_{d² ∣ n} μ(d)`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Restricting the square-divisor sum to squarefree divisors. -/
theorem sum_sq_dvd_eq_sum_squarefree (n : ℕ) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ)
      = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n ∧ Squarefree d),
          ((moebius d : ℤ) : ℝ) := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.1⟩
  · intro d hd hnot
    rw [Finset.mem_filter] at hd hnot
    have hnsf : ¬ Squarefree d := by tauto
    have hz : moebius d = 0 := by
      by_contra hne
      exact hnsf (moebius_ne_zero_iff_squarefree.mp hne)
    rw [hz]
    norm_num

/-- **The divisor sum vanishes at a non-squarefree argument.** -/
theorem sum_moebius_sq_dvd_of_not_squarefree {n : ℕ} (hn : 0 < n) (hsf : ¬ Squarefree n) :
    ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ) = 0 := by
  classical
  obtain ⟨p, hp, hpp⟩ : ∃ p, p.Prime ∧ p * p ∣ n := by
    by_contra hcon
    exact hsf (Nat.squarefree_iff_prime_squarefree.mpr fun q hq hqq => hcon ⟨q, hq, hqq⟩)
  have hp2 : p ^ 2 ∣ n := by rwa [pow_two]
  rw [sum_sq_dvd_eq_sum_squarefree n]
  set S := (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n ∧ Squarefree d) with hS
  have hmem : ∀ d ∈ S, 1 ≤ d ∧ d ≤ n ∧ d ^ 2 ∣ n ∧ Squarefree d := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨hd.1.1, hd.1.2, hd.2.1, hd.2.2⟩
  refine Finset.sum_involution (fun d _ => if p ∣ d then d / p else d * p) ?_ ?_ ?_ ?_
  · -- the two terms cancel
    intro d hd
    obtain ⟨hd1, hdn, hdvd, hdsf⟩ := hmem d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
      obtain ⟨c, rfl⟩ := hpd
      have hpc : ¬ p ∣ c := by
        intro hc
        obtain ⟨b, rfl⟩ := hc
        exact absurd (hdsf p ⟨b, by ring⟩) (by simpa using hp.one_lt.ne')
      have hdiv : p * c / p = c := by
        rw [Nat.mul_div_cancel_left c hp.pos]
      rw [hdiv]
      have hcop : Nat.Coprime p c := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpc
      have hmul : moebius (p * c) = moebius p * moebius c :=
        isMultiplicative_moebius.map_mul_of_coprime hcop
      rw [hmul, moebius_apply_prime hp]
      push_cast
      ring
    · rw [if_neg hpd]
      have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
      have hmul : moebius (d * p) = moebius d * moebius p :=
        isMultiplicative_moebius.map_mul_of_coprime (Nat.Coprime.symm hcop)
      rw [hmul, moebius_apply_prime hp]
      push_cast
      ring
  · -- the involution moves every point with a nonzero term
    intro d hd hne
    obtain ⟨hd1, hdn, hdvd, hdsf⟩ := hmem d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
      intro hcon
      obtain ⟨c, rfl⟩ := hpd
      rw [Nat.mul_div_cancel_left c hp.pos] at hcon
      have hc0 : c ≠ 0 := by rintro rfl; simp at hd1
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      nlinarith [hp.two_le, hc1, hcon]
    · rw [if_neg hpd]
      intro hcon
      have : p = 1 := by
        have hd0 : 0 < d := hd1
        nlinarith [hcon, hd0]
      exact hp.one_lt.ne' this
  · -- the involution lands in the set
    intro d hd
    obtain ⟨hd1, hdn, hdvd, hdsf⟩ := hmem d hd
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
      obtain ⟨c, rfl⟩ := hpd
      rw [Nat.mul_div_cancel_left c hp.pos]
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | hc
        · simp at hd1
        · exact hc
      have hcdvd : c ^ 2 ∣ n := dvd_trans (by exact ⟨p ^ 2, by ring⟩) hdvd
      exact ⟨⟨hc1, le_trans (Nat.le_mul_of_pos_left c hp.pos) hdn⟩, hcdvd,
        hdsf.squarefree_of_dvd ⟨p, by ring⟩⟩
    · rw [if_neg hpd]
      have hcop : Nat.Coprime (d ^ 2) (p ^ 2) :=
        Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
      have hdp : (d * p) ^ 2 ∣ n := by
        have : (d * p) ^ 2 = d ^ 2 * p ^ 2 := by ring
        rw [this]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd hp2
      have hdp1 : 1 ≤ d * p := Nat.mul_pos hd1 hp.pos
      have hdpn : d * p ≤ n := by
        have h1 : d * p ≤ (d * p) ^ 2 := by nlinarith [hdp1]
        exact le_trans h1 (Nat.le_of_dvd hn hdp)
      refine ⟨⟨hdp1, hdpn⟩, hdp, ?_⟩
      exact (Nat.squarefree_mul_iff.mpr
        ⟨((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm, hdsf, hp.squarefree⟩)
  · -- the map is an involution
    intro d hd
    obtain ⟨hd1, hdn, hdvd, hdsf⟩ := hmem d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
      obtain ⟨c, rfl⟩ := hpd
      rw [Nat.mul_div_cancel_left c hp.pos]
      have hpc : ¬ p ∣ c := by
        intro hc
        obtain ⟨b, rfl⟩ := hc
        exact absurd (hdsf p ⟨b, by ring⟩) (by simpa using hp.one_lt.ne')
      rw [if_neg hpc, Nat.mul_comm]
    · rw [if_neg hpd, if_pos ⟨d, Nat.mul_comm d p⟩, Nat.mul_div_cancel _ hp.pos]

/-- **Card equation (7)**: `μ²(n) = ∑_{d² ∣ n} μ(d)`. -/
theorem moebius_sq_eq_sum_sq_dvd {n : ℕ} (hn : 0 < n) :
    ((moebius n : ℤ) : ℝ) ^ 2
      = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n), ((moebius d : ℤ) : ℝ) := by
  classical
  by_cases hsf : Squarefree n
  · rw [moebius_sq_eq_indicator, if_pos hsf, sum_moebius_sq_dvd_of_squarefree hn hsf]
  · rw [moebius_sq_eq_indicator, if_neg hsf, sum_moebius_sq_dvd_of_not_squarefree hn hsf]

end RHTower.Sieve
