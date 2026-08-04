import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# The Möbius inverse-square series with one prime removed

Deleting the multiples of a prime `p` from `∑_{d≥1} μ(d)/d²` multiplies the value by
`(1 - p^{-2})^{-1}`:

    S_p = ∑_{p ∤ d} μ(d)/d² = D / (1 - p^{-2}),   D = 6/π².

The proof is the reindexing `d = p·e` on the deleted part: `μ(pe)` vanishes when `p ∣ e` and equals
`-μ(e)` otherwise, so the deleted part is `-p^{-2}·S_p` and `D = S_p - p^{-2}·S_p`.

This is the analytic content of the card's equation `(8)`; the Euler-factor identity
`(1-1/p)/(1-1/p²) = p/(p+1)` was already available, but the value of the series was not.
-/

namespace RHTower.Sieve

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- The Möbius inverse-square term with the multiples of `p` deleted. -/
noncomputable def coprimeMoebiusTerm (p d : ℕ) : ℝ :=
  if p ∣ d then 0 else ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2

/-- Every term is dominated by the inverse square. -/
theorem norm_coprimeMoebiusTerm_le (p d : ℕ) :
    ‖coprimeMoebiusTerm p d‖ ≤ (1 : ℝ) / (d : ℝ) ^ 2 := by
  rw [coprimeMoebiusTerm]
  by_cases hd : p ∣ d
  · rw [if_pos hd, norm_zero]
    positivity
  · rw [if_neg hd]
    have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      have hc : ((|μ d| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
      rwa [Int.cast_abs] at hc
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hsq]
    exact div_le_div_of_nonneg_right hmu hsq

/-- The deleted series converges absolutely. -/
theorem summable_coprimeMoebiusTerm (p : ℕ) : Summable (coprimeMoebiusTerm p) :=
  Summable.of_norm_bounded (g := fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.2 (by norm_num)) (norm_coprimeMoebiusTerm_le p)

/-- The Möbius inverse-square series with the multiples of `p` deleted. -/
noncomputable def coprimeSquarefreeSum (p : ℕ) : ℝ := ∑' d : ℕ, coprimeMoebiusTerm p d

/-- **Truncation error of the deleted density.** -/
theorem abs_sum_Icc_coprimeMoebius_sub_le {p R : ℕ} (hR : 1 ≤ R) :
    |∑ d ∈ Finset.Icc 1 R, coprimeMoebiusTerm p d - coprimeSquarefreeSum p| ≤ 1 / (R : ℝ) := by
  classical
  set f : ℕ → ℝ := coprimeMoebiusTerm p with hf
  have hsum := summable_coprimeMoebiusTerm p
  have hsplit : ∑ i ∈ Finset.range (R + 1), f i + ∑' n : ℕ, f (n + (R + 1)) = ∑' d : ℕ, f d :=
    hsum.sum_add_tsum_nat_add (R + 1)
  have hins : Finset.range (R + 1) = insert 0 (Finset.Icc 1 R) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : f 0 = 0 := by
    rw [hf, coprimeMoebiusTerm]
    by_cases hp : p ∣ 0
    · rw [if_pos hp]
    · rw [if_neg hp]
      simp
  have hfin : ∑ i ∈ Finset.range (R + 1), f i = ∑ d ∈ Finset.Icc 1 R, f d := by
    rw [hins, Finset.sum_insert (by simp), h0, zero_add]
  have htail : |∑' n : ℕ, f (n + (R + 1))| ≤ 1 / (R : ℝ) := by
    have hbound : ∀ n : ℕ, ‖f (n + (R + 1))‖ ≤ (1 : ℝ) / ((n : ℝ) + R + 1) ^ 2 := by
      intro n
      have hcast : ((n + (R + 1) : ℕ) : ℝ) = (n : ℝ) + R + 1 := by push_cast; ring
      have h := norm_coprimeMoebiusTerm_le p (n + (R + 1))
      rwa [hcast] at h
    have hsummable : Summable (fun n : ℕ => f (n + (R + 1))) :=
      (summable_nat_add_iff (R + 1)).2 hsum
    rw [← Real.norm_eq_abs]
    refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
    · exact hsummable.norm
    · refine le_trans (Summable.tsum_le_tsum hbound hsummable.norm (summable_inv_sq_shift R)) ?_
      exact tsum_inv_sq_shift_le hR
  rw [← hfin, coprimeSquarefreeSum, ← hf, ← hsplit]
  have hcancel : ∑ i ∈ Finset.range (R + 1), f i
      - (∑ i ∈ Finset.range (R + 1), f i + ∑' n : ℕ, f (n + (R + 1)))
      = -(∑' n : ℕ, f (n + (R + 1))) := by ring
  rw [hcancel, abs_neg]
  exact htail

/-- The deleted part is the full term on the multiples of `p`. -/
theorem sub_coprimeMoebiusTerm_eq (p d : ℕ) :
    ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 - coprimeMoebiusTerm p d
      = if p ∣ d then ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 else 0 := by
  rw [coprimeMoebiusTerm]
  by_cases hd : p ∣ d
  · rw [if_pos hd, if_pos hd, sub_zero]
  · rw [if_neg hd, if_neg hd, sub_self]

/-- The Möbius value on a multiple of a prime. -/
theorem moebius_prime_mul {p e : ℕ} (hp : p.Prime) :
    ((μ (p * e) : ℤ) : ℝ)
      = if p ∣ e then 0 else -((μ e : ℤ) : ℝ) := by
  by_cases he : p ∣ e
  · rw [if_pos he]
    obtain ⟨k, rfl⟩ := he
    have hnsf : ¬ Squarefree (p * (p * k)) := by
      intro hsf
      have hu : ¬ IsUnit p := by
        rw [Nat.isUnit_iff]
        exact hp.one_lt.ne'
      exact hu (hsf p ⟨k, by ring⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    norm_num
  · rw [if_neg he]
    have hcop : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).2 he
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring

/-- The reindexed term. -/
theorem term_prime_mul_eq {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (if p ∣ p * e then ((μ (p * e) : ℤ) : ℝ) / ((p * e : ℕ) : ℝ) ^ 2 else 0)
      = -(1 / (p : ℝ) ^ 2) * coprimeMoebiusTerm p e := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [if_pos ⟨e, rfl⟩, coprimeMoebiusTerm, moebius_prime_mul hp]
  by_cases he : p ∣ e
  · rw [if_pos he, if_pos he]
    simp
  · rw [if_neg he, if_neg he]
    push_cast
    field_simp

/-- **The deleted part of the series.** -/
theorem tsum_deleted_eq {p : ℕ} (hp : p.Prime) :
    ∑' d : ℕ, (if p ∣ d then ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 else 0)
      = -(1 / (p : ℝ) ^ 2) * coprimeSquarefreeSum p := by
  classical
  set F : ℕ → ℝ := fun d => if p ∣ d then ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 else 0 with hF
  have hinj : Function.Injective (fun e : ℕ => p * e) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  have hsupp : Function.support F ⊆ Set.range (fun e : ℕ => p * e) := by
    intro d hd
    rw [Function.mem_support, hF] at hd
    by_cases hpd : p ∣ d
    · obtain ⟨k, rfl⟩ := hpd
      exact ⟨k, rfl⟩
    · exact absurd (if_neg hpd) hd
  have hre := hinj.tsum_eq (f := F) hsupp
  rw [← hre]
  have hterm : ∀ e : ℕ, F (p * e) = -(1 / (p : ℝ) ^ 2) * coprimeMoebiusTerm p e := by
    intro e
    rw [hF]
    exact term_prime_mul_eq hp e
  rw [tsum_congr hterm, tsum_mul_left, coprimeSquarefreeSum]

/-- **Card equation (8), analytic form.**  Deleting the multiples of `p` rescales the Möbius
inverse-square series by `(1 - p^{-2})^{-1}`. -/
theorem coprimeSquarefreeSum_mul_eq {p : ℕ} (hp : p.Prime) :
    coprimeSquarefreeSum p * (1 - 1 / (p : ℝ) ^ 2) = squarefreeDensity := by
  have hsub : Summable (fun d : ℕ => ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 - coprimeMoebiusTerm p d) :=
    summable_moebius_div_sq.sub (summable_coprimeMoebiusTerm p)
  have hsplit : ∑' d : ℕ, (((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 - coprimeMoebiusTerm p d)
      = squarefreeDensity - coprimeSquarefreeSum p := by
    rw [squarefreeDensity, coprimeSquarefreeSum]
    exact summable_moebius_div_sq.tsum_sub (summable_coprimeMoebiusTerm p)
  have hcongr : ∑' d : ℕ, (((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 - coprimeMoebiusTerm p d)
      = ∑' d : ℕ, (if p ∣ d then ((μ d : ℤ) : ℝ) / (d : ℝ) ^ 2 else 0) :=
    tsum_congr (sub_coprimeMoebiusTerm_eq p)
  rw [hcongr, tsum_deleted_eq hp] at hsplit
  linarith [hsplit]

end RHTower.Sieve
