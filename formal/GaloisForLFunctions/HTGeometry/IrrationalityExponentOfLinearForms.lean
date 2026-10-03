import Mathlib

/-!
# Irrationality exponents from integer linear forms

Let `ξ` be real and let `aₙ, bₙ` be integers with, for all large `n`,

* `c γⁿ ≤ |aₙ ξ + bₙ| ≤ C λⁿ` and `|aₙ| ≤ C Λⁿ`,

where `0 < λ < 1`, `0 < γ ≤ 1 ≤ Λ` and `0 < c ≤ 1 ≤ C`.  Then `ξ` has finite irrationality
exponent: `|ξ − m/q| ≥ c₁ q^{−K}` for an explicit natural `K` and all fractions, hence
`¬ LiouvilleWith p ξ` for every `p > K`.

For a fraction `m/q` take the least `N` with `C λᴺ ≤ 1/(2q)` and `n = n₀ + N`.  The integer
`q bₙ + aₙ m = q(aₙξ + bₙ) − aₙ(qξ − m)` is either nonzero, giving `|qξ − m| ≥ 1/(2|aₙ|)`, or zero,
giving `|ξ − m/q| = |aₙξ + bₙ|/|aₙ|`.  Minimality of `N` gives `λⁿ ≥ λ^{n₀+1}/(2Cq)`, and with
`λᵏ ≤ γ/Λ` both cases yield a power of `q`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry.IrrationalityExponent

/-- **Rational lower bound from linear forms.** -/
theorem exists_abs_sub_div_ge {ξ l L g C c : ℝ} {a b : ℕ → ℤ} {n₀ : ℕ}
    (hl0 : 0 < l) (hl1 : l < 1) (hg0 : 0 < g) (hg1 : g ≤ 1) (hL : 1 ≤ L) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hup : ∀ n ≥ n₀, |(a n : ℝ) * ξ + b n| ≤ C * l ^ n)
    (hlow : ∀ n ≥ n₀, c * g ^ n ≤ |(a n : ℝ) * ξ + b n|)
    (ha : ∀ n ≥ n₀, |(a n : ℝ)| ≤ C * L ^ n) :
    ∃ K : ℕ, ∃ c₁ > 0, ∀ (m : ℤ) (q : ℕ), 1 ≤ q → c₁ / (q : ℝ) ^ K ≤ |ξ - m / q| := by
  -- an integer `k` with `lᵏ ≤ g/L`
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < g / L by positivity) hl1
  have hρ0 : 0 < g / L := by positivity
  have hρ1 : g / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  refine ⟨k + 1, c / (2 * C) * (l ^ (n₀ + 1) / (2 * C)) ^ k, by positivity, ?_⟩
  intro m q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  -- the least `N` with `C lᴺ ≤ 1/(2q)`
  have hex : ∃ N : ℕ, C * l ^ N ≤ 1 / (2 * q) := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (2 * q) / C by positivity) hl1
    refine ⟨N, ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hN
    linarith
  classical
  set N := Nat.find hex with hNdef
  have hN : C * l ^ N ≤ 1 / (2 * q) := Nat.find_spec hex
  have hNlow : l / (2 * C * q) ≤ l ^ N := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, pow_zero, div_le_one (by positivity)]
      nlinarith
    · have hmin := Nat.find_min hex (show N - 1 < N by omega)
      simp only [not_le] at hmin
      have hsplit : l ^ N = l * l ^ (N - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hsplit, div_le_iff₀ (by positivity)]
      have : 1 / (2 * q) < C * l ^ (N - 1) := hmin
      rw [div_lt_iff₀ (by positivity)] at this
      nlinarith
  set n := n₀ + N with hn
  have hnn : n ≥ n₀ := by omega
  have hupn : C * l ^ n ≤ 1 / (2 * q) := by
    have : l ^ n ≤ l ^ N := pow_le_pow_of_le_one hl0.le hl1.le (by omega)
    nlinarith [pow_pos hl0 N]
  have hlown : l ^ (n₀ + 1) / (2 * C * q) ≤ l ^ n := by
    calc l ^ (n₀ + 1) / (2 * C * q) = l ^ n₀ * (l / (2 * C * q)) := by rw [pow_succ]; ring
      _ ≤ l ^ n₀ * l ^ N := mul_le_mul_of_nonneg_left hNlow (by positivity)
      _ = l ^ n := by rw [hn, pow_add]
  -- `(g/L)ⁿ ≥ (lⁿ)ᵏ`
  have hρn : (l ^ n) ^ k ≤ (g / L) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hk.le n
  have hfinal_low : c / (2 * C) * (l ^ (n₀ + 1) / (2 * C)) ^ k / (q : ℝ) ^ (k + 1) ≤
      c / (2 * C) * (g / L) ^ n / q := by
    have h1 : (l ^ (n₀ + 1) / (2 * C)) ^ k / (q : ℝ) ^ k ≤ (l ^ n) ^ k := by
      rw [← div_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      rw [div_div]; exact hlown
    have h2 : (l ^ (n₀ + 1) / (2 * C)) ^ k / (q : ℝ) ^ (k + 1) ≤ (g / L) ^ n / q := by
      rw [show (q : ℝ) ^ (k + 1) = (q : ℝ) ^ k * q from pow_succ _ _, ← div_div]
      exact div_le_div_of_nonneg_right (h1.trans hρn) hqpos.le
    calc c / (2 * C) * (l ^ (n₀ + 1) / (2 * C)) ^ k / (q : ℝ) ^ (k + 1) =
        c / (2 * C) * ((l ^ (n₀ + 1) / (2 * C)) ^ k / (q : ℝ) ^ (k + 1)) := by ring
      _ ≤ c / (2 * C) * ((g / L) ^ n / q) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = c / (2 * C) * (g / L) ^ n / q := by ring
  refine hfinal_low.trans ?_
  have hLn : 0 < L ^ n := by positivity
  have hanle := ha n hnn
  have hlo := hlow n hnn
  have hup' := hup n hnn
  set z : ℤ := (q : ℤ) * b n + a n * m with hz
  have hzR : (z : ℝ) = q * ((a n : ℝ) * ξ + b n) - (a n : ℝ) * (q * ξ - m) := by
    rw [hz]; push_cast; ring
  have hgn : (g / L) ^ n = g ^ n / L ^ n := div_pow g L n
  by_cases hz0 : z = 0
  · -- `|ξ − m/q| = |aₙξ + bₙ|/|aₙ|`
    have hrel : (a n : ℝ) * ξ + b n = (a n : ℝ) * (ξ - m / q) := by
      have : (q : ℝ) * ((a n : ℝ) * ξ + b n) = (a n : ℝ) * (q * ξ - m) := by
        have := hzR; rw [hz0, Int.cast_zero] at this; linarith
      field_simp
      linarith
    have hapos : 0 < |(a n : ℝ)| := by
      rcases eq_or_ne (a n) 0 with h | h
      · exfalso
        rw [hrel, h, Int.cast_zero, zero_mul, abs_zero] at hlo
        have : 0 < c * g ^ n := by positivity
        linarith
      · exact abs_pos.mpr (by exact_mod_cast h)
    have hbound : c * g ^ n ≤ |(a n : ℝ)| * |ξ - m / q| := by rw [← abs_mul, ← hrel]; exact hlo
    have hdiv : c * g ^ n / (C * L ^ n) ≤ |ξ - m / q| := by
      rw [div_le_iff₀ (by positivity)]
      calc c * g ^ n ≤ |(a n : ℝ)| * |ξ - m / q| := hbound
        _ ≤ C * L ^ n * |ξ - m / q| := mul_le_mul_of_nonneg_right hanle (abs_nonneg _)
        _ = |ξ - m / q| * (C * L ^ n) := by ring
    refine le_trans ?_ hdiv
    rw [hgn]
    have hq2 : c / (2 * C) * (g ^ n / L ^ n) / q ≤ c * g ^ n / (C * L ^ n) := by
      rw [div_le_iff₀ hqpos]
      have : c * g ^ n / (C * L ^ n) * q ≥ c * g ^ n / (C * L ^ n) * 1 :=
        mul_le_mul_of_nonneg_left hq1 (by positivity)
      have e : c / (2 * C) * (g ^ n / L ^ n) = (c * g ^ n / (C * L ^ n)) / 2 := by
        field_simp
      rw [e]
      nlinarith [show 0 ≤ c * g ^ n / (C * L ^ n) by positivity]
    exact hq2
  · -- `|z| ≥ 1`
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
      have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
      exact_mod_cast this
    have htri : |(z : ℝ)| ≤ q * |(a n : ℝ) * ξ + b n| + |(a n : ℝ)| * |q * ξ - m| := by
      rw [hzR]
      calc |(q : ℝ) * ((a n : ℝ) * ξ + b n) - (a n : ℝ) * (q * ξ - m)| ≤
          |(q : ℝ) * ((a n : ℝ) * ξ + b n)| + |(a n : ℝ) * (q * ξ - m)| := abs_sub _ _
        _ = q * |(a n : ℝ) * ξ + b n| + |(a n : ℝ)| * |q * ξ - m| := by
          rw [abs_mul, abs_mul, abs_of_pos hqpos]
    have hqfirst : (q : ℝ) * |(a n : ℝ) * ξ + b n| ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (hup'.trans hupn) hqpos.le
      rw [show (q : ℝ) * (1 / (2 * q)) = 1 / 2 by field_simp] at this
      exact this
    have hsec : 1 / 2 ≤ |(a n : ℝ)| * |q * ξ - m| := by linarith
    have hqξ : |(q : ℝ) * ξ - m| = q * |ξ - m / q| := by
      rw [show (q : ℝ) * ξ - m = q * (ξ - m / q) by field_simp, abs_mul, abs_of_pos hqpos]
    rw [hqξ] at hsec
    have hdiv : 1 / (2 * q * (C * L ^ n)) ≤ |ξ - m / q| := by
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) ≤ 2 * (|(a n : ℝ)| * (q * |ξ - m / q|)) := by linarith
        _ ≤ 2 * (C * L ^ n * (q * |ξ - m / q|)) := by
          gcongr
        _ = |ξ - m / q| * (2 * q * (C * L ^ n)) := by ring
    refine le_trans ?_ hdiv
    rw [hgn, div_le_div_iff₀ hqpos (by positivity)]
    have hgle : g ^ n ≤ 1 := pow_le_one₀ hg0.le hg1
    have e : c / (2 * C) * (g ^ n / L ^ n) * (2 * q * (C * L ^ n)) = c * g ^ n * q := by
      field_simp
    rw [e, one_mul]
    exact mul_le_of_le_one_left hqpos.le (mul_le_one₀ hc1 (by positivity) hgle)

/-- **Finite irrationality exponent from linear forms.** -/
theorem exists_not_liouvilleWith {ξ l L g C c : ℝ} {a b : ℕ → ℤ} {n₀ : ℕ}
    (hl0 : 0 < l) (hl1 : l < 1) (hg0 : 0 < g) (hg1 : g ≤ 1) (hL : 1 ≤ L) (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hC : 1 ≤ C)
    (hup : ∀ n ≥ n₀, |(a n : ℝ) * ξ + b n| ≤ C * l ^ n)
    (hlow : ∀ n ≥ n₀, c * g ^ n ≤ |(a n : ℝ) * ξ + b n|)
    (ha : ∀ n ≥ n₀, |(a n : ℝ)| ≤ C * L ^ n) :
    ∃ K : ℕ, ∀ p > (K : ℝ), ¬ LiouvilleWith p ξ := by
  obtain ⟨K, c₁, hc₁, hbound⟩ := exists_abs_sub_div_ge hl0 hl1 hg0 hg1 hL hc0 hc1 hC hup hlow ha
  refine ⟨K, fun p hp hLw => ?_⟩
  set r : ℝ := (K + p) / 2 with hr
  have hKr : (K : ℝ) < r := by rw [hr]; linarith
  have hfreq := hLw.frequently_lt_rpow_neg (show r < p by rw [hr]; linarith)
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((K : ℝ) - r) < c₁ := by
    have h := (tendsto_rpow_neg_atTop (show 0 < r - K by linarith)).comp
      tendsto_natCast_atTop_atTop
    have h' := h.eventually (gt_mem_nhds hc₁)
    refine h'.mono fun n hn => ?_
    simpa [neg_sub] using hn
  obtain ⟨n, ⟨hn, hn1⟩, m, -, hm⟩ :=
    ((hev.and (eventually_ge_atTop 1)).and_frequently hfreq).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlowb := hbound m n hn1
  have h1 : c₁ / (n : ℝ) ^ K < (n : ℝ) ^ (-r) := lt_of_le_of_lt hlowb hm
  rw [div_lt_iff₀ (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hnpos] at h1
  have h2 : (n : ℝ) ^ (-r + K) = (n : ℝ) ^ ((K : ℝ) - r) := by ring_nf
  rw [h2] at h1
  linarith

end GaloisForLFunctions.HTGeometry.IrrationalityExponent
