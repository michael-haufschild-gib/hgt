import GaloisForLFunctions.PrimeTorusTheory.NonAlignmentAtEveryLargeHeight

/-!
# The orbit avoids the torsion points of the torus

`exists_not_aligned_of_large` speaks of the corner `+1`. Multiplying the height carries every torsion point to `+1`: if `t log p/2π`
is within `ε` of `(1/m)ℤ` then `mt log p/2π` is within `mε` of `ℤ`. So at every large height some prime stays away from every
`m`-th root of unity; `m = 2` is the corner `−1`.

* `exists_prime_not_aligned_of_large`: at large `|t|`, with `L = log |t|`, `ℓ = log L`, some prime `p` with
  `log p ≤ 50 √L ℓ^{3/2}` has `t log p/2π` at distance more than `√ℓ/(5 L^{3/2})` from the integers.
* `exists_prime_not_near_torsion`: at large `m|t|` the same holds for `mt`, so `t log p/2π` is at distance more than
  `√ℓ/(5 m L^{3/2})` from `(1/m)ℤ`, with `L = log(m|t|)`, `ℓ = log L`.

The proof uses all integers in short intervals, hence all small primes; the weight `p^{-1/2}` is out of reach of this argument.
-/

open Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- **Non-alignment for primes at every large height.** -/
theorem exists_prime_not_aligned_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∃ p : ℕ, p.Prime ∧
        Real.log p ≤ 50 * √(Real.log |t|) * (Real.log (Real.log |t|) * √(Real.log (Real.log |t|))) ∧
        ∀ j : ℤ, √(Real.log (Real.log |t|)) / (5 * Real.log |t| * √(Real.log |t|)) <
          |t * Real.log p / (2 * π) - j| := by
  obtain ⟨T₁, hT₁, h⟩ := exists_not_aligned_of_large
  refine ⟨max T₁ (Real.exp (Real.exp 1)), lt_of_lt_of_le hT₁ (le_max_left _ _), fun t ht => ?_⟩
  obtain ⟨n, hn1, hnlog, hn⟩ := h t ((le_max_left _ _).trans ht)
  have hexp : Real.exp (Real.exp 1) ≤ |t| := (le_max_right _ _).trans ht
  have hpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hL1 : Real.exp 1 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le hpos]
    exact hexp
  set L := Real.log |t| with hL
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL1
  have hℓ1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hLpos]
    exact hL1
  set ℓ := Real.log L with hℓ
  have hℓpos : 0 < ℓ := by linarith
  set r := √L with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hLpos
  have hrsq : r * r = L := Real.mul_self_sqrt hLpos.le
  set w := √ℓ with hw
  have hwpos : 0 < w := Real.sqrt_pos.mpr hℓpos
  have hwsq : w * w = ℓ := Real.mul_self_sqrt hℓpos.le
  set ε : ℝ := w / (5 * L * r) with hε
  have hε0 : 0 ≤ ε := by positivity
  by_contra hcon
  push Not at hcon
  have hal : ∀ p : ℕ, p.Prime → p ≤ n → ∃ j : ℤ, |t * Real.log p / (2 * π) - j| ≤ ε := by
    intro p hp hpn
    have hplog : Real.log p ≤ 50 * r * (ℓ * w) := by
      refine le_trans (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpn)) hnlog
    exact hcon p hp hplog
  obtain ⟨j, hj⟩ := aligned_of_primes hε0 hal n hn1 le_rfl
  have hn2 := hn j
  have hlog2 : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlogp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hlogp]
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hbound : (Nat.log 2 n : ℝ) * ε ≤ 16 * ℓ ^ 2 / L := by
    have hlog2' : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hnlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h1 : (Nat.log 2 n : ℝ) ≤ 3 / 2 * (50 * r * (ℓ * w)) := by
      refine hlog2.trans ?_
      calc Real.log n / Real.log 2 ≤ Real.log n / (2 / 3) :=
            div_le_div_of_nonneg_left hnlog0 (by norm_num) hlog2'
        _ = 3 / 2 * Real.log n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hnlog (by norm_num)
    have e : 3 / 2 * (50 * r * (ℓ * w)) * ε = 15 * (ℓ * (w * w)) / L := by
      rw [hε]
      field_simp
      ring
    have h3 : 15 * (ℓ * (w * w)) / L ≤ 16 * ℓ ^ 2 / L := by
      rw [hwsq]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      nlinarith [sq_nonneg ℓ]
    calc (Nat.log 2 n : ℝ) * ε ≤ 3 / 2 * (50 * r * (ℓ * w)) * ε :=
          mul_le_mul_of_nonneg_right h1 hε0
      _ = _ := e
      _ ≤ _ := h3
  linarith

/-- **The orbit stays away from every torsion point.** The angle `t log p/2π` of some prime is far from `(1/m)ℤ`: apply the
non-alignment at height `mt`. -/
theorem exists_prime_not_near_torsion :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (m : ℕ) (t : ℝ), 1 ≤ m → T₀ ≤ (m : ℝ) * |t| →
      ∃ p : ℕ, p.Prime ∧
        Real.log p ≤ 50 * √(Real.log ((m : ℝ) * |t|)) *
          (Real.log (Real.log ((m : ℝ) * |t|)) * √(Real.log (Real.log ((m : ℝ) * |t|)))) ∧
        ∀ a : ℤ,
          √(Real.log (Real.log ((m : ℝ) * |t|))) /
              (5 * Real.log ((m : ℝ) * |t|) * √(Real.log ((m : ℝ) * |t|))) / (m : ℝ) <
            |t * Real.log p / (2 * π) - (a : ℝ) / (m : ℝ)| := by
  obtain ⟨T₀, hT₀, h⟩ := exists_prime_not_aligned_of_large
  refine ⟨T₀, hT₀, fun m t hm ht => ?_⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have habs : |(m : ℝ) * t| = (m : ℝ) * |t| := by rw [abs_mul, abs_of_pos hmpos]
  obtain ⟨p, hp, hplog, hpal⟩ := h ((m : ℝ) * t) (by rw [habs]; exact ht)
  rw [habs] at hplog hpal
  refine ⟨p, hp, hplog, fun a => ?_⟩
  have h1 := hpal a
  have e : (m : ℝ) * t * Real.log p / (2 * π) - (a : ℝ) =
      (m : ℝ) * (t * Real.log p / (2 * π) - (a : ℝ) / (m : ℝ)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hmpos] at h1
  rw [div_lt_iff₀' hmpos]
  exact h1

end

end GaloisForLFunctions.PrimeTorusTheory
