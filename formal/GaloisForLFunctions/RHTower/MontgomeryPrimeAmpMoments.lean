import GaloisForLFunctions.RHTower.MontgomeryPrimeSideMeanSquare
import GaloisForLFunctions.RHTower.VonMangoldtSquarePowerMoments

/-!
# The prime-side energies `Σ d_n²` and `Σ n d_n²`

For the amplitudes `d_n` of the prime side of Montgomery's lemma,

`Σ_n d_n² = (1/x) Σ_{n≤x} Λ(n)² n + x³ Σ_{n>x} Λ(n)²/n³ ~ x log x`,
`Σ_n n d_n² = (1/x) Σ_{n≤x} Λ(n)² n² + x³ Σ_{n>x} Λ(n)²/n² ≤ 3 x² log x` eventually.

Both follow from the `Λ(n)²` power moments of the prime number theorem.
-/

open Filter Topology Set
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The squared amplitudes -/

theorem primeAmp_sq_eq {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 0 < n) :
    primeAmp x n ^ 2 = if (n : ℝ) ≤ x then vonMangoldt n ^ 2 * n / x
      else vonMangoldt n ^ 2 * x ^ 3 / (n : ℝ) ^ 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hy : 0 < x / n := by positivity
  unfold primeAmp
  split_ifs with h
  · have hsq : ((x / n) ^ (-(1 / 2 : ℝ))) ^ 2 = (x / n) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
    rw [mul_pow, hsq, Real.rpow_neg_one, inv_div]
    ring
  · have hsq : ((x / n) ^ ((3 / 2 : ℝ))) ^ 2 = (x / n) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, show ((3 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = ((3 : ℕ) : ℝ) by
        norm_num, Real.rpow_natCast]
    rw [mul_pow, hsq, div_pow]
    ring

theorem summable_primeAmp_sq_le_part {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ => if (n : ℝ) ≤ x then primeAmp x n ^ 2 else 0) :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
    (fun n => by split_ifs <;> [exact le_rfl; positivity]) (summable_primeAmp_sq hx)

theorem summable_primeAmp_sq_gt_part {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ => if x < (n : ℝ) then primeAmp x n ^ 2 else 0) :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
    (fun n => by split_ifs <;> [exact le_rfl; positivity]) (summable_primeAmp_sq hx)

/-- `Σ_n d_n² = (1/x) Σ_{n≤x} Λ(n)² n + x³ Σ_{n>x} Λ(n)²/n³`. -/
theorem tsum_primeAmp_sq_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, primeAmp x n ^ 2
      = (1 / x) * ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * n
        + x ^ 3 * ∑' n : ℕ, (if x < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 3 else 0) := by
  have hx0 : 0 < x := by linarith
  have hsplit : ∑' n : ℕ, primeAmp x n ^ 2
      = (∑' n : ℕ, (if (n : ℝ) ≤ x then primeAmp x n ^ 2 else 0))
        + ∑' n : ℕ, (if x < (n : ℝ) then primeAmp x n ^ 2 else 0) := by
    rw [← (summable_primeAmp_sq_le_part hx).tsum_add (summable_primeAmp_sq_gt_part hx)]
    refine tsum_congr fun n => ?_
    by_cases h : (n : ℝ) ≤ x
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (lt_of_not_ge h), zero_add]
  rw [hsplit]
  congr 1
  · rw [tsum_eq_sum (s := Finset.Icc 0 ⌊x⌋₊) fun n hn => ?_, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Icc] at hn
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hn.2
      rw [if_pos hnx]
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [primeAmp]
      · rw [primeAmp_sq_eq hx hn0, if_pos hnx]; ring
    · rw [if_neg]
      simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] at hn
      intro hle
      exact absurd (Nat.le_floor hle) (not_le.mpr hn)
  · rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases h : x < (n : ℝ)
    · rw [if_pos h, if_pos h]
      have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at h; linarith)
      rw [primeAmp_sq_eq hx hn0, if_neg (not_le.mpr h)]; ring
    · rw [if_neg h, if_neg h, mul_zero]

/-- `Σ_n n d_n² = (1/x) Σ_{n≤x} Λ(n)² n² + x³ Σ_{n>x} Λ(n)²/n²`. -/
theorem tsum_mul_primeAmp_sq_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2
      = (1 / x) * ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * (n : ℝ) ^ 2
        + x ^ 3 * ∑' n : ℕ, (if x < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0) := by
  have hx0 : 0 < x := by linarith
  have hs := summable_mul_primeAmp_sq hx
  have hle : Summable (fun n : ℕ => if (n : ℝ) ≤ x then (n : ℝ) * primeAmp x n ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity]) hs
  have hgt : Summable (fun n : ℕ => if x < (n : ℝ) then (n : ℝ) * primeAmp x n ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity]) hs
  have hsplit : ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2
      = (∑' n : ℕ, (if (n : ℝ) ≤ x then (n : ℝ) * primeAmp x n ^ 2 else 0))
        + ∑' n : ℕ, (if x < (n : ℝ) then (n : ℝ) * primeAmp x n ^ 2 else 0) := by
    rw [← hle.tsum_add hgt]
    refine tsum_congr fun n => ?_
    by_cases h : (n : ℝ) ≤ x
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (lt_of_not_ge h), zero_add]
  rw [hsplit]
  congr 1
  · rw [tsum_eq_sum (s := Finset.Icc 0 ⌊x⌋₊) fun n hn => ?_, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Icc] at hn
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hn.2
      rw [if_pos hnx]
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [primeAmp]
      · rw [primeAmp_sq_eq hx hn0, if_pos hnx]; ring
    · rw [if_neg]
      simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] at hn
      intro hle'
      exact absurd (Nat.le_floor hle') (not_le.mpr hn)
  · rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    by_cases h : x < (n : ℝ)
    · rw [if_pos h, if_pos h]
      have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at h; linarith)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [primeAmp_sq_eq hx hn0, if_neg (not_le.mpr h)]
      field_simp
    · rw [if_neg h, if_neg h, mul_zero]

/-! ## The asymptotics -/

/-- **`Σ_n d_n² / (x log x) → 1`.** -/
theorem tendsto_tsum_primeAmp_sq_div :
    Tendsto (fun x : ℝ => (∑' n : ℕ, primeAmp x n ^ 2) / (x * Real.log x)) atTop (𝓝 1) := by
  have h1 := tendsto_sum_vonMangoldt_sq_mul_div
  have h2 := tendsto_tail_vonMangoldt_sq 1
  have h := h1.add h2
  rw [show (1 / 2 : ℝ) + 1 / (((1 : ℕ) : ℝ) + 1) = 1 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [tsum_primeAmp_sq_eq (by linarith)]
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  field_simp
  ring

/-- **`Σ_n n d_n² ≤ 3 x² log x`** for all large `x`. -/
theorem eventually_tsum_mul_primeAmp_sq_le :
    ∀ᶠ x : ℝ in atTop, ∑' n : ℕ, (n : ℝ) * primeAmp x n ^ 2 ≤ 3 * (x ^ 2 * Real.log x) := by
  have h1 := tendsto_sum_vonMangoldt_sq_mul_div.eventually (eventually_le_nhds (by norm_num :
    (1 / 2 : ℝ) < 1))
  have h2 := (tendsto_tail_vonMangoldt_sq 0).eventually (eventually_le_nhds (by norm_num :
    1 / (((0 : ℕ) : ℝ) + 1) < 2))
  filter_upwards [h1, h2, eventually_ge_atTop (2 : ℝ)] with x hA hB hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have hpos : 0 < x ^ 2 * Real.log x := by positivity
  rw [tsum_mul_primeAmp_sq_eq (by linarith)]
  -- the finite part
  have hfin : (1 / x) * ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hn.2
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hx0]
    calc vonMangoldt n ^ 2 * (n : ℝ) ^ 2 = (vonMangoldt n ^ 2 * n) * n := by ring
      _ ≤ (vonMangoldt n ^ 2 * n) * x := mul_le_mul_of_nonneg_left hnx (by positivity)
  have hA' : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * n ≤ x ^ 2 * Real.log x := by
    rwa [div_le_iff₀ hpos, one_mul] at hA
  -- the tail
  have hB' : x ^ 3 * ∑' n : ℕ, (if x < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ 2 else 0)
      ≤ 2 * (x ^ 2 * Real.log x) := by
    simp only [zero_add, pow_one] at hB
    have := hB
    rw [div_mul_eq_mul_div, div_le_iff₀ hlx] at this
    nlinarith
  linarith

end RHTower
