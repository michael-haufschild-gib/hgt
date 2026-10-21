import GaloisForLFunctions.BezoutValuationIncidence.SharpConstantOfTheRankTwoRemainder

/-!
# Large-sieve dispersion for bounded rows

For a row with `|c(d)| ≤ 1` supported on `[1, Q₀]` the Selberg coordinates are bounded by a
harmonic sum over multiples,

`|Y_c(e)| ≤ Σ_{k ≤ Q₀/e} 1/(ek) ≤ 2 √(Q₀/e)/e`,

using `Σ_{k ≤ m} 1/k ≤ 2√m`. The Selberg-coordinate dispersion then holds with explicit constants
for every bounded row, including Möbius, Liouville, characters and their restrictions:

`Σ_{e ≤ Q₀} Y(e)² e⁴ ≤ 2 Q₀² (Q₀ + 1)`,  `Σ_{e ≤ Q₀} |Y(e)| e³ ≤ Q₀² (Q₀ + 1)`,

`|B(c, c') + m(c) R(c') + β(c) H(c')|
  ≤ ½ √(2Q₀²(Q₀+1)) √(L + 2Q₀² - 1) √(Σ_n c'(n)²/n⁴) + ½ Q₀²(Q₀+1) Σ_n |c'(n)|/n³`

for `c'` on `[A+1, A+L]`. Against the rank-two remainder bound `≍ Q₀² Σ|c'|/n²` the large sieve gains
`≍ √(Q₀/L)` on long large-scale windows `Q₀ ≤ L ≤ Q₀²`. This is the prime-packet dispersion
extended to every bounded row of the receiver, with no arithmetic input.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- `Σ_{k ≤ m} 1/k ≤ 2√m`. -/
theorem sum_Icc_inv_le_two_sqrt (m : ℕ) : ∑ k ∈ Icc 1 m, 1 / (k : ℝ) ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hs1 : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = (m : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hsq0 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg _)
    have hle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    -- `1/(m+1) ≤ 2(√(m+1) - √m)`
    have key : 1 / ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) - 2 * Real.sqrt m := by
      have hprod : (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt m) *
          (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt m) = 1 := by
        nlinarith
      have hsum : Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt m ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
        have : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
          rw [Real.sqrt_le_left (by positivity)]
          push_cast; nlinarith
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

/-- `|Y_c(e)| ≤ 2√(Q₀/e)/e` for a row bounded by one on `[1, Q₀]`. -/
theorem abs_selbergMultiplesCoord_le {N Q₀ e : ℕ} (he : 1 ≤ e) {c : ℕ → ℝ}
    (hc : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) :
    |selbergMultiplesCoord N c e| ≤ 2 * Real.sqrt ((Q₀ / e : ℕ) : ℝ) / e := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  unfold selbergMultiplesCoord
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ (Icc 1 N).filter (fun d => e ∣ d), |c d / d|
      ≤ ∑ k ∈ Icc 1 (Q₀ / e), 1 / ((e * k : ℕ) : ℝ) := by
        have hsub : ((Icc 1 N).filter (fun d => e ∣ d)).filter (fun d => c d ≠ 0) ⊆
            (Icc 1 (Q₀ / e)).image (fun k => e * k) := by
          intro d hd
          obtain ⟨hd1, hcd⟩ := mem_filter.mp hd
          obtain ⟨hdI, k, rfl⟩ := mem_filter.mp hd1
          have hdQ := hsupp _ hcd
          have hk : 1 ≤ k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · subst h; simp at hdI
            · exact h
          exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk, (Nat.le_div_iff_mul_le he).mpr (by
            rw [mul_comm]; exact hdQ)⟩, rfl⟩
        calc ∑ d ∈ (Icc 1 N).filter (fun d => e ∣ d), |c d / d|
            = ∑ d ∈ ((Icc 1 N).filter (fun d => e ∣ d)).filter (fun d => c d ≠ 0), |c d / d| := by
              refine (sum_filter_of_ne fun d _ h => ?_).symm
              intro hc0; apply h; rw [hc0, zero_div, abs_zero]
          _ ≤ ∑ d ∈ (Icc 1 (Q₀ / e)).image (fun k => e * k), 1 / (d : ℝ) := by
              refine sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity) |>.trans' ?_
              refine sum_le_sum fun d hd => ?_
              have hd1 := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hd).1).1).1
              have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
              rw [abs_div, abs_of_pos hdR, div_le_div_iff_of_pos_right hdR]
              exact hc d
          _ = ∑ k ∈ Icc 1 (Q₀ / e), 1 / ((e * k : ℕ) : ℝ) := by
              rw [sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h]
    _ = 1 / (e : ℝ) * ∑ k ∈ Icc 1 (Q₀ / e), 1 / (k : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by push_cast; field_simp
    _ ≤ 1 / (e : ℝ) * (2 * Real.sqrt ((Q₀ / e : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_le_two_sqrt _) (by positivity)
    _ = 2 * Real.sqrt ((Q₀ / e : ℕ) : ℝ) / e := by ring

theorem sum_Icc_cast_eq (n : ℕ) : ∑ e ∈ Icc 1 n, (e : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

theorem sum_selberg_sq_mul_pow_four_le {N Q₀ : ℕ} {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1)
    (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) :
    ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4 ≤
      2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1) := by
  have hterm : ∀ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4 ≤ 4 * Q₀ * (e : ℝ) := by
    intro e he
    have he' := mem_Icc.mp he
    have heR : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
    have hY := abs_selbergMultiplesCoord_le (N := N) (e := e) (by omega) hc hsupp
    have hm : ((Q₀ / e : ℕ) : ℝ) * e ≤ Q₀ := by exact_mod_cast Nat.div_mul_le_self Q₀ e
    have hsq : selbergMultiplesCoord N c e ^ 2 ≤ 4 * ((Q₀ / e : ℕ) : ℝ) / (e : ℝ) ^ 2 := by
      have h0 : 0 ≤ |selbergMultiplesCoord N c e| := abs_nonneg _
      have := pow_le_pow_left₀ h0 hY 2
      rw [sq_abs, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at this
      linarith
    calc selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4
        ≤ 4 * ((Q₀ / e : ℕ) : ℝ) / (e : ℝ) ^ 2 * (e : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 4 * (((Q₀ / e : ℕ) : ℝ) * e) * e := by field_simp
      _ ≤ 4 * Q₀ * (e : ℝ) := by gcongr
  calc ∑ e ∈ Icc 2 Q₀, selbergMultiplesCoord N c e ^ 2 * (e : ℝ) ^ 4
      ≤ ∑ e ∈ Icc 2 Q₀, 4 * Q₀ * (e : ℝ) := sum_le_sum hterm
    _ ≤ ∑ e ∈ Icc 1 Q₀, 4 * Q₀ * (e : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
          fun _ _ _ => by positivity
    _ = 2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1) := by rw [← mul_sum, sum_Icc_cast_eq]; ring

theorem sum_abs_selberg_mul_pow_three_le {N Q₀ : ℕ} {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1)
    (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀) :
    ∑ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3 ≤ (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1) := by
  have hterm : ∀ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3 ≤ 2 * Q₀ * (e : ℝ) := by
    intro e he
    have he' := mem_Icc.mp he
    have heR : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
    have heQ : (e : ℝ) ≤ Q₀ := by exact_mod_cast he'.2
    have hY := abs_selbergMultiplesCoord_le (N := N) (e := e) (by omega) hc hsupp
    have hm : ((Q₀ / e : ℕ) : ℝ) * e ≤ Q₀ := by exact_mod_cast Nat.div_mul_le_self Q₀ e
    -- `√(Q₀/e) e ≤ Q₀`
    have hs : Real.sqrt ((Q₀ / e : ℕ) : ℝ) * e ≤ Q₀ := by
      have h1 : (Real.sqrt ((Q₀ / e : ℕ) : ℝ) * e) ^ 2 ≤ (Q₀ : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
    calc |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3
        ≤ 2 * Real.sqrt ((Q₀ / e : ℕ) : ℝ) / e * (e : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hY (by positivity)
      _ = 2 * (Real.sqrt ((Q₀ / e : ℕ) : ℝ) * e) * e := by field_simp
      _ ≤ 2 * Q₀ * (e : ℝ) := by gcongr
  calc ∑ e ∈ Icc 2 Q₀, |selbergMultiplesCoord N c e| * (e : ℝ) ^ 3
      ≤ ∑ e ∈ Icc 2 Q₀, 2 * Q₀ * (e : ℝ) := sum_le_sum hterm
    _ ≤ ∑ e ∈ Icc 1 Q₀, 2 * Q₀ * (e : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
          fun _ _ _ => by positivity
    _ = (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1) := by rw [← mul_sum, sum_Icc_cast_eq]; ring

/-- **Large-sieve dispersion for bounded rows.** For `|c| ≤ 1` on `[1, Q₀]`, `2 ≤ Q₀ ≤ N`, and `c'`
on `[A+1, A+L]`, `A + L ≤ N`:
`|B + m R' + β H'| ≤ ½ √(2Q₀²(Q₀+1)) √(L + 2Q₀² - 1) √(Σ c'²/n⁴) + ½ Q₀²(Q₀+1) Σ |c'|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_bounded {N Q₀ A L : ℕ} {c c' : ℕ → ℝ}
    (hQ₀ : 2 ≤ Q₀) (hQN : Q₀ ≤ N) (hc : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ≤ Q₀)
    (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L)) (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      1 / 2 * Real.sqrt (2 * (Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1)) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 2 * ((Q₀ : ℝ) ^ 2 * ((Q₀ : ℝ) + 1)) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 := by
  refine (abs_rowBilinear_add_mean_add_beta_le_selberg hQ₀ hQN hsupp hsupp' hAL).trans ?_
  have h1 := sum_selberg_sq_mul_pow_four_le (N := N) hc hsupp
  have h2 := sum_abs_selberg_mul_pow_three_le (N := N) hc hsupp
  have hn : 0 ≤ ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 :=
    sum_nonneg fun n _ => by positivity
  gcongr

end

end GaloisForLFunctions.BezoutValuationIncidence
