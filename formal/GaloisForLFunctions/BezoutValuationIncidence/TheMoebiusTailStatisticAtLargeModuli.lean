import GaloisForLFunctions.BezoutValuationIncidence.TheMoebiusRowInvertsTheCrossScaleKernel
import GaloisForLFunctions.BezoutValuationIncidence.TheDiagonalDualNormIsArchimedean

/-!
# The statistic of the Möbius tail at large moduli

Near the origin both kernels are quadratic in the residue: for `jn < d`,
`Φ_d(jn)/j² + (2Ψ_d - Φ_d)(jn)/(j³n) = d²/(4j²) - 1/(12j²) - nd/j + 5n²/6`. Splitting the harmonics at
`jn < d` gives, for all `n, d ≥ 1`,

`|n² ℓ_d(n) - (π²/24) d²| ≤ 5 n d (1 + log d)`  (`abs_sq_mul_kernelTerm_sub_le`),

so on `n ≤ X` the Möbius statistic is `(π²/24) d² Σ_{n ≤ X} μ(n)/n²` up to
`5 d (1 + log d)(1 + log X)` (`abs_sum_moebius_mul_kernelTerm_sub_le`). Since the full row has the
explicit statistic `2Ψ_d(1) - (6/π²) m_d` (`hasSum_moebius_mul_kernelTerm`), the statistic of the
tail `n > X`, a sum of window statistics, is pinned to `(π²/24) d² Σ_{n > X} μ(n)/n²`
(`abs_kernelValue_sub_sum_le_of_windows`).
-/

open Finset Filter Topology ArithmeticFunction RHTower
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The kernel near the origin -/

/-- The combined harmonic of `n² ℓ_d(n)`, centred at `d²/(4j²)`. -/
def nearOriginHarmonic (d n j : ℕ) : ℝ :=
  residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 +
    (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) /
      (((j : ℝ) + 1) ^ 3 * n) - (d : ℝ) ^ 2 / 4 / ((j : ℝ) + 1) ^ 2

theorem hasSum_nearOriginHarmonic {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    HasSum (nearOriginHarmonic d n)
      (bernoulliKernel d n + cubicKernel d n / n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have h := ((hasSum_bernoulliKernel hd n).add ((hasSum_cubicKernel hd n).div_const (n : ℝ))).sub
    (hz.mul_left ((d : ℝ) ^ 2 / 4))
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : nearOriginHarmonic d n = fun j : ℕ =>
      residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 +
        (2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) /
          ((j : ℝ) + 1) ^ 3 / n - (d : ℝ) ^ 2 / 4 * (1 / ((j : ℝ) + 1) ^ 2) := by
    funext j
    have hk : ((j : ℝ) + 1) ≠ 0 := by positivity
    unfold nearOriginHarmonic
    field_simp
  rw [e, show Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 = (d : ℝ) ^ 2 / 4 * (Real.pi ^ 2 / 6) by ring]
  exact h

/-- Below the first wrap, `(j + 1) n < d`, the harmonic is `-1/(12k²) - nd/k + 5n²/6`, `k = j + 1`. -/
theorem nearOriginHarmonic_eq_of_lt {d n j : ℕ} (hd : 0 < d) (hn : 0 < n) (h : (j + 1) * n < d) :
    nearOriginHarmonic d n j =
      -(1 / (12 * ((j : ℝ) + 1) ^ 2)) - (n : ℝ) * d / ((j : ℝ) + 1) + 5 * (n : ℝ) ^ 2 / 6 := by
  have hmod : (j + 1) * n % d = (j + 1) * n := Nat.mod_eq_of_lt h
  have hc := two_mul_cubicPotential_sub_eq hd ((j + 1) * n)
  rw [hmod] at hc
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : ((j : ℝ) + 1) ≠ 0 := by positivity
  unfold nearOriginHarmonic
  rw [hc, residuePotential, hmod]
  push_cast
  field_simp
  ring

/-- Beyond the first wrap the harmonic is at most `3d²/(8k²) + d³/(2k³n)`. -/
theorem abs_nearOriginHarmonic_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (j : ℕ) :
    |nearOriginHarmonic d n j| ≤
      3 * (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 + (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) := by
  have h1 := abs_residuePotential_le hd ((j + 1) * n)
  have h2 := abs_two_mul_cubicPotential_sub_le hd ((j + 1) * n)
  have hk2 : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
  have hk3 : (0 : ℝ) < ((j : ℝ) + 1) ^ 3 * n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold nearOriginHarmonic
  have t1 : |residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2| ≤ (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 := by
    rw [abs_div, abs_of_pos hk2]; exact div_le_div_of_nonneg_right h1 hk2.le
  have t2 : |(2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) /
      (((j : ℝ) + 1) ^ 3 * n)| ≤ (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) := by
    rw [abs_div, abs_of_pos hk3]; exact div_le_div_of_nonneg_right h2 hk3.le
  have t3 : |(d : ℝ) ^ 2 / 4 / ((j : ℝ) + 1) ^ 2| = (d : ℝ) ^ 2 / 4 / ((j : ℝ) + 1) ^ 2 :=
    abs_of_nonneg (by positivity)
  calc _ ≤ |residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2| +
        |(2 * cubicPotential d ((j + 1) * n) - residuePotential d ((j + 1) * n)) /
          (((j : ℝ) + 1) ^ 3 * n)| + |(d : ℝ) ^ 2 / 4 / ((j : ℝ) + 1) ^ 2| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 + (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) +
        (d : ℝ) ^ 2 / 4 / ((j : ℝ) + 1) ^ 2 := by rw [t3]; linarith
    _ = _ := by ring

/-- `Σ_{j<K} 1/(j+1)² ≤ 2`. -/
theorem sum_range_one_div_succ_sq_le_two (K : ℕ) :
    ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases K with _ | K
  · simp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1)]
  have h := sum_Ico_one_div_succ_sq_le (le_refl 1) (K + 1)
  norm_num at h ⊢
  linarith

/-- `Σ_{J ≤ j < K} 1/(j+1)² ≤ 2/(J+1)`. -/
theorem sum_Ico_one_div_succ_sq_le_two_div (J K : ℕ) :
    ∑ j ∈ Ico J K, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 / ((J : ℝ) + 1) := by
  rcases le_or_gt K J with h | h
  · rw [Ico_eq_empty_of_le h, sum_empty]; positivity
  rw [Finset.sum_eq_sum_Ico_succ_bot h]
  have h1 := sum_Ico_one_div_succ_sq_le (by omega : 1 ≤ J + 1) K
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have h2 : 1 / ((J : ℝ) + 1) ^ 2 ≤ 1 / ((J : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hJ]
    nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  push_cast at h1
  have : 2 / ((J : ℝ) + 1) = 1 / ((J : ℝ) + 1) + 1 / ((J : ℝ) + 1) := by ring
  linarith

/-- The partial sums of the centred harmonics are at most `4 n d (1 + log d)`. -/
theorem abs_sum_range_nearOriginHarmonic_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (K : ℕ) :
    |∑ j ∈ range K, nearOriginHarmonic d n j| ≤ 4 * (n : ℝ) * d * (1 + Real.log d) := by
  set J₀ := (d - 1) / n with hJ₀
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  -- `J₀ n < d ≤ (J₀ + 1) n`
  have hJn : J₀ * n ≤ d - 1 := Nat.div_mul_le_self _ _
  have hJn' : d ≤ (J₀ + 1) * n := by
    have h1 := Nat.div_add_mod (d - 1) n
    have h2 := Nat.mod_lt (d - 1) hn
    rw [hJ₀, Nat.add_mul, one_mul, mul_comm]
    omega
  have hJnR : (J₀ : ℝ) * n ≤ d := by
    have : J₀ * n ≤ d := hJn.trans (Nat.sub_le d 1)
    exact_mod_cast this
  have hJnR' : (d : ℝ) ≤ ((J₀ : ℝ) + 1) * n := by exact_mod_cast hJn'
  have hJ1 : 1 / ((J₀ : ℝ) + 1) ≤ (n : ℝ) / d := by
    rw [div_le_div_iff₀ (by positivity) hdR]; linarith
  -- termwise majorant
  set b : ℕ → ℝ := fun j => if j < J₀ then
      1 / (12 * ((j : ℝ) + 1) ^ 2) + (n : ℝ) * d / ((j : ℝ) + 1) + 5 * (n : ℝ) ^ 2 / 6
    else 3 * (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 + (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n)
  have hab : ∀ j, |nearOriginHarmonic d n j| ≤ b j := by
    intro j
    simp only [b]
    split_ifs with hj
    · have hlt : (j + 1) * n < d := by
        have : (j + 1) * n ≤ J₀ * n := Nat.mul_le_mul_right _ hj
        omega
      rw [nearOriginHarmonic_eq_of_lt hd hn hlt]
      have h0 : 0 ≤ 1 / (12 * ((j : ℝ) + 1) ^ 2) := by positivity
      have h1 : 0 ≤ (n : ℝ) * d / ((j : ℝ) + 1) := by positivity
      have h2 : 0 ≤ 5 * (n : ℝ) ^ 2 / 6 := by positivity
      rw [abs_le]; constructor <;> linarith
    · exact abs_nearOriginHarmonic_le hd hn j
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hab j).trans ?_)
  -- split the majorant at `J₀`
  have hsplit : ∑ j ∈ range K, b j ≤
      ∑ j ∈ range J₀, (1 / (12 * ((j : ℝ) + 1) ^ 2) + (n : ℝ) * d / ((j : ℝ) + 1) +
        5 * (n : ℝ) ^ 2 / 6) +
      ∑ j ∈ Ico J₀ K, (3 * (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 +
        (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n)) := by
    simp only [b]
    rw [sum_ite]
    refine add_le_add ?_ ?_
    · exact sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [mem_filter, mem_range] at hj ⊢; exact hj.2) fun _ _ _ => by positivity
    · exact sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [mem_filter, mem_range, mem_Ico, not_lt] at hj ⊢; exact ⟨hj.2, hj.1⟩)
        fun _ _ _ => by positivity
  refine hsplit.trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
  -- the head
  have hH1 : ∑ j ∈ range J₀, 1 / (12 * ((j : ℝ) + 1) ^ 2) ≤ 1 / 6 := by
    have := sum_range_one_div_succ_sq_le_two J₀
    have e : ∑ j ∈ range J₀, 1 / (12 * ((j : ℝ) + 1) ^ 2) =
        (1 / 12) * ∑ j ∈ range J₀, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by field_simp
    rw [e]; linarith
  have hH2 : ∑ j ∈ range J₀, (n : ℝ) * d / ((j : ℝ) + 1) ≤ (n : ℝ) * d * (1 + Real.log d) := by
    have e : ∑ j ∈ range J₀, (n : ℝ) * d / ((j : ℝ) + 1) =
        (n : ℝ) * d * ∑ j ∈ range J₀, 1 / ((j : ℝ) + 1) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases Nat.eq_zero_or_pos J₀ with h0 | h0
    · rw [h0, range_zero, sum_empty]; linarith
    · have hs := sum_range_one_div_succ_le h0
      have hJd : (J₀ : ℝ) ≤ d := by
        have : (J₀ : ℝ) * 1 ≤ (J₀ : ℝ) * n :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Nat.cast_nonneg _)
        linarith
      have : Real.log J₀ ≤ Real.log d :=
        Real.log_le_log (by exact_mod_cast h0) hJd
      linarith
  have hH3 : ∑ j ∈ range J₀, 5 * (n : ℝ) ^ 2 / 6 ≤ 5 / 6 * ((n : ℝ) * d) := by
    rw [sum_const, card_range, nsmul_eq_mul]
    nlinarith
  -- the tail
  have hT0 := sum_Ico_one_div_succ_sq_le_two_div J₀ K
  have hT1 : ∑ j ∈ Ico J₀ K, 3 * (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 ≤ 3 / 4 * ((n : ℝ) * d) := by
    have e : ∑ j ∈ Ico J₀ K, 3 * (d : ℝ) ^ 2 / 8 / ((j : ℝ) + 1) ^ 2 =
        3 * (d : ℝ) ^ 2 / 8 * ∑ j ∈ Ico J₀ K, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by field_simp
    rw [e]
    calc 3 * (d : ℝ) ^ 2 / 8 * ∑ j ∈ Ico J₀ K, 1 / ((j : ℝ) + 1) ^ 2
        ≤ 3 * (d : ℝ) ^ 2 / 8 * (2 * ((n : ℝ) / d)) := by
          refine mul_le_mul_of_nonneg_left (hT0.trans ?_) (by positivity)
          rw [show 2 / ((J₀ : ℝ) + 1) = 2 * (1 / ((J₀ : ℝ) + 1)) by ring]
          linarith
      _ = 3 / 4 * ((n : ℝ) * d) := by field_simp; ring
  have hT2 : ∑ j ∈ Ico J₀ K, (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) ≤ (n : ℝ) * d := by
    have hterm : ∀ j ∈ Ico J₀ K, (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) ≤
        (d : ℝ) ^ 3 / (2 * n) * ((n : ℝ) / d) * (1 / ((j : ℝ) + 1) ^ 2) := by
      intro j hj
      have hjJ : (J₀ : ℝ) + 1 ≤ (j : ℝ) + 1 := by
        have := (mem_Ico.mp hj).1
        have : (J₀ : ℝ) ≤ j := by exact_mod_cast this
        linarith
      have hk : 1 / ((j : ℝ) + 1) ≤ (n : ℝ) / d :=
        (one_div_le_one_div_of_le (by positivity) hjJ).trans hJ1
      calc (d : ℝ) ^ 3 / 2 / (((j : ℝ) + 1) ^ 3 * n) =
            (d : ℝ) ^ 3 / (2 * n) * (1 / ((j : ℝ) + 1)) * (1 / ((j : ℝ) + 1) ^ 2) := by
            field_simp
        _ ≤ (d : ℝ) ^ 3 / (2 * n) * ((n : ℝ) / d) * (1 / ((j : ℝ) + 1) ^ 2) := by gcongr
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    calc (d : ℝ) ^ 3 / (2 * n) * ((n : ℝ) / d) * ∑ j ∈ Ico J₀ K, 1 / ((j : ℝ) + 1) ^ 2
        ≤ (d : ℝ) ^ 3 / (2 * n) * ((n : ℝ) / d) * (2 * ((n : ℝ) / d)) := by
          refine mul_le_mul_of_nonneg_left (hT0.trans ?_) (by positivity)
          rw [show 2 / ((J₀ : ℝ) + 1) = 2 * (1 / ((J₀ : ℝ) + 1)) by ring]
          linarith
      _ = (n : ℝ) * d := by field_simp
  have hnd1 : (1 : ℝ) ≤ (n : ℝ) * d := by
    have : 1 ≤ n * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' hd.ne')
    exact_mod_cast this
  have hmono : (n : ℝ) * d ≤ (n : ℝ) * d * (1 + Real.log d) := le_mul_of_one_le_right (by linarith) (by linarith)
  linarith

/-- **The kernel near the origin.** For `n, d ≥ 1`, `|n² ℓ_d(n) - (π²/24) d²| ≤ 5 n d (1 + log d)`. -/
theorem abs_sq_mul_kernelTerm_sub_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    |(n : ℝ) ^ 2 * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2| ≤
      5 * (n : ℝ) * d * (1 + Real.log d) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum := hasSum_nearOriginHarmonic hd hn
  have hA : |bernoulliKernel d n + cubicKernel d n / n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2| ≤
      4 * (n : ℝ) * d * (1 + Real.log d) :=
    le_of_tendsto' hsum.tendsto_sum_nat.abs fun K => abs_sum_range_nearOriginHarmonic_le hd hn K
  have hm0 := kernelMean_nonneg hd
  have hm : kernelMean d ≤ (n : ℝ) * d * (1 + Real.log d) := by
    have h1 := kernelMean_le hd
    have h2 : ((d.divisors.card : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.card_divisors_le_self d
    have hpi : Real.pi ^ 2 / 72 ≤ 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc kernelMean d ≤ Real.pi ^ 2 / 72 * (((d.divisors.card : ℕ) : ℝ) - 1) := h1
      _ ≤ 1 * (d : ℝ) := by
          have : ((d.divisors.card : ℕ) : ℝ) - 1 ≤ d := by linarith
          have h0 : 0 ≤ ((d.divisors.card : ℕ) : ℝ) - 1 := by
            have : 1 ≤ d.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hd.ne'⟩
            have : (1 : ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by exact_mod_cast this
            linarith
          exact mul_le_mul hpi this h0 (by norm_num)
      _ ≤ (n : ℝ) * d * (1 + Real.log d) := by
          have : (d : ℝ) ≤ (n : ℝ) * d := le_mul_of_one_le_left hdR hn1
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ n) hdR) hlog]
  have e : (n : ℝ) ^ 2 * kernelTerm d n =
      bernoulliKernel d n + cubicKernel d n / n - kernelMean d := by
    unfold kernelTerm
    field_simp
    ring
  rw [e]
  calc |bernoulliKernel d n + cubicKernel d n / n - kernelMean d - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2|
      ≤ |bernoulliKernel d n + cubicKernel d n / n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2| +
          |kernelMean d| := by
        rw [show bernoulliKernel d n + cubicKernel d n / n - kernelMean d -
          Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 = (bernoulliKernel d n + cubicKernel d n / n -
          Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) - kernelMean d by ring]
        exact abs_sub _ _
    _ ≤ 4 * (n : ℝ) * d * (1 + Real.log d) + (n : ℝ) * d * (1 + Real.log d) := by
        rw [abs_of_nonneg hm0]; linarith
    _ = 5 * (n : ℝ) * d * (1 + Real.log d) := by ring

/-! ## §2. The head of the Möbius row -/

/-- `Σ_{0 < n ≤ X} f(n) = Σ_{j < X} f(j + 1)` for `f(n) = 1/n`. -/
theorem sum_Ioc_eq_sum_range_succ (X : ℕ) :
    ∑ n ∈ Ioc 0 X, 1 / (n : ℝ) = ∑ j ∈ range X, 1 / ((j : ℝ) + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le X), ih, Finset.sum_range_succ]
    push_cast
    ring

/-- On `n ≤ X` the Möbius statistic is `(π²/24) d² Σ_{n ≤ X} μ(n)/n²` up to
`5 d (1 + log d)(1 + log X)`. -/
theorem abs_sum_moebius_mul_kernelTerm_sub_le {d X : ℕ} (hd : 0 < d) (hX : 1 ≤ X) :
    |∑ n ∈ Ioc 0 X, (μ n : ℝ) * kernelTerm d n -
        Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * ∑ n ∈ Ioc 0 X, (μ n : ℝ) / (n : ℝ) ^ 2| ≤
      5 * (d : ℝ) * (1 + Real.log d) * (1 + Real.log X) := by
  rw [mul_sum, ← sum_sub_distrib]
  have hterm : ∀ n ∈ Ioc 0 X, |(μ n : ℝ) * kernelTerm d n -
      Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * ((μ n : ℝ) / (n : ℝ) ^ 2)| ≤
        5 * (d : ℝ) * (1 + Real.log d) * (1 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn0, -⟩ := mem_Ioc.mp hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hb := abs_sq_mul_kernelTerm_sub_le hd hn0
    have hmu : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have e : (μ n : ℝ) * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2 * ((μ n : ℝ) / (n : ℝ) ^ 2) =
        (μ n : ℝ) * (((n : ℝ) ^ 2 * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2) / (n : ℝ) ^ 2) := by
      field_simp
    rw [e, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    calc |(μ n : ℝ)| * (|(n : ℝ) ^ 2 * kernelTerm d n - Real.pi ^ 2 / 24 * (d : ℝ) ^ 2| / (n : ℝ) ^ 2)
        ≤ 1 * (5 * (n : ℝ) * d * (1 + Real.log d) / (n : ℝ) ^ 2) :=
          mul_le_mul hmu (div_le_div_of_nonneg_right hb (by positivity)) (by positivity)
            (by norm_num)
      _ = 5 * (d : ℝ) * (1 + Real.log d) * (1 / (n : ℝ)) := by field_simp
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by
    have := Real.log_nonneg (by exact_mod_cast hd : (1 : ℝ) ≤ d); positivity)
  rw [sum_Ioc_eq_sum_range_succ]
  exact sum_range_one_div_succ_le hX

/-! ## §3. The tail as a sum of windows -/

/-- The full-row statistic as a `HasSum` over `ℕ`. -/
theorem hasSum_nat_moebius_mul_kernelTerm {d : ℕ} (hd : 0 < d) :
    HasSum (fun n : ℕ => (μ n : ℝ) * kernelTerm d n)
      (2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d) := by
  refine (Function.Injective.hasSum_iff PNat.coe_injective fun n hn => ?_).mp
    (hasSum_moebius_mul_kernelTerm hd)
  have : n = 0 := by
    by_contra h0
    exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
  simp [this]

/-- A window statistic is the Möbius sum of `ℓ_d` over the window. -/
theorem kernelStatisticAll_moebiusWindowRow_eq (d Q : ℕ) :
    kernelStatisticAll (2 * Q) (moebiusWindowRow Q) d =
      ∑ n ∈ Ioc Q (2 * Q), (μ n : ℝ) * kernelTerm d n := by
  rw [kernelStatisticAll_eq_sum_kernelTerm]
  have e : ∀ n ∈ Icc 1 (2 * Q), moebiusWindowRow Q n * kernelTerm d n =
      if Q < n ∧ n ≤ 2 * Q then (μ n : ℝ) * kernelTerm d n else 0 := fun n _ => by
    unfold moebiusWindowRow moebiusReal
    split_ifs <;> simp
  rw [sum_congr rfl e, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

/-- The sums over `(0, 2^k X]` telescope into the head and `k` windows. -/
theorem sum_Ioc_two_pow_mul_eq (F : ℕ → ℝ) (X k : ℕ) :
    ∑ n ∈ Ioc 0 (2 ^ k * X), F n =
      ∑ n ∈ Ioc 0 X, F n + ∑ i ∈ range k, ∑ n ∈ Ioc (2 ^ i * X) (2 * (2 ^ i * X)), F n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih,
      show 2 ^ (k + 1) * X = 2 * (2 ^ k * X) by ring,
      sum_Ioc_consecutive _ (Nat.zero_le _) (by omega : 2 ^ k * X ≤ 2 * (2 ^ k * X))]

/-- **The tail of the Möbius row as a sum of windows.** If the window statistics
`Λ_d(μ𝟙_{(2^i X, 2^{i+1} X]})` are at most `b_i` and `Σ_{i<k} b_i ≤ B` for all `k`, then the head
`Σ_{n ≤ X} μ(n) ℓ_d(n)` differs from the full-row value `2Ψ_d(1) - (6/π²) m_d` by at most `B`. -/
theorem abs_kernelValue_sub_sum_le_of_windows {d X : ℕ} (hd : 0 < d) (hX : 1 ≤ X) {b : ℕ → ℝ}
    {B : ℝ}
    (hb : ∀ i, |kernelStatisticAll (2 * (2 ^ i * X)) (moebiusWindowRow (2 ^ i * X)) d| ≤ b i)
    (hB : ∀ k, ∑ i ∈ range k, b i ≤ B) :
    |2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d -
        ∑ n ∈ Ioc 0 X, (μ n : ℝ) * kernelTerm d n| ≤ B := by
  set F : ℕ → ℝ := fun n => (μ n : ℝ) * kernelTerm d n
  have hF0 : F 0 = 0 := by simp [F]
  have hsum := hasSum_nat_moebius_mul_kernelTerm hd
  -- partial sums over `(0, M]` converge to the full-row value
  have hIoc : ∀ M, ∑ n ∈ Ioc 0 M, F n = ∑ n ∈ range (M + 1), F n := fun M => by
    induction M with
    | zero => simp [hF0]
    | succ M ih => rw [sum_Ioc_succ_top (Nat.zero_le M), ih, Finset.sum_range_succ _ (M + 1)]
  have hgrow : Tendsto (fun k : ℕ => 2 ^ k * X + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ 2 ^ k * X := Nat.le_mul_of_pos_right _ hX
    simp only [id]; omega
  have hlim : Tendsto (fun k : ℕ => ∑ n ∈ Ioc 0 (2 ^ k * X), F n) atTop
      (𝓝 (2 * cubicPotential d 1 - 6 / Real.pi ^ 2 * kernelMean d)) := by
    simp_rw [hIoc]
    exact hsum.tendsto_sum_nat.comp hgrow
  have hlim' := (hlim.sub_const (∑ n ∈ Ioc 0 X, F n)).abs
  refine le_of_tendsto' hlim' fun k => ?_
  rw [sum_Ioc_two_pow_mul_eq, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => ?_).trans (hB k))
  rw [← kernelStatisticAll_moebiusWindowRow_eq]
  exact hb i

end

end GaloisForLFunctions.BezoutValuationIncidence
