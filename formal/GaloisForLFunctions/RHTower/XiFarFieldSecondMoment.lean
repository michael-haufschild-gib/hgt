import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance

open Finset

namespace RHTower

/-- `log y ≤ 2√y` for `y > 0`. -/
private theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  rw [h2] at h1
  have h3 : (0 : ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
  linarith

/-- The telescoping majorant for the tail weights `log(k+1)/k²`. -/
private theorem log_div_sq_le_telescope {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) / (k : ℝ) ^ (2 : ℕ)
      ≤ 12 * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  set a := Real.sqrt (k : ℝ) with ha
  set b := Real.sqrt ((k : ℝ) + 1) with hb
  have ha2 : a ^ (2 : ℕ) = (k : ℝ) := Real.sq_sqrt (by linarith)
  have hb2 : b ^ (2 : ℕ) = (k : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have ha1 : 1 ≤ a := by
    rw [ha, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hk1
  have hab : a ≤ b := by
    rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have hba : b ≤ a + 1 := by nlinarith [ha2, hb2, ha1, hab]
  have hlog : Real.log ((k : ℝ) + 1) ≤ 2 * b := by
    have h := log_le_two_sqrt (y := (k : ℝ) + 1) (by linarith)
    rw [← hb] at h; exact h
  have hk4 : (k : ℝ) ^ (2 : ℕ) = a ^ (4 : ℕ) := by
    rw [← ha2]; ring
  have hdiff : (b - a) * (b + a) = 1 := by nlinarith [ha2, hb2]
  have hmain : b ^ (2 : ℕ) * (a + b) ≤ 6 * a ^ (3 : ℕ) := by nlinarith [ha1, hba, hb2]
  have hstep : 2 * b / a ^ (4 : ℕ) ≤ 12 * (1 / a - 1 / b) := by
    rw [← sub_nonneg]
    have hrw : 12 * (1 / a - 1 / b) - 2 * b / a ^ (4 : ℕ)
        = (12 * (b - a) * a ^ (3 : ℕ) - 2 * b ^ (2 : ℕ)) / (a ^ (4 : ℕ) * b) := by
      field_simp
    rw [hrw]
    refine div_nonneg ?_ (by positivity)
    have hsum : (0 : ℝ) < a + b := by linarith
    nlinarith [hmain, hdiff, hsum]
  calc Real.log ((k : ℝ) + 1) / (k : ℝ) ^ (2 : ℕ) = Real.log ((k : ℝ) + 1) / a ^ (4 : ℕ) := by
        rw [hk4]
    _ ≤ 2 * b / a ^ (4 : ℕ) := by gcongr
    _ ≤ _ := hstep

/-- `∑_{k=1}^{K} log(k+1)/k² ≤ 12`. -/
private theorem sum_log_div_sq_le (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, Real.log ((k : ℝ) + 1) / (k : ℝ) ^ (2 : ℕ) ≤ 12 := by
  have hbound : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, Real.log ((k : ℝ) + 1) / (k : ℝ) ^ (2 : ℕ)
      ≤ 12 * (1 - 1 / Real.sqrt ((n : ℝ) + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hterm := log_div_sq_le_telescope (k := m + 1) (by omega)
      push_cast at hterm ⊢
      linarith
  have h := hbound K
  have hnn : (0 : ℝ) ≤ 1 / Real.sqrt ((K : ℝ) + 1) := by positivity
  linarith

/-- `∑_{k=1}^{K} 1/k² ≤ 2`. -/
private theorem sum_inv_sq_le (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ (2 : ℕ) ≤ 2 := by
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ (2 : ℕ) ≤ 2 - 1 / (n : ℝ) := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_or_lt_of_le hn with h | h
      · have hm : m = 0 := by omega
        subst hm; norm_num
      · have hm1 : 1 ≤ m := by omega
        have ihm := ih hm1
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep : 1 / (((m : ℕ) + 1 : ℝ)) ^ (2 : ℕ) ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hmpos) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith
        push_cast
        linarith
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · have := hbound K h
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) < 1 / (K : ℝ) := by positivity
    linarith [hbound K h]


/-- **The far field of the zero divisor is `O(log t)`.**  Over any finite set of zero copies whose
ordinates are at distance at least `1` from `t`, the sum of inverse squared distances is bounded by
an absolute multiple of `log t`.  This is the second-order counterpart of the classical bound for
`∑ (1/4 + (t − γ)²)⁻¹`, and it needs only the unit-window zero count. -/
theorem sum_inv_sq_far_le {t : ℝ} (ht : 4 ≤ t) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, 1 ≤ |t - (q.1 : ℂ).im|) :
    ∑ q ∈ F, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ)
      ≤ 160 * Real.log (180 * (t + 1)) + 2 * (smallHeightCount : ℝ) + 960 := by
  classical
  set L : ℝ := Real.log (180 * (t + 1)) with hL
  have hLnn : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by linarith)
  set g : XiZeroCopy → ℕ := fun q => ⌊|t - (q.1 : ℂ).im|⌋₊ with hg
  set K : ℕ := F.sup g with hK
  have hmaps : ∀ q ∈ F, g q ∈ Finset.Icc 1 K := by
    intro q hq
    rw [Finset.mem_Icc]
    refine ⟨?_, Finset.le_sup hq⟩
    have h1 := hF q hq
    have h2 : ((1 : ℕ) : ℝ) ≤ |t - (q.1 : ℂ).im| := by exact_mod_cast h1
    exact Nat.le_floor h2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
      (fun q : XiZeroCopy => 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ))
  rw [← hfib]
  have hkbound : ∀ k ∈ Finset.Icc 1 K,
      (∑ q ∈ F.filter (fun q => g q = k), 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ))
        ≤ (80 * L + 80 * Real.log ((k : ℝ) + 1) + (smallHeightCount : ℝ))
            / (k : ℝ) ^ (2 : ℕ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    set G := F.filter (fun q => g q = k) with hG
    have hann : ∀ q ∈ G, (k : ℝ) ≤ |t - (q.1 : ℂ).im| ∧ |t - (q.1 : ℂ).im| < k + 1 := by
      intro q hq
      rw [hG, Finset.mem_filter] at hq
      exact (Nat.floor_eq_iff (abs_nonneg _)).mp hq.2
    have hcard := card_zeroWindow_le ht k G hann
    have hterm : ∀ q ∈ G, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ) ≤ 1 / (k : ℝ) ^ (2 : ℕ) := by
      intro q hq
      have h1 := (hann q hq).1
      have habs : |t - (q.1 : ℂ).im| ^ (2 : ℕ) = (t - (q.1 : ℂ).im) ^ (2 : ℕ) := sq_abs _
      have hle : (k : ℝ) ^ (2 : ℕ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        rw [← habs]; nlinarith [abs_nonneg (t - (q.1 : ℂ).im)]
      exact one_div_le_one_div_of_le (by positivity) hle
    have hsum_le : (∑ q ∈ G, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ))
        ≤ (G.card : ℝ) * (1 / (k : ℝ) ^ (2 : ℕ)) := by
      calc (∑ q ∈ G, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ))
          ≤ ∑ _q ∈ G, 1 / (k : ℝ) ^ (2 : ℕ) := Finset.sum_le_sum hterm
        _ = (G.card : ℝ) * (1 / (k : ℝ) ^ (2 : ℕ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hlogsplit : Real.log (180 * (t + k + 1)) ≤ L + Real.log ((k : ℝ) + 1) := by
      have h1 : (180 : ℝ) * (t + k + 1) ≤ (180 * (t + 1)) * ((k : ℝ) + 1) := by nlinarith
      rw [hL]
      calc Real.log (180 * (t + k + 1)) ≤ Real.log ((180 * (t + 1)) * ((k : ℝ) + 1)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log (180 * (t + 1)) + Real.log ((k : ℝ) + 1) :=
            Real.log_mul (by positivity) (by positivity)
    have hfinal : (G.card : ℝ)
        ≤ 80 * L + 80 * Real.log ((k : ℝ) + 1) + (smallHeightCount : ℝ) := by
      linarith [hcard, hlogsplit]
    calc (∑ q ∈ G, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ))
        ≤ (G.card : ℝ) * (1 / (k : ℝ) ^ (2 : ℕ)) := hsum_le
      _ ≤ (80 * L + 80 * Real.log ((k : ℝ) + 1) + (smallHeightCount : ℝ))
            * (1 / (k : ℝ) ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_right hfinal (by positivity)
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hkbound) ?_
  have hsplit : ∀ k ∈ Finset.Icc 1 K,
      (80 * L + 80 * Real.log ((k : ℝ) + 1) + (smallHeightCount : ℝ)) / (k : ℝ) ^ (2 : ℕ)
        = (80 * L + (smallHeightCount : ℝ)) * (1 / (k : ℝ) ^ (2 : ℕ))
          + 80 * (Real.log ((k : ℝ) + 1) / (k : ℝ) ^ (2 : ℕ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_inv_sq_le K
  have h2 := sum_log_div_sq_le K
  have hcnn : (0 : ℝ) ≤ (smallHeightCount : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, h2, hLnn, hcnn]

/-- The same bound in `∃`-form, with the constant absorbed. -/
theorem exists_sum_inv_sq_far_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t → ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, 1 ≤ |t - (q.1 : ℂ).im|) →
      ∑ q ∈ F, 1 / (t - (q.1 : ℂ).im) ^ (2 : ℕ) ≤ C * (1 + Real.log t) := by
  refine ⟨160 * Real.log 360 + 2 * (smallHeightCount : ℝ) + 960 + 160, by positivity, ?_⟩
  intro t ht F hF
  have h := sum_inv_sq_far_le ht F hF
  have hlog : Real.log (180 * (t + 1)) ≤ Real.log 360 + Real.log t := by
    have h1 : (180 : ℝ) * (t + 1) ≤ 360 * t := by linarith
    calc Real.log (180 * (t + 1)) ≤ Real.log (360 * t) := Real.log_le_log (by linarith) h1
      _ = Real.log 360 + Real.log t := Real.log_mul (by norm_num) (by linarith)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlog360 : 0 ≤ Real.log 360 := Real.log_nonneg (by norm_num)
  have hcnn : (0 : ℝ) ≤ (smallHeightCount : ℝ) := Nat.cast_nonneg _
  nlinarith [h, hlog, hlogt, hlog360, hcnn]

end RHTower
