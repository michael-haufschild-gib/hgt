import GaloisForLFunctions.RHTower.CentralBinomialAbelBounds

/-!
# The half-sum estimate for the Legendre convolution

For `‖η‖ = 1`, `η ≠ 1`, `N ≥ 8` and `N/2 − 1 ≤ K ≤ N/2 + 2`,

`‖Σ_{k<K} C_k C_{N−k} η^k − C_N (1 − η)^{-1/2}‖ ≤ 400 / (‖1 − η‖ N)`.

Writing `C_{N−k} = C_N (1 + g_k)` with `0 ≤ g_k ≤ 8k/N`, the main part is the boundary
central-binomial series (tail `≤ 2C_K/‖1−η‖`) and the remainder `C_N Σ C_k g_k η^k` is controlled by
Abel's bound through the variation of `C_k g_k`.
-/

open Finset
open scoped BigOperators

namespace RHTower

namespace LegendreBoost

open RouteJProfile

/-! ## The ratio `C_{N−k}/C_N` -/

theorem cb_sub_succ (m : ℕ) : cb m - cb (m + 1) = cb m / (2 * (m : ℝ) + 2) := by
  rw [cb_succ]
  have hm : (2 * ((m : ℝ) + 1)) ≠ 0 := by positivity
  field_simp
  ring

theorem cb_pred_eq (m : ℕ) : cb m = cb (m + 1) * (1 + 1 / (2 * (m : ℝ) + 1)) := by
  rw [cb_succ]
  have h1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * ((m : ℝ) + 1)) ≠ 0 := by positivity
  field_simp
  ring

/-- `(1 + x)^k ≤ 1 + 4kx` when `4kx ≤ 3`, `x ≥ 0`. -/
theorem one_add_pow_le_of_small {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : 4 * (k : ℝ) * x ≤ 3) :
    (1 + x) ^ k ≤ 1 + 4 * (k : ℝ) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : 4 * (k : ℝ) * x ≤ 3 := by push_cast at hk; nlinarith
      have ih' := ih hk'
      rw [pow_succ]
      push_cast
      calc (1 + x) ^ k * (1 + x) ≤ (1 + 4 * (k : ℝ) * x) * (1 + x) :=
            mul_le_mul_of_nonneg_right ih' (by linarith)
        _ = 1 + 4 * ((k : ℝ) + 1) * x - (3 * x - 4 * (k : ℝ) * x ^ 2) := by ring
        _ ≤ 1 + 4 * ((k : ℝ) + 1) * x := by nlinarith

/-- `C_{N−k} ≤ C_N (1 + 1/(N−1))^k` for `2k ≤ N + 2`. -/
theorem cb_sub_le_pow {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * k ≤ N + 2) :
    cb (N - k) ≤ cb N * (1 + 1 / ((N : ℝ) - 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : 2 * k ≤ N + 2 := by omega
      have ih' := ih hk'
      have hrec := cb_pred_eq (N - k - 1)
      rw [show N - k - 1 + 1 = N - k by omega] at hrec
      rw [show N - (k + 1) = N - k - 1 by omega, hrec, pow_succ]
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (8 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      have hfac : 1 + 1 / (2 * ((N - k - 1 : ℕ) : ℝ) + 1) ≤ 1 + 1 / ((N : ℝ) - 1) := by
        have hcast : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - k - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
        rw [hcast]
        have hk2 : (2 * (k : ℝ)) ≤ N := by exact_mod_cast (by omega : 2 * k ≤ N)
        gcongr
        linarith
      have hpos : 0 ≤ cb N * (1 + 1 / ((N : ℝ) - 1)) ^ k := by
        have := cb_pos N
        positivity
      calc cb (N - k) * (1 + 1 / (2 * ((N - k - 1 : ℕ) : ℝ) + 1))
          ≤ cb N * (1 + 1 / ((N : ℝ) - 1)) ^ k * (1 + 1 / ((N : ℝ) - 1)) :=
            mul_le_mul ih' hfac (by positivity) hpos
        _ = cb N * ((1 + 1 / ((N : ℝ) - 1)) ^ k * (1 + 1 / ((N : ℝ) - 1))) := by ring

/-- **The ratio bound:** `C_{N−k} ≤ C_N (1 + 8k/N)` for `N ≥ 8`, `2k ≤ N + 2`. -/
theorem cb_sub_le {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * k ≤ N + 2) :
    cb (N - k) ≤ cb N * (1 + 8 * (k : ℝ) / N) := by
  have h1 := cb_sub_le_pow hN hk
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hkr : 2 * (k : ℝ) ≤ N + 2 := by exact_mod_cast hk
  have hx : (0 : ℝ) ≤ 1 / ((N : ℝ) - 1) := by
    apply div_nonneg zero_le_one; linarith
  have hsmall : 4 * (k : ℝ) * (1 / ((N : ℝ) - 1)) ≤ 3 := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    linarith
  have h2 := one_add_pow_le_of_small hx k hsmall
  have h3 : 4 * (k : ℝ) * (1 / ((N : ℝ) - 1)) ≤ 8 * (k : ℝ) / N := by
    rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc cb (N - k) ≤ cb N * (1 + 1 / ((N : ℝ) - 1)) ^ k := h1
    _ ≤ cb N * (1 + 4 * (k : ℝ) * (1 / ((N : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left h2 (cb_pos N).le
    _ ≤ cb N * (1 + 8 * (k : ℝ) / N) := mul_le_mul_of_nonneg_left (by linarith) (cb_pos N).le

theorem cb_le_cb_sub (N k : ℕ) : cb N ≤ cb (N - k) :=
  cb_antitone (Nat.sub_le N k)

/-- The relative excess `g_k = C_{N−k}/C_N − 1`. -/
noncomputable def gk (N k : ℕ) : ℝ := cb (N - k) / cb N - 1

theorem gk_nonneg (N k : ℕ) : 0 ≤ gk N k := by
  unfold gk
  rw [sub_nonneg, le_div_iff₀ (cb_pos N), one_mul]
  exact cb_le_cb_sub N k

theorem gk_le {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * k ≤ N + 2) : gk N k ≤ 8 * (k : ℝ) / N := by
  unfold gk
  rw [sub_le_iff_le_add, div_le_iff₀ (cb_pos N)]
  have := cb_sub_le hN hk
  linarith

/-- The increment `g_{k+1} − g_k ≤ 12/N`. -/
theorem gk_succ_sub_le {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * (k + 1) ≤ N + 2) :
    gk N (k + 1) - gk N k ≤ 12 / N := by
  unfold gk
  have hrec := cb_sub_succ (N - k - 1)
  rw [show N - k - 1 + 1 = N - k by omega] at hrec
  rw [show N - (k + 1) = N - k - 1 by omega]
  have hcast : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hkr : 2 * ((k : ℝ) + 1) ≤ N + 2 := by exact_mod_cast hk
  have hb := cb_sub_le hN hk
  rw [show N - (k + 1) = N - k - 1 by omega] at hb
  have hcN := cb_pos N
  have hcNk := cb_pos (N - k - 1)
  -- (cb (N−k−1) − cb (N−k))/cb N = cb (N−k−1)/(2(N−k−1)+2)/cb N ≤ (1 + 8(k+1)/N)/(2(N−k)) ≤ 12/N
  have hdiff : cb (N - k - 1) / cb N - 1 - (cb (N - k) / cb N - 1) =
      (cb (N - k - 1) - cb (N - k)) / cb N := by
    field_simp
    ring
  rw [hdiff, hrec, hcast]
  have hNk : (0 : ℝ) < 2 * ((N : ℝ) - k - 1) + 2 := by linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at hb
  have h8 : 8 * ((k : ℝ) + 1) / N ≤ 5 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hb6 : cb (N - k - 1) ≤ 6 * cb N := by
    calc cb (N - k - 1) ≤ cb N * (1 + 8 * ((k : ℝ) + 1) / N) := hb
      _ ≤ cb N * 6 := mul_le_mul_of_nonneg_left (by linarith) hcN.le
      _ = 6 * cb N := by ring
  nlinarith [mul_le_mul_of_nonneg_right hb6 (Nat.cast_nonneg N), hcN, hkr, hNr]

/-! ## The variation term `d_k = C_k g_k` -/

/-- `d_k = C_k g_k`. -/
noncomputable def dk (N k : ℕ) : ℝ := cb k * gk N k

theorem dk_nonneg (N k : ℕ) : 0 ≤ dk N k := mul_nonneg (cb_pos k).le (gk_nonneg N k)

theorem dk_le {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * k ≤ N + 2) : dk N k ≤ cb k * (8 * (k : ℝ) / N) :=
  mul_le_mul_of_nonneg_left (gk_le hN hk) (cb_pos k).le

theorem gk_succ_sub_nonneg (N k : ℕ) (hk : k + 1 ≤ N) : 0 ≤ gk N (k + 1) - gk N k := by
  unfold gk
  rw [sub_sub_sub_cancel_right, sub_nonneg]
  apply div_le_div_of_nonneg_right _ (cb_pos N).le
  exact cb_antitone (by omega)

theorem abs_dk_succ_sub_le {N k : ℕ} (hN : 8 ≤ N) (hk : 2 * (k + 1) ≤ N + 2) :
    |dk N (k + 1) - dk N k| ≤ 16 * cb k / N := by
  unfold dk
  have hΔg := gk_succ_sub_le hN hk
  have hΔg0 := gk_succ_sub_nonneg N k (by omega)
  have hg := gk_le hN (by omega : 2 * k ≤ N + 2)
  have hg0 := gk_nonneg N k
  have hcs := cb_sub_succ k
  have hck := cb_pos k
  have hck1 := cb_pos (k + 1)
  have hcle : cb (k + 1) ≤ cb k := cb_antitone (Nat.le_succ k)
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hkr : 2 * ((k : ℝ) + 1) ≤ N + 2 := by exact_mod_cast hk
  -- d_{k+1} − d_k = C_{k+1} (g_{k+1} − g_k) − (C_k − C_{k+1}) g_k
  have hid : cb (k + 1) * gk N (k + 1) - cb k * gk N k =
      cb (k + 1) * (gk N (k + 1) - gk N k) - (cb k - cb (k + 1)) * gk N k := by ring
  rw [hid, abs_le]
  have hA : 0 ≤ cb (k + 1) * (gk N (k + 1) - gk N k) := mul_nonneg hck1.le hΔg0
  have hA' : cb (k + 1) * (gk N (k + 1) - gk N k) ≤ 12 * cb k / N := by
    calc cb (k + 1) * (gk N (k + 1) - gk N k) ≤ cb k * (12 / N) :=
          mul_le_mul hcle hΔg hΔg0 hck.le
      _ = 12 * cb k / N := by ring
  have hB : 0 ≤ (cb k - cb (k + 1)) * gk N k := mul_nonneg (by linarith) hg0
  have hB' : (cb k - cb (k + 1)) * gk N k ≤ 4 * cb k / N := by
    rw [hcs]
    have hk2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
    calc cb k / (2 * (k : ℝ) + 2) * gk N k ≤ cb k / (2 * (k : ℝ) + 2) * (8 * (k : ℝ) / N) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = cb k * (8 * (k : ℝ) / ((2 * (k : ℝ) + 2) * N)) := by
          field_simp
      _ ≤ cb k * (4 / N) := by
          apply mul_le_mul_of_nonneg_left _ hck.le
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = 4 * cb k / N := by ring
  have hq : 0 ≤ cb k / N := by positivity
  have e12 : 12 * cb k / N = 12 * (cb k / N) := by ring
  have e4 : 4 * cb k / N = 4 * (cb k / N) := by ring
  have e16 : 16 * cb k / N = 16 * (cb k / N) := by ring
  rw [e12] at hA'
  rw [e4] at hB'
  rw [e16]
  constructor <;> linarith

/-! ## The Abel estimate for `Σ d_k η^k` -/

theorem sqrt_bound_aux {N K : ℕ} (hN : 8 ≤ N) (hK' : N ≤ 2 * K + 2) :
    cb (K - 1) ≤ 2 / Real.sqrt N := by
  have h1 := cb_le_inv_sqrt (K - 1)
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : (2 * ((K - 1 : ℕ) : ℝ) + 1) ≥ (N : ℝ) - 3 := by
    have : ((K - 1 : ℕ) : ℝ) ≥ (K : ℝ) - 1 := by
      rcases Nat.eq_zero_or_pos K with h | h
      · subst h; simp
      · rw [Nat.cast_sub h]; push_cast; linarith
    have hK'' : (N : ℝ) ≤ 2 * K + 2 := by exact_mod_cast hK'
    linarith
  have hsq : Real.sqrt N / 2 ≤ Real.sqrt (2 * ((K - 1 : ℕ) : ℝ) + 1) := by
    calc Real.sqrt N / 2 = Real.sqrt (N / 4) := by
          rw [Real.sqrt_div (Nat.cast_nonneg N), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (2 * ((K - 1 : ℕ) : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  calc cb (K - 1) ≤ 1 / Real.sqrt (2 * ((K - 1 : ℕ) : ℝ) + 1) := h1
    _ ≤ 1 / (Real.sqrt N / 2) := by
        apply one_div_le_one_div_of_le (by positivity) hsq
    _ = 2 / Real.sqrt N := by field_simp

theorem norm_sum_dk_mul_pow_le {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) {N K : ℕ} (hN : 8 ≤ N)
    (hK : 2 * K ≤ N + 4) (hK' : N ≤ 2 * K + 2) :
    ‖∑ k ∈ range K, (dk N k : ℂ) * η ^ k‖ ≤ 2 / ‖1 - η‖ * (76 / Real.sqrt N) := by
  have hab := norm_sum_mul_pow_le_abel hη h1 (dk N) K
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  -- the boundary term
  have hbd : |dk N (K - 1)| ≤ 12 / Real.sqrt N := by
    rw [abs_of_nonneg (dk_nonneg _ _)]
    have h := dk_le hN (k := K - 1) (by omega)
    have hc := sqrt_bound_aux hN hK'
    have h8 : 8 * ((K - 1 : ℕ) : ℝ) / N ≤ 6 := by
      rw [div_le_iff₀ (by positivity)]
      have : ((K - 1 : ℕ) : ℝ) ≤ (N : ℝ) / 2 + 2 := by
        have : (K - 1 : ℕ) ≤ N / 2 + 2 := by omega
        have h' : ((K - 1 : ℕ) : ℝ) ≤ ((N / 2 + 2 : ℕ) : ℝ) := by exact_mod_cast this
        have h'' : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
          rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self N 2
        push_cast at h'
        linarith
      linarith
    calc dk N (K - 1) ≤ cb (K - 1) * (8 * ((K - 1 : ℕ) : ℝ) / N) := h
      _ ≤ (2 / Real.sqrt N) * 6 := mul_le_mul hc h8 (by positivity) (by positivity)
      _ = 12 / Real.sqrt N := by ring
  -- the variation
  have hvar : ∑ i ∈ range (K - 1), |dk N (i + 1) - dk N i| ≤ 64 / Real.sqrt N := by
    calc ∑ i ∈ range (K - 1), |dk N (i + 1) - dk N i|
        ≤ ∑ i ∈ range (K - 1), 16 * cb i / N := by
          apply sum_le_sum
          intro i hi
          rw [mem_range] at hi
          exact abs_dk_succ_sub_le hN (by omega)
      _ = 16 / N * ∑ i ∈ range (K - 1), cb i := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      _ ≤ 16 / N * (2 * Real.sqrt (2 * ((K - 1 : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_cb_le (K - 1)) (by positivity)
      _ ≤ 16 / N * (2 * (2 * Real.sqrt N)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc Real.sqrt (2 * ((K - 1 : ℕ) : ℝ) + 1) ≤ Real.sqrt (4 * N) := by
                apply Real.sqrt_le_sqrt
                have : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
                have hK2 : (2 * K : ℝ) ≤ N + 4 := by exact_mod_cast hK
                linarith
            _ = 2 * Real.sqrt N := by
                rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ = 64 / Real.sqrt N := by
          have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
          rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hsqrt.ne']
          linear_combination 64 * hss
  calc ‖∑ k ∈ range K, (dk N k : ℂ) * η ^ k‖
      ≤ 2 / ‖1 - η‖ * (|dk N (K - 1)| + ∑ i ∈ range (K - 1), |dk N (i + 1) - dk N i|) := hab
    _ ≤ 2 / ‖1 - η‖ * (12 / Real.sqrt N + 64 / Real.sqrt N) := by gcongr
    _ = 2 / ‖1 - η‖ * (76 / Real.sqrt N) := by ring

/-! ## The half-sum estimate -/

theorem cb_le_two_div_sqrt {N : ℕ} (hN : 8 ≤ N) : cb N ≤ 2 / Real.sqrt N := by
  have h1 := cb_le_inv_sqrt N
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  calc cb N ≤ 1 / Real.sqrt (2 * (N : ℝ) + 1) := h1
    _ ≤ 1 / Real.sqrt N := by
        apply one_div_le_one_div_of_le hpos
        exact Real.sqrt_le_sqrt (by linarith)
    _ ≤ 2 / Real.sqrt N := by
        rw [div_le_div_iff_of_pos_right hpos]; norm_num

theorem cb_K_le_two_div_sqrt {N K : ℕ} (hN : 8 ≤ N) (hK' : N ≤ 2 * K + 2) : cb K ≤ 2 / Real.sqrt N := by
  have h := sqrt_bound_aux (K := K + 1) hN (by omega)
  simpa using h

/-- **The half-sum estimate.** -/
theorem norm_halfSum_sub_le {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) {N K : ℕ} (hN : 8 ≤ N)
    (hK : 2 * K ≤ N + 4) (hK' : N ≤ 2 * K + 2) :
    ‖∑ k ∈ range K, ((cb k * cb (N - k) : ℝ) : ℂ) * η ^ k - (cb N : ℂ) * (1 - η) ^ (-(1 / 2 : ℂ))‖ ≤
      400 / (‖1 - η‖ * N) := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hη1 : 0 < ‖1 - η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h1))
  have hcN := cb_pos N
  -- decomposition C_k C_{N−k} = C_N C_k + C_N d_k
  have hsplit : ∑ k ∈ range K, ((cb k * cb (N - k) : ℝ) : ℂ) * η ^ k =
      (cb N : ℂ) * ∑ k ∈ range K, (cb k : ℂ) * η ^ k + (cb N : ℂ) * ∑ k ∈ range K, (dk N k : ℂ) * η ^ k := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    have : cb k * cb (N - k) = cb N * cb k + cb N * dk N k := by
      unfold dk gk
      field_simp
      ring
    rw [this]
    push_cast
    ring
  rw [hsplit]
  have htail := norm_boundary_tail_le hη h1 K
  have hdk := norm_sum_dk_mul_pow_le hη h1 hN hK hK'
  have hcNb := cb_le_two_div_sqrt hN
  have hcK := cb_K_le_two_div_sqrt hN hK'
  calc ‖(cb N : ℂ) * ∑ k ∈ range K, (cb k : ℂ) * η ^ k + (cb N : ℂ) * ∑ k ∈ range K, (dk N k : ℂ) * η ^ k -
        (cb N : ℂ) * (1 - η) ^ (-(1 / 2 : ℂ))‖
      = ‖(cb N : ℂ) * (∑ k ∈ range K, (cb k : ℂ) * η ^ k - (1 - η) ^ (-(1 / 2 : ℂ))) +
          (cb N : ℂ) * ∑ k ∈ range K, (dk N k : ℂ) * η ^ k‖ := by congr 1; ring
    _ ≤ ‖(cb N : ℂ) * (∑ k ∈ range K, (cb k : ℂ) * η ^ k - (1 - η) ^ (-(1 / 2 : ℂ)))‖ +
          ‖(cb N : ℂ) * ∑ k ∈ range K, (dk N k : ℂ) * η ^ k‖ := norm_add_le _ _
    _ = cb N * ‖(1 - η) ^ (-(1 / 2 : ℂ)) - ∑ k ∈ range K, (cb k : ℂ) * η ^ k‖ +
          cb N * ‖∑ k ∈ range K, (dk N k : ℂ) * η ^ k‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcN, norm_sub_rev]
    _ ≤ (2 / Real.sqrt N) * (2 / ‖1 - η‖ * (2 / Real.sqrt N)) +
          (2 / Real.sqrt N) * (2 / ‖1 - η‖ * (76 / Real.sqrt N)) := by
        gcongr
        · exact htail.trans (by gcongr)
    _ = 312 / (‖1 - η‖ * (Real.sqrt N * Real.sqrt N)) := by
        field_simp
        ring
    _ = 312 / (‖1 - η‖ * N) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]
    _ ≤ 400 / (‖1 - η‖ * N) := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

end LegendreBoost

end RHTower
