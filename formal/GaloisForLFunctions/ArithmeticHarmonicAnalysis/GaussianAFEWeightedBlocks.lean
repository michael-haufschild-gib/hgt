import GaloisForLFunctions.ArithmeticHarmonicAnalysis.GaussianDualWeightScaleVariation
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-! # Gaussian AFE weights on partial Dirichlet blocks

Finite Abel summation inserts a complex weight at the cost of its endpoint
norm and total discrete variation. The two exact Mellin contours bound this
cost uniformly at the conductor scale.
-/

noncomputable section
open Complex RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Abel's identity with complex weights on a half-open interval. -/
theorem sum_Ico_complex_weight_mul_eq (a w : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    ∑ n ∈ Finset.Ico N M, w n * a n =
      (∑ m ∈ Finset.Ico N M,
        (w m - w (m + 1)) * (∑ n ∈ Finset.Ico N (m + 1), a n)) +
      w M * ∑ n ∈ Finset.Ico N M, a n := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    have hS : ∑ n ∈ Finset.Ico N (M + 1), a n =
        (∑ n ∈ Finset.Ico N M, a n) + a M := Finset.sum_Ico_succ_top hM a
    rw [Finset.sum_Ico_succ_top hM (fun n => w n * a n), ih,
      Finset.sum_Ico_succ_top hM
        (fun m => (w m - w (m + 1)) * (∑ n ∈ Finset.Ico N (m + 1), a n)), hS]
    ring

/-- Complex Abel summation costs exactly endpoint norm plus discrete variation. -/
theorem norm_sum_Ico_complex_weight_mul_le (a w : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M)
    {P : ℝ} (hP : ∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ico N m, a n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ico N M, w n * a n‖ ≤
      P * (‖w M‖ + ∑ m ∈ Finset.Ico N M, ‖w (m + 1) - w m‖) := by
  rw [sum_Ico_complex_weight_mul_eq a w hNM]
  have hterm : ∀ m ∈ Finset.Ico N M,
      ‖(w m - w (m + 1)) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖ ≤
        ‖w (m + 1) - w m‖ * P := by
    intro m hm
    obtain ⟨hmN, hmM⟩ := Finset.mem_Ico.mp hm
    rw [norm_mul, norm_sub_rev (w m)]
    exact mul_le_mul_of_nonneg_left (hP (m + 1) (by omega) (by omega)) (norm_nonneg _)
  have hlast : ‖w M * ∑ n ∈ Finset.Ico N M, a n‖ ≤ ‖w M‖ * P := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hP M hNM le_rfl) (norm_nonneg _)
  calc _ ≤ (∑ m ∈ Finset.Ico N M,
        ‖(w m - w (m + 1)) * (∑ n ∈ Finset.Ico N (m + 1), a n)‖) +
        ‖w M * ∑ n ∈ Finset.Ico N M, a n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    _ ≤ (∑ m ∈ Finset.Ico N M, ‖w (m + 1) - w m‖ * P) + ‖w M‖ * P :=
      add_le_add (Finset.sum_le_sum hterm) hlast
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A uniform scale-Lipschitz bound controls all discrete variation on one block. -/
theorem sum_dualWeight_variation_le {t x D : ℝ} (hD : 0 ≤ D)
    {N M : ℕ} (hM : M ≤ 2 * N)
    (hstep : ∀ n ∈ Finset.Ico N M,
      ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
        smoothAFEZetaDualWeight t ((n : ℝ) * x)‖ ≤ D) :
    (∑ n ∈ Finset.Ico N M,
      ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
        smoothAFEZetaDualWeight t ((n : ℝ) * x)‖) ≤ (N : ℝ) * D := by
  calc _ ≤ ∑ _n ∈ Finset.Ico N M, D := Finset.sum_le_sum hstep
    _ = ((M - N : ℕ) : ℝ) * D := by simp
    _ ≤ (N : ℝ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - N ≤ N by omega)) hD

/-- Above the conductor, the endpoint and variation together decay as `t/(Nx)`. -/
theorem exists_dualWeight_block_cost_le_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), 1 ≤ t → 0 < x → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → M ≤ 2 * N →
      ‖smoothAFEZetaDualWeight t ((M : ℝ) * x)‖ +
        (∑ n ∈ Finset.Ico N M,
          ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
            smoothAFEZetaDualWeight t ((n : ℝ) * x)‖) ≤ C * t / ((N : ℝ) * x) := by
  obtain ⟨K, hK, hend⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  obtain ⟨L, hL, hvar⟩ := exists_norm_dualWeight_sub_le_positive_scale
  refine ⟨2 * (K + L), by positivity, fun t x ht hx N M hN hNM hM => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM0 : (0 : ℝ) < M := hN0.trans_le hNM'
  have hNx : 0 < (N : ℝ) * x := mul_pos hN0 hx
  have hend' : ‖smoothAFEZetaDualWeight t ((M : ℝ) * x)‖ ≤ K * (1 + t) / ((N : ℝ) * x) := by
    have h := hend t (mul_pos hM0 hx)
    rw [abs_of_pos ht0] at h
    refine h.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ hNx (mul_le_mul_of_nonneg_right hNM' hx.le)) (by positivity)
  let D : ℝ := L * (1 + t) * ((N : ℝ) * x) ^ (-2 : ℝ) * x
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hstep : ∀ n ∈ Finset.Ico N M,
      ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
        smoothAFEZetaDualWeight t ((n : ℝ) * x)‖ ≤ D := by
    intro n hn
    obtain ⟨hnN, _⟩ := Finset.mem_Ico.mp hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hn0 : (0 : ℝ) < n := hN0.trans_le hNn
    have h := hvar t (mul_pos hn0 hx) (by push_cast; nlinarith only [hx.le] :
      (n : ℝ) * x ≤ ((n + 1 : ℕ) : ℝ) * x)
    have hdiff : ((n + 1 : ℕ) : ℝ) * x - (n : ℝ) * x = x := by push_cast; ring
    rw [abs_of_pos ht0, hdiff] at h
    refine h.trans ?_
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hNx (mul_le_mul_of_nonneg_right hNn hx.le) (by norm_num))
        (by positivity)) hx.le
  have hsum := sum_dualWeight_variation_le hD hM hstep
  have hND : (N : ℝ) * D = L * (1 + t) / ((N : ℝ) * x) := by
    dsimp only [D]
    rw [Real.rpow_neg hNx.le, Real.rpow_two]
    field_simp [hN0.ne', hx.ne']
  rw [hND] at hsum
  have htwo : 1 + t ≤ 2 * t := by linarith only [ht]
  have hm := mul_le_mul_of_nonneg_left htwo (div_nonneg (add_nonneg hK hL) hNx.le)
  have he : (K + L) / ((N : ℝ) * x) * (2 * t) = 2 * (K + L) * t / ((N : ℝ) * x) := by ring
  rw [he] at hm
  calc _ ≤ K * (1 + t) / ((N : ℝ) * x) + L * (1 + t) / ((N : ℝ) * x) :=
      add_le_add hend' hsum
    _ = (K + L) / ((N : ℝ) * x) * (1 + t) := by ring
    _ ≤ _ := hm

/-- Below the conductor, the negative contour bounds both endpoint and variation by a constant. -/
theorem exists_dualWeight_block_cost_le_low :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), 1 ≤ t → 0 < x → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → M ≤ 2 * N → (N : ℝ) * x ≤ t →
      ‖smoothAFEZetaDualWeight t ((M : ℝ) * x)‖ +
        (∑ n ∈ Finset.Ico N M,
          ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
            smoothAFEZetaDualWeight t ((n : ℝ) * x)‖) ≤ C := by
  obtain ⟨K, hK, hend⟩ := exists_norm_smoothAFEZetaDualWeight_sub_one_le_conductor
    (δ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨L, hL, hvar⟩ := exists_norm_dualWeight_sub_le_negative_scale
    (δ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨1 + 2 * K + L, by positivity, fun t x ht hx N M hN hNM hM hNxle => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM0 : (0 : ℝ) < M := hN0.trans_le hNM'
  have hNx : 0 < (N : ℝ) * x := mul_pos hN0 hx
  have hMt : (M : ℝ) * x ≤ 2 * t := by
    have hMN : (M : ℝ) ≤ 2 * N := by exact_mod_cast hM
    have hm := mul_le_mul_of_nonneg_right hMN hx.le
    linarith only [hm, hNxle]
  have hpow : ((M : ℝ) * x) ^ (1 / 4 : ℝ) ≤ 2 * t ^ (1 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) hMt (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) ht0.le]
    have hc : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hend' : ‖smoothAFEZetaDualWeight t ((M : ℝ) * x)‖ ≤ 1 + 2 * K := by
    have h := hend t (mul_pos hM0 hx)
    rw [abs_of_pos ht0, max_eq_right ht] at h
    have hc : K * ((M : ℝ) * x) ^ (1 / 4 : ℝ) / t ^ (1 / 4 : ℝ) ≤ 2 * K := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_left hpow hK]
    have htri := norm_add_le (smoothAFEZetaDualWeight t ((M : ℝ) * x) - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at htri
    linarith only [htri, h, hc]
  let D : ℝ := L * ((N : ℝ) * x) ^ (-(3 / 4) : ℝ) / t ^ (1 / 4 : ℝ) * x
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hstep : ∀ n ∈ Finset.Ico N M,
      ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
        smoothAFEZetaDualWeight t ((n : ℝ) * x)‖ ≤ D := by
    intro n hn
    obtain ⟨hnN, _⟩ := Finset.mem_Ico.mp hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hn0 : (0 : ℝ) < n := hN0.trans_le hNn
    have h := hvar t (mul_pos hn0 hx) (by push_cast; nlinarith only [hx.le] :
      (n : ℝ) * x ≤ ((n + 1 : ℕ) : ℝ) * x)
    have hdiff : ((n + 1 : ℕ) : ℝ) * x - (n : ℝ) * x = x := by push_cast; ring
    rw [abs_of_pos ht0, max_eq_right ht, hdiff,
      show (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) by norm_num] at h
    refine h.trans ?_
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hNx (mul_le_mul_of_nonneg_right hNn hx.le) (by norm_num)) hL)
        (by positivity)) hx.le
  have hsum := sum_dualWeight_variation_le hD hM hstep
  have hND : (N : ℝ) * D = L * ((N : ℝ) * x) ^ (1 / 4 : ℝ) / t ^ (1 / 4 : ℝ) := by
    have he : ((N : ℝ) * x) * ((N : ℝ) * x) ^ (-(3 / 4) : ℝ) =
        ((N : ℝ) * x) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_one_add' hNx.le (by norm_num)]
      norm_num
    dsimp only [D]
    calc _ = L * (((N : ℝ) * x) * ((N : ℝ) * x) ^ (-(3 / 4) : ℝ)) /
          t ^ (1 / 4 : ℝ) := by ring
      _ = _ := by rw [he]
  have hNDle : (N : ℝ) * D ≤ L := by
    rw [hND, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hNx.le hNxle (by norm_num)) hL
  linarith only [hend', hsum, hNDle]

/-- The exact complex dual weight has uniformly bounded Abel cost at the conductor scale. -/
theorem exists_dualWeight_block_cost_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), 1 ≤ t → 0 < x → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → M ≤ 2 * N →
      ‖smoothAFEZetaDualWeight t ((M : ℝ) * x)‖ +
        (∑ n ∈ Finset.Ico N M,
          ‖smoothAFEZetaDualWeight t (((n + 1 : ℕ) : ℝ) * x) -
            smoothAFEZetaDualWeight t ((n : ℝ) * x)‖) ≤
        C * min 1 (t / ((N : ℝ) * x)) := by
  obtain ⟨A, hA, hlow⟩ := exists_dualWeight_block_cost_le_low
  obtain ⟨B, hB, hhigh⟩ := exists_dualWeight_block_cost_le_high
  refine ⟨A + B, add_nonneg hA hB, fun t x ht hx N M hN hNM hM => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNx : 0 < (N : ℝ) * x := mul_pos hN0 hx
  by_cases hsmall : (N : ℝ) * x ≤ t
  · have hratio : 1 ≤ t / ((N : ℝ) * x) := (le_div_iff₀ hNx).2 (by simpa using hsmall)
    rw [min_eq_left hratio, mul_one]
    exact (hlow t x ht hx N M hN hNM hM hsmall).trans (le_add_of_nonneg_right hB)
  · have hratio : t / ((N : ℝ) * x) ≤ 1 := (div_le_one hNx).2 (le_of_lt (lt_of_not_ge hsmall))
    rw [min_eq_right hratio, ← mul_div_assoc]
    refine (hhigh t x ht hx N M hN hNM hM).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (by linarith only [ht])) hNx.le

/-- The real Gaussian cutoff inserts into a block at cost `min(1,x/N)`. -/
theorem exists_norm_sum_directWeight_mul_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ), 0 < x → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → ∀ (a : ℕ → ℂ) (P : ℝ),
      (∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ico N m, a n‖ ≤ P) →
      ‖∑ n ∈ Finset.Ico N M, a n * smoothAFECutoff ((n : ℝ) / x)‖ ≤
        P * (C * min 1 (x / (N : ℝ))) := by
  obtain ⟨K, hK, htail⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) zero_lt_one
  refine ⟨1 + K, by positivity, fun x hx N M hN hNM a P hP => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hP0 : 0 ≤ P := by
    have h := hP N le_rfl hNM
    simpa only [Finset.Ico_self, Finset.sum_empty, norm_zero] using h
  let w : ℕ → ℝ := fun n => (smoothAFECutoff ((n : ℝ) / x)).re
  have heq : ∀ n, N ≤ n → (w n : ℂ) = smoothAFECutoff ((n : ℝ) / x) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply Complex.ext
    · simp only [w, Complex.ofReal_re]
    · simp only [Complex.ofReal_im, smoothAFECutoff_im_eq_zero (div_pos hn0 hx)]
  have hanti : ∀ n, N ≤ n → n < M → w (n + 1) ≤ w n := by
    intro n hn _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact smoothAFECutoff_re_antitoneOn
      (by change 0 < (n : ℝ) / x; positivity)
      (by change 0 < ((n + 1 : ℕ) : ℝ) / x; positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hx.le)
  have hab := RHTower.Sieve.abel_block_bound a w N M hNM
    (smoothAFECutoff_re_nonneg (div_pos hM0 hx)) hanti P hP
  have hsum : (∑ n ∈ Finset.Ico N M, a n * smoothAFECutoff ((n : ℝ) / x)) =
      ∑ n ∈ Finset.Ico N M, (w n : ℂ) * a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [heq n (Finset.mem_Ico.mp hn).1, mul_comm]
  rw [hsum]
  refine hab.trans (mul_le_mul_of_nonneg_left ?_ hP0)
  have hw1 : w N ≤ 1 := smoothAFECutoff_re_le_one (div_pos hN0 hx)
  have hwK : w N ≤ K * (x / (N : ℝ)) := by
    have h := (Complex.re_le_norm (smoothAFECutoff ((N : ℝ) / x))).trans
      (htail (div_pos hN0 hx))
    rw [Real.rpow_neg_one, inv_div] at h
    exact h
  by_cases hr : x / (N : ℝ) ≤ 1
  · rw [min_eq_right hr]
    exact hwK.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hr)), mul_one]
    exact hw1.trans (le_add_of_nonneg_right hK)

/-- The exact complex dual weight inserts into a block at cost `min(1,t/(Nx))`. -/
theorem exists_norm_sum_dualWeight_mul_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), 1 ≤ t → 0 < x → ∀ N M : ℕ,
      1 ≤ N → N ≤ M → M ≤ 2 * N → ∀ (a : ℕ → ℂ) (P : ℝ),
      (∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ico N m, a n‖ ≤ P) →
      ‖∑ n ∈ Finset.Ico N M, a n * smoothAFEZetaDualWeight t ((n : ℝ) * x)‖ ≤
        P * (C * min 1 (t / ((N : ℝ) * x))) := by
  obtain ⟨C, hC, hcost⟩ := exists_dualWeight_block_cost_le
  refine ⟨C, hC, fun t x ht hx N M hN hNM hM a P hP => ?_⟩
  have hP0 : 0 ≤ P := by
    have h := hP N le_rfl hNM
    simpa only [Finset.Ico_self, Finset.sum_empty, norm_zero] using h
  have hab := norm_sum_Ico_complex_weight_mul_le a
    (fun n => smoothAFEZetaDualWeight t ((n : ℝ) * x)) hNM hP
  have he : (∑ n ∈ Finset.Ico N M, a n * smoothAFEZetaDualWeight t ((n : ℝ) * x)) =
      ∑ n ∈ Finset.Ico N M, smoothAFEZetaDualWeight t ((n : ℝ) * x) * a n := by
    apply Finset.sum_congr rfl
    intro n _
    exact mul_comm _ _
  rw [he]
  exact hab.trans (mul_le_mul_of_nonneg_left (hcost t x ht hx N M hN hNM hM) hP0)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_sum_Ico_complex_weight_mul_le

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_dualWeight_block_cost_le_high

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_dualWeight_block_cost_le

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_sum_directWeight_mul_le
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_sum_dualWeight_mul_le
