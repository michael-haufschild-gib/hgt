import GaloisForLFunctions.RHTower.ZetaGaussianZeroSumTests

/-!
# The main term of `Σ_ρ m_ρ ζ'(ρ) r^ρ g_T(ρ)`

With `U = log T + 1`, `ℓ = (Λ · log) ⋆ 1` and `W_T(y) = e^{−4π²y²/T²}`:

* (`exists_abs_tsum_logVM_leftKernel_sub_le`) for `N ≥ TU/r`,
  `Σ_n ℓ(n) J_T(nr) = Σ_{n ≤ N} ℓ(n) 2cos(2πnr) W_T(nr) + O(TU)`.  For `nr ≤ TU` the kernel is
  `2cos(2πy) W_T(y) + O(y/T² + 1/T)`; beyond, both are `O(T²/y²) = U⁻² O(min(1, (TU/y)²))`, and
  the layer bound sums each part to `O(TU)` (using `U³ ≤ 27eT`).
* (`exists_abs_re_zeroSum_deriv_sub_cos_le`) over the zeros of `[−½, 11/10] × [t₀, Y]`,
  `Re Σ m_ρ ζ'(ρ) r^ρ g_T(ρ) = r Σ_{n ≤ N} ℓ(n) cos(2πnr) W_T(nr) + O(TU)`.
* (`exists_re_zeroSum_deriv_natCast_ge`) for an integer `r = p ≥ 1` this is
  `≥ (e^{−4π²}/32) T log²(T/p) − O(TU)`;
* (`exists_abs_re_zeroSum_deriv_div_le`) for `r = p/q` with `q ∤ p` it is `O(TU)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

theorem logVM_zero : logVM 0 = 0 := by simp [logVM]

theorem sum_logVM_le (m : ℕ) :
    ∑ a ∈ Finset.Icc 1 m, logVM a ≤ 1 * m * (Real.log m + 1) ^ 2 := by
  have h : ∀ a ∈ Finset.Icc 1 m, logVM a ≤ (Real.log m + 1) ^ 2 := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast h1
    have hla : 0 ≤ Real.log a := Real.log_natCast_nonneg a
    have hle : Real.log a ≤ Real.log m := Real.log_le_log ha0 (by exact_mod_cast h2)
    calc logVM a ≤ Real.log a ^ 2 := logVM_le_log_sq a
      _ ≤ (Real.log m + 1) ^ 2 := pow_le_pow_left₀ hla (by linarith) 2
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- `(log T + 1)³ ≤ 27 e T` for `T ≥ 1`. -/
theorem log_add_one_pow_three_le {T : ℝ} (hT : 1 ≤ T) :
    (Real.log T + 1) ^ 3 ≤ 27 * Real.exp 1 * T := by
  have hT0 : 0 < T := by linarith
  have he : Real.log T + 1 = Real.log (Real.exp 1 * T) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hT0.ne', Real.log_exp]; ring
  have hx : 0 ≤ Real.exp 1 * T := by positivity
  have h0 : 0 ≤ Real.log T + 1 := by linarith [Real.log_nonneg hT]
  have h1 := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < ((3 : ℕ) : ℝ)⁻¹)
  rw [← he] at h1
  have h2 := pow_le_pow_left₀ h0 h1 3
  rw [div_pow, Real.rpow_inv_natCast_pow hx (by norm_num)] at h2
  refine h2.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- `W_T(y) ≤ T²/y²`. -/
theorem gaussW_le_sq_div {T y : ℝ} (hT : 0 < T) (hy : 0 < y) : gaussW T y ≤ T ^ 2 / y ^ 2 := by
  have h := exp_neg_sq_mul_sq_le_one (2 * Real.pi * y / T)
  rw [← gaussW_eq T y hT.ne'] at h
  have hg := gaussW_pos T y
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have e : (2 * Real.pi * y / T) ^ 2 = (2 * Real.pi) ^ 2 * (y ^ 2 / T ^ 2) := by
    field_simp
  rw [e] at h
  have h2 : gaussW T y * (y ^ 2 / T ^ 2) ≤ 1 := by
    have hq : 0 ≤ y ^ 2 / T ^ 2 := by positivity
    have : gaussW T y * (y ^ 2 / T ^ 2) ≤ gaussW T y * ((2 * Real.pi) ^ 2 * (y ^ 2 / T ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hq hpi) hg.le
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h3 : gaussW T y * y ^ 2 = gaussW T y * (y ^ 2 / T ^ 2) * T ^ 2 := by field_simp
  rw [h3]
  calc gaussW T y * (y ^ 2 / T ^ 2) * T ^ 2 ≤ 1 * T ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = T ^ 2 := one_mul _

/-- The indicator of `u ≤ 1`, a weight `≤ min(1, u⁻²)`. -/
def nearInd (u : ℝ) : ℝ := if u ≤ 1 then 1 else 0

theorem nearInd_nonneg (u : ℝ) : 0 ≤ nearInd u := by unfold nearInd; split_ifs <;> norm_num

theorem nearInd_le_one (u : ℝ) : nearInd u ≤ 1 := by unfold nearInd; split_ifs <;> norm_num

theorem nearInd_mul_sq_le (u : ℝ) (hu : 0 < u) : nearInd u * u ^ 2 ≤ 1 := by
  unfold nearInd
  split_ifs with h
  · rw [one_mul]; nlinarith
  · simp

/-- `min(1, u⁻²) = u⁻²` for `u ≥ 1`. -/
theorem decayProfile_of_one_le {u : ℝ} (hu : 1 ≤ u) : decayProfile u = (u ^ 2)⁻¹ := by
  unfold decayProfile
  exact min_eq_right (inv_le_one_of_one_le₀ (one_le_pow₀ hu))

/-- **Pointwise comparison of the kernel with the cosine.** For `n ≥ 1`, `X = TU/r ≤ N`:
`|ℓ(n) J_T(nr) − 1_{n ≤ N} ℓ(n) 2cos(2πnr) W_T(nr)| ≤ ℓ(n) (C₁ (U+1)/T 1_{n ≤ X} + C₂ U⁻² min(1, (X/n)²))`. -/
theorem abs_logVM_leftKernel_sub_le {C₁ Cs T U r : ℝ} (hC₁0 : 0 ≤ C₁) (hCs0 : 0 ≤ Cs)
    (hC₁ : ∀ y : ℝ, 0 ≤ y → |leftKernel T y - 2 * Real.cos (2 * Real.pi * y) *
      Real.exp (-(4 * Real.pi ^ 2 * y ^ 2 / T ^ 2))| ≤ C₁ * (y / T ^ 2 + 1 / T))
    (hCs : ∀ y : ℝ, 0 < y → |leftKernel T y| ≤ Cs * T ^ 2 / y ^ 2)
    (hT : 0 < T) (hU : 0 < U) (hr : 0 < r) {N : ℕ} (hN : T * U / r ≤ N) {n : ℕ} (hn : 1 ≤ n) :
    |logVM n * leftKernel T (n * r) - (if n ∈ Finset.Icc 1 N then
        logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)) else 0)| ≤
      logVM n * (C₁ * ((U + 1) / T) * nearInd (n / (T * U / r)) +
        (Cs + 2) / U ^ 2 * decayProfile (n / (T * U / r))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < (n : ℝ) * r := by positivity
  have hX0 : 0 < T * U / r := by positivity
  have hℓ := logVM_nonneg n
  have hW : 2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r) =
      2 * Real.cos (2 * Real.pi * (n * r)) * Real.exp (-(4 * Real.pi ^ 2 * (n * r) ^ 2 / T ^ 2)) := by
    rw [gaussW, mul_assoc (2 * Real.pi)]
  have hnear0 := nearInd_nonneg ((n : ℝ) / (T * U / r))
  have hdec0 := decayProfile_nonneg ((n : ℝ) / (T * U / r))
  rcases le_or_gt ((n : ℝ) / (T * U / r)) 1 with hnX | hnX
  · -- near: `nr ≤ TU`, and `n ≤ N`
    have hnX' : (n : ℝ) ≤ T * U / r := (div_le_one hX0).mp hnX
    have hnN : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hn, by exact_mod_cast hnX'.trans hN⟩
    have hyTU : (n : ℝ) * r ≤ T * U := (le_div_iff₀ hr).mp hnX'
    rw [if_pos hnN, ← mul_sub, abs_mul, abs_of_nonneg hℓ, hW]
    have hk := hC₁ (n * r) hy.le
    have hsmall : (n : ℝ) * r / T ^ 2 + 1 / T ≤ (U + 1) / T := by
      have : (n : ℝ) * r / T ^ 2 ≤ U / T := by
        rw [div_le_div_iff₀ (by positivity) hT]; nlinarith
      rw [add_div]; linarith
    have hnear : nearInd ((n : ℝ) / (T * U / r)) = 1 := by unfold nearInd; rw [if_pos hnX]
    rw [hnear, mul_one]
    apply mul_le_mul_of_nonneg_left _ hℓ
    have hfar : 0 ≤ (Cs + 2) / U ^ 2 * decayProfile ((n : ℝ) / (T * U / r)) := by positivity
    calc _ ≤ C₁ * ((n : ℝ) * r / T ^ 2 + 1 / T) := hk
      _ ≤ C₁ * ((U + 1) / T) := mul_le_mul_of_nonneg_left hsmall hC₁0
      _ ≤ _ := by linarith
  · -- far: both terms are `O(T²/y²)`
    have hdec : (Cs + 2) / U ^ 2 * decayProfile ((n : ℝ) / (T * U / r)) =
        (Cs + 2) * T ^ 2 / ((n : ℝ) * r) ^ 2 := by
      rw [decayProfile_of_one_le hnX.le]
      field_simp
    have hJ := hCs (n * r) hy
    have hWb : |2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)| ≤ 2 * T ^ 2 / ((n : ℝ) * r) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (gaussW_pos T _)]
      have h1 := Real.abs_cos_le_one (2 * Real.pi * n * r)
      have h2 := gaussW_le_sq_div hT hy
      have h3 := gaussW_pos T ((n : ℝ) * r)
      calc 2 * |Real.cos (2 * Real.pi * n * r)| * gaussW T (n * r) ≤ 2 * 1 * (T ^ 2 / ((n : ℝ) * r) ^ 2) := by
            gcongr
        _ = _ := by ring
    have hsum : |leftKernel T (n * r)| + |2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)| ≤
        (Cs + 2) * T ^ 2 / ((n : ℝ) * r) ^ 2 := by
      have e : (Cs + 2) * T ^ 2 / ((n : ℝ) * r) ^ 2 =
          Cs * T ^ 2 / ((n : ℝ) * r) ^ 2 + 2 * T ^ 2 / ((n : ℝ) * r) ^ 2 := by ring
      rw [e]; exact add_le_add hJ hWb
    have hbound : |logVM n * leftKernel T (n * r) - (if n ∈ Finset.Icc 1 N then
        logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)) else 0)| ≤
        logVM n * (|leftKernel T (n * r)| +
          |2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)|) := by
      split_ifs
      · rw [← mul_sub, abs_mul, abs_of_nonneg hℓ]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) hℓ
      · rw [sub_zero, abs_mul, abs_of_nonneg hℓ]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hℓ
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hℓ)
    rw [hdec]
    have : 0 ≤ C₁ * ((U + 1) / T) * nearInd ((n : ℝ) / (T * U / r)) := by positivity
    linarith

/-- **Kernel to cosine.** With `U = log T + 1` and `N ≥ TU/r`:
`|Σ_n ℓ(n) J_T(nr) − Σ_{n ≤ N} ℓ(n) 2cos(2πnr) W_T(nr)| ≤ C T U`. -/
theorem exists_abs_tsum_logVM_leftKernel_sub_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → r ≤ T → ∀ N : ℕ, T * (Real.log T + 1) / r ≤ N →
      |(∑' n : ℕ, (if n = 0 then 0 else logVM n * leftKernel T (n * r))) -
        ∑ n ∈ Finset.Icc 1 N, logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r))| ≤
        C * T * (Real.log T + 1) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_leftKernel_sub_le
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_leftKernel_le_sq
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_abs_leftKernel_le_decay
  set L : ℝ := 2 + |Real.log r| with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨48 * L ^ 2 * (54 * Real.exp 1 * C₁ + (Cs + 2)) / r, by positivity,
    fun T hT hrT N hN => ?_⟩
  have hT0 : 0 < T := by linarith
  set U : ℝ := Real.log T + 1 with hU
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  set X : ℝ := T * U / r with hX
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ hr]; nlinarith
  have hlogX : Real.log X + 1 ≤ L * U := by
    have h1 : Real.log X = Real.log T + Real.log U - Real.log r := by
      rw [hX, Real.log_div (by positivity) hr.ne', Real.log_mul hT0.ne' hU0.ne']
    have h2 : Real.log U ≤ U - 1 := Real.log_le_sub_one_of_pos hU0
    have h3 : -Real.log r ≤ |Real.log r| := neg_le_abs _
    have h5 : |Real.log r| ≤ |Real.log r| * U := le_mul_of_one_le_right (abs_nonneg _) hU1
    rw [h1, hL]; nlinarith
  set e : ℕ → ℝ := fun n => logVM n * (C₁ * ((U + 1) / T) * nearInd (n / X) +
      (Cs + 2) / U ^ 2 * decayProfile (n / X)) with he
  set a : ℕ → ℝ := fun n => logVM n * leftKernel T (n * r) with ha
  set b : ℕ → ℝ := fun n => if n ∈ Finset.Icc 1 N then
      logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)) else 0 with hb
  have hite : (fun n : ℕ => if n = 0 then 0 else logVM n * leftKernel T (n * r)) = a := by
    funext n
    split_ifs with h
    · subst h; simp [ha, logVM_zero]
    · rfl
  have he0 : ∀ n, 0 ≤ e n := fun n => mul_nonneg (logVM_nonneg n)
    (add_nonneg (mul_nonneg (by positivity) (nearInd_nonneg _))
      (mul_nonneg (by positivity) (decayProfile_nonneg _)))
  have hpt : ∀ n : ℕ, |a n - b n| ≤ e n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha, hb, logVM_zero, he0 0]
    exact abs_logVM_leftKernel_sub_le hC₁0 hCs0 (hC₁ T hT) (hCs T hT) hT0 hU0 hr hN hn
  -- summability
  obtain ⟨hsumA, -⟩ := tsum_mul_abs_leftKernel_le (c := logVM) logVM_nonneg logVM_zero zero_le_one
    le_rfl sum_logVM_le hCJ0 hCJ hT hr ((one_le_div hr).mpr hrT)
  have hA : Summable a := by
    refine Summable.of_norm (hsumA.congr fun n => ?_)
    simp only [ha, Real.norm_eq_abs, abs_mul, abs_of_nonneg (logVM_nonneg n)]
  have hB : Summable b := summable_of_ne_finset_zero (s := Finset.Icc 1 N) fun n hn => by
    simp only [hb, if_neg hn]
  have hBsum : ∑' n, b n = ∑ n ∈ Finset.Icc 1 N,
      logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N) fun n hn => by simp only [hb, if_neg hn]]
    exact Finset.sum_congr rfl fun n hn => by simp only [hb, if_pos hn]
  -- partial sums of the error
  have hpart : ∀ M : ℕ, ∑ n ∈ Finset.range M, |a n - b n| ≤
      (C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2) * (48 * 1 * X * (Real.log X + 1) ^ 2) := by
    intro M
    have hsub : ∑ n ∈ Finset.range M, |a n - b n| ≤ ∑ n ∈ Finset.Icc 1 M, e n := by
      refine (Finset.sum_le_sum fun n _ => hpt n).trans ?_
      rw [Finset.range_eq_Ico]
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp
      rw [Finset.sum_eq_sum_Ico_succ_bot hM]
      have he00 : e 0 = 0 := by simp [he, logVM_zero]
      rw [he00, zero_add]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => by rw [Finset.mem_Ico] at hn; rw [Finset.mem_Icc]; omega)
        (fun n _ _ => he0 n)
    refine hsub.trans ?_
    have hsplit : ∑ n ∈ Finset.Icc 1 M, e n =
        C₁ * ((U + 1) / T) * ∑ n ∈ Finset.Icc 1 M, logVM n * nearInd (n / X) +
          (Cs + 2) / U ^ 2 * ∑ n ∈ Finset.Icc 1 M, logVM n * decayProfile (n / X) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by simp only [he]; ring
    rw [hsplit]
    have h1 := sum_mul_weight_le_layers logVM_nonneg zero_le_one le_rfl sum_logVM_le
      nearInd_le_one nearInd_mul_sq_le hX1 M
    have h2 := sum_mul_weight_le_layers logVM_nonneg zero_le_one le_rfl sum_logVM_le
      decayProfile_le_one decayProfile_mul_sq_le hX1 M
    have hc1 : 0 ≤ C₁ * ((U + 1) / T) := by positivity
    have hc2 : 0 ≤ (Cs + 2) / U ^ 2 := by positivity
    calc C₁ * ((U + 1) / T) * ∑ n ∈ Finset.Icc 1 M, logVM n * nearInd (n / X) +
          (Cs + 2) / U ^ 2 * ∑ n ∈ Finset.Icc 1 M, logVM n * decayProfile (n / X)
        ≤ C₁ * ((U + 1) / T) * (48 * 1 * X * (Real.log X + 1) ^ 2) +
          (Cs + 2) / U ^ 2 * (48 * 1 * X * (Real.log X + 1) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)
      _ = _ := by ring
  have hsumD : Summable fun n => |a n - b n| := (hA.sub hB).abs
  have htsum : ∑' n, |a n - b n| ≤
      (C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2) * (48 * 1 * X * (Real.log X + 1) ^ 2) :=
    Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hpart
  -- the arithmetic of the bound
  have hU3 := log_add_one_pow_three_le hT
  have hfinal : (C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2) * (48 * 1 * X * (Real.log X + 1) ^ 2) ≤
      48 * L ^ 2 * (54 * Real.exp 1 * C₁ + (Cs + 2)) / r * T * U := by
    have hlogX0 : 0 ≤ Real.log X + 1 := by linarith [Real.log_nonneg hX1]
    have hcoef : 0 ≤ C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2 := by positivity
    have hsq : (Real.log X + 1) ^ 2 ≤ (L * U) ^ 2 := pow_le_pow_left₀ hlogX0 hlogX 2
    have hC1U : C₁ * (U + 1) * U ^ 3 ≤ 54 * Real.exp 1 * C₁ * T * U := by
      calc C₁ * (U + 1) * U ^ 3 ≤ C₁ * (2 * U) * (27 * Real.exp 1 * T) := by
            gcongr; linarith
        _ = 54 * Real.exp 1 * C₁ * T * U := by ring
    calc (C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2) * (48 * 1 * X * (Real.log X + 1) ^ 2)
        ≤ (C₁ * ((U + 1) / T) + (Cs + 2) / U ^ 2) * (48 * 1 * X * (L * U) ^ 2) := by gcongr
      _ = 48 * L ^ 2 / r * (C₁ * (U + 1) * U ^ 3 + (Cs + 2) * T * U) := by
          rw [hX]; field_simp
      _ ≤ 48 * L ^ 2 / r * (54 * Real.exp 1 * C₁ * T * U + (Cs + 2) * T * U) := by gcongr
      _ = _ := by ring
  rw [hite, ← hBsum, ← hA.tsum_sub hB]
  calc |∑' n, (a n - b n)| = ‖∑' n, (a n - b n)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖a n - b n‖ := norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsumD)
    _ = ∑' n, |a n - b n| := by simp only [Real.norm_eq_abs]
    _ ≤ _ := htsum.trans hfinal

/-- **Rule A with the cosine main term.** For `N ≥ TU/r`,
`|Re Σ m_ρ ζ'(ρ) r^ρ g_T(ρ) − r Σ_{n ≤ N} ℓ(n) cos(2πnr) W_T(nr)| ≤ C T U`. -/
theorem exists_abs_re_zeroSum_deriv_sub_cos_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → r ≤ T → ∀ N : ℕ, T * (Real.log T + 1) / r ≤ N →
      ∀ Y : ℝ, GoodTop T Y →
        |(∑ w ∈ rectZeros bottomHeight Y,
            (mult w : ℂ) * (deriv riemannZeta w * (r : ℂ) ^ w * gaussWeight T w)).re -
          r * ∑ n ∈ Finset.Icc 1 N,
            logVM n * (Real.cos (2 * Real.pi * n * r) * gaussW T (n * r))| ≤
          C * T * (Real.log T + 1) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_abs_re_zeroSum_deriv_gW_sub_le hr
  obtain ⟨CK, hCK0, hCK⟩ := exists_abs_tsum_logVM_leftKernel_sub_le hr
  refine ⟨CA + r / 2 * CK, by positivity, fun T hT hrT N hN Y hY => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hU1 : 1 ≤ Real.log T + 1 := by linarith [Real.log_nonneg hT1]
  have h1 := hCA T hT hrT Y hY
  have h2 := hCK T hT1 hrT N hN
  set Z := (∑ w ∈ rectZeros bottomHeight Y,
    (mult w : ℂ) * (deriv riemannZeta w * (r : ℂ) ^ w * gaussWeight T w)).re
  set S := ∑' n : ℕ, (if n = 0 then 0 else logVM n * leftKernel T (n * r))
  set P := ∑ n ∈ Finset.Icc 1 N, logVM n * (2 * Real.cos (2 * Real.pi * n * r) * gaussW T (n * r))
  have hP : r * ∑ n ∈ Finset.Icc 1 N,
      logVM n * (Real.cos (2 * Real.pi * n * r) * gaussW T (n * r)) = r / 2 * P := by
    simp only [P, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hP]
  have e : Z - r / 2 * P = (Z - r / 2 * S) + r / 2 * (S - P) := by ring
  rw [e]
  calc |(Z - r / 2 * S) + r / 2 * (S - P)| ≤ |Z - r / 2 * S| + |r / 2 * (S - P)| := abs_add_le _ _
    _ = |Z - r / 2 * S| + r / 2 * |S - P| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < r / 2)]
    _ ≤ CA * T + r / 2 * (CK * T * (Real.log T + 1)) := by gcongr
    _ ≤ CA * T * (Real.log T + 1) + r / 2 * (CK * T * (Real.log T + 1)) :=
        add_le_add (le_mul_of_one_le_right (by positivity) hU1) le_rfl
    _ = _ := by ring

/-- **Integer frequencies.** For `p ≥ 1`,
`Re Σ m_ρ ζ'(ρ) p^ρ g_T(ρ) ≥ (e^{−4π²}/32) T log²(T/p) − C T U` once `T ≥ e^{202} p`. -/
theorem exists_re_zeroSum_deriv_natCast_ge {p : ℕ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → Real.exp 202 * p ≤ T → ∀ Y : ℝ, GoodTop T Y →
      Real.exp (-(4 * Real.pi ^ 2)) / 32 * T * Real.log (T / p) ^ 2 - C * T * (Real.log T + 1) ≤
        (∑ w ∈ rectZeros bottomHeight Y,
          (mult w : ℂ) * (deriv riemannZeta w * ((p : ℝ) : ℂ) ^ w * gaussWeight T w)).re := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨C, hC0, hC⟩ := exists_abs_re_zeroSum_deriv_sub_cos_le hp0
  refine ⟨C, hC0, fun T hT hpT Y hY => ?_⟩
  have hT0 : 0 < T := by linarith
  have he1 : (1 : ℝ) ≤ Real.exp 202 := Real.one_le_exp (by norm_num)
  have hpT' : (p : ℝ) ≤ T := le_trans (le_mul_of_one_le_left hp0.le he1) hpT
  have hU1 : 1 ≤ Real.log T + 1 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]
  set N : ℕ := ⌈T * (Real.log T + 1) / p⌉₊ with hN
  have hN1 : T * (Real.log T + 1) / p ≤ N := Nat.le_ceil _
  have hN2 : T / p ≤ N := by
    refine le_trans ?_ hN1
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hT0.le hU1) hp0.le
  have hTp : Real.exp 202 ≤ T / p := by rw [le_div_iff₀ hp0]; exact hpT
  have hmain := sum_logVM_gaussW_ge hp hTp hN2
  have hcos : ∀ n : ℕ, Real.cos (2 * Real.pi * n * (p : ℝ)) = 1 := fun n => by
    rw [show 2 * Real.pi * n * (p : ℝ) = ((n * p : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_nat_mul_two_pi _
  have h := hC T hT hpT' N hN1 Y hY
  simp only [hcos, one_mul] at h
  have hsum : Real.exp (-(4 * Real.pi ^ 2)) / 32 * T * Real.log (T / p) ^ 2 =
      (p : ℝ) * (Real.exp (-(4 * Real.pi ^ 2)) / 32 * (T / p) * Real.log (T / p) ^ 2) := by
    field_simp
  rw [hsum]
  have hm := mul_le_mul_of_nonneg_left hmain hp0.le
  have := (abs_le.mp h).1
  linarith

/-- **Non-integer frequencies.** For `p, q ≥ 1` with `q ∤ p`,
`|Re Σ m_ρ ζ'(ρ) (p/q)^ρ g_T(ρ)| ≤ C T U` for large `T`. -/
theorem exists_abs_re_zeroSum_deriv_div_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hqp : ¬ q ∣ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y,
          (mult w : ℂ) * (deriv riemannZeta w * (((p : ℝ) / q : ℝ) : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  set g := Nat.gcd p q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left q hp
  have hcop : Nat.Coprime (p / g) (q / g) := Nat.coprime_div_gcd_div_gcd hg0
  have hgp : g ∣ p := Nat.gcd_dvd_left p q
  have hgq : g ∣ q := Nat.gcd_dvd_right p q
  have hp' : 0 < p / g := Nat.div_pos (Nat.le_of_dvd hp hgp) hg0
  have hq' : 2 ≤ q / g := by
    have h0 : q / g ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq hgq) hg0).ne'
    have h1 : q / g ≠ 1 := by
      intro h
      have : q = g := by
        have := Nat.div_mul_cancel hgq
        rw [h, one_mul] at this; exact this.symm
      exact hqp (this ▸ hgp)
    exact (Nat.two_le_iff _).mpr ⟨h0, h1⟩
  have hg0' : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hr : ((p : ℝ) / q) = ((p / g : ℕ) : ℝ) / ((q / g : ℕ) : ℝ) := by
    rw [Nat.cast_div hgp hg0', Nat.cast_div hgq hg0']
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  have hr0 : (0 : ℝ) < (p : ℝ) / q := by positivity
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_re_zeroSum_deriv_sub_cos_le hr0
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_sum_logVM_cos_le hp' hq' hcop
  refine ⟨C₁ + (p : ℝ) / q * C₂, by positivity,
    max 2 (max ((p : ℝ) / q) (2 * Real.pi * (p / g : ℕ) / (q / g : ℕ))), fun T hT Y hY => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := by linarith
  have hrT : (p : ℝ) / q ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hphT : 2 * Real.pi * (p / g : ℕ) / (q / g : ℕ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  set N : ℕ := ⌈T * (Real.log T + 1) / ((p : ℝ) / q)⌉₊
  have h1 := hC₁ T hT2 hrT N (Nat.le_ceil _) Y hY
  have h2 := hC₂ T hT1 hphT N
  rw [← hr] at h2
  set Z := (∑ w ∈ rectZeros bottomHeight Y,
    (mult w : ℂ) * (deriv riemannZeta w * (((p : ℝ) / q : ℝ) : ℂ) ^ w * gaussWeight T w)).re
  set P := ∑ n ∈ Finset.Icc 1 N,
    logVM n * (Real.cos (2 * Real.pi * n * ((p : ℝ) / q)) * gaussW T (n * ((p : ℝ) / q)))
  calc |Z| = |(Z - (p : ℝ) / q * P) + (p : ℝ) / q * P| := by ring_nf
    _ ≤ |Z - (p : ℝ) / q * P| + |(p : ℝ) / q * P| := abs_add_le _ _
    _ = |Z - (p : ℝ) / q * P| + (p : ℝ) / q * |P| := by rw [abs_mul, abs_of_pos hr0]
    _ ≤ C₁ * T * (Real.log T + 1) + (p : ℝ) / q * (C₂ * T * (Real.log T + 1)) := by gcongr
    _ = _ := by ring

end

end RHTower.GaussZeroSum
