import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalNonzeroModes

/-!
# Guth–Maynard Lemma 6.2 for `ζ`, in the paper's form

Guth–Maynard (arXiv:2405.20552, Lemma 6.2): for every `t` with `|t| ∼ T₀ ≥ T^ε`,

`|Σ_{m ≠ 0} ĥ_t(mN)| ≪ T₀^{−1/2} ∫_{|u| ⪅ 1} |Σ_{m ⪅ T₀/N} m^{−i(t+u)}| du + O_ε(T^{−100})`.

`cglGM_lemma62_zeta` proves this for the Chen–Gupta–Li bump `h_t(u) = w(u)² u^{it}` (real `w`
supported in `[1,2]`): for every `ε ∈ (0,1]` there is `C` such that for all `T ≥ 1`, `N ≥ 1`,
`T^ε ≤ |t| ≤ T`,

`‖Σ_{m ≠ 0} ĥ_t(mN)‖ ≤ C |t|^{−1/2} ∫_{−T^ε/2}^{T^ε/2} ‖Σ_{m=1}^{M} m^{−i(t+u)}‖ du + C T^{−100}`,
`M = ⌈|t|^{1+ε}/N⌉`.

Mechanism: the explicit bound `norm_cglGMNonzeroModeSum_le` with `U = T^ε/2`, Mellin decay
order `n = ⌈104/ε⌉` (so `U^{−n} M log 2M ≪ T^{−100}`) and Fourier decay order
`j = ⌈104/ε²⌉ + 2` (so the frequencies `|m| > M`, where `mN ≥ |t|^{1+ε}`, cost `≪ T^{−100}`).
For `|t| < 2` the left side is bounded by a constant while `T < 2^{1/ε}`, so the constant is
absorbed into `C T^{−100}`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- `T^{−100} = 1/T^{100}`. -/
theorem rpow_neg_hundred (T : ℝ) (hT : 0 ≤ T) : T ^ (-100 : ℝ) = (T ^ 100)⁻¹ := by
  rw [Real.rpow_neg hT, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `T^{104} ≤ T^a` for `T ≥ 1` and `104 ≤ a`. -/
theorem pow_hundredFour_le_rpow {T a : ℝ} (hT : 1 ≤ T) (ha : 104 ≤ a) : T ^ 104 ≤ T ^ a := by
  rw [show T ^ 104 = T ^ ((104 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  exact Real.rpow_le_rpow_of_exponent_le hT (by exact_mod_cast ha)

/-- The window weight: `c₁/π ≤ (56 B₀/π) |t|^{−1/2}`. -/
theorem cglGMWindowWeight_div_pi_le (w : CGLRealSmoothBump) {t : ℝ} (ht : 0 < |t|) :
    cglGMWindowWeight w t / Real.pi ≤
      56 * cglGMMellinBudget w 0 / Real.pi * |t| ^ (-(1 / 2 : ℝ)) := by
  have hB := cglGMMellinBudget_nonneg w 0
  have h := div_sqrt_half_le (by norm_num : (0 : ℝ) ≤ 28) ht
  rw [Real.rpow_neg (abs_nonneg t), ← Real.sqrt_eq_rpow, cglGMWindowWeight]
  have hpi := Real.pi_pos
  have hs : 0 < Real.sqrt |t| := Real.sqrt_pos.mpr ht
  calc cglGMMellinBudget w 0 * (28 / Real.sqrt (|t| / 2)) / Real.pi
      ≤ cglGMMellinBudget w 0 * (2 * 28 / Real.sqrt |t|) / Real.pi := by gcongr
    _ = 56 * cglGMMellinBudget w 0 / Real.pi * (Real.sqrt |t|)⁻¹ := by
        field_simp; ring

/-- The Mellin tail: `c₂ ≤ 8 · 2^n (B_n + B_{n+2}) T^{−100}` for `U = T^ε/2`, `εn ≥ 104`,
`M ≤ 2T²`. -/
theorem cglGMTailWeight_le_rpow (w : CGLRealSmoothBump) {T ε : ℝ} (hT : 1 ≤ T) {n : ℕ}
    (hn : 104 ≤ ε * n) {M : ℕ} (hM1 : 1 ≤ M) (hM : (M : ℝ) ≤ 2 * T ^ 2) :
    cglGMTailWeight w n (T ^ ε / 2) M ≤
      8 * 2 ^ n * (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) * T ^ (-100 : ℝ) := by
  set B : ℝ := cglGMMellinBudget w n + cglGMMellinBudget w (n + 2) with hB
  have hB0 : 0 ≤ B := add_nonneg (cglGMMellinBudget_nonneg w n) (cglGMMellinBudget_nonneg w _)
  have hT0 : 0 < T := by linarith
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hU : T ^ 104 / 2 ^ n ≤ (T ^ ε / 2) ^ n := by
    rw [div_pow, ← Real.rpow_mul_natCast hT0.le]
    gcongr
    exact pow_hundredFour_le_rpow hT hn
  have hlog : (M : ℝ) * Real.log (2 * M) ≤ 8 * T ^ 4 := by
    have h1 : Real.log (2 * M) ≤ 2 * M := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * M)
      linarith
    have h2 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
    calc (M : ℝ) * Real.log (2 * M) ≤ (2 * T ^ 2) * (2 * (2 * T ^ 2)) := by
          gcongr
          linarith
      _ = 8 * T ^ 4 := by ring
  unfold cglGMTailWeight
  rw [← hB, rpow_neg_hundred T hT0.le]
  calc B / (T ^ ε / 2) ^ n * ((M : ℝ) * Real.log (2 * M))
      ≤ B / (T ^ 104 / 2 ^ n) * (8 * T ^ 4) := by
        gcongr
        · positivity
    _ = 8 * 2 ^ n * B * (T ^ 100)⁻¹ := by
        field_simp
        ring

/-- The frequency tail: for `N M ≥ |t|^{1+ε}`, `|t| ≥ T^ε`, `ε² j ≥ 104`, `M ≤ 2T²`,
`tail_j ≤ 8 · 2^j A_j Z T^{−100}`. -/
theorem cglGMFrequencyTailWeight_le_rpow (w : CGLSmoothBump) {T ε t N : ℝ} (hT : 1 ≤ T)
    (hε : 0 < ε) (hN : 1 ≤ N) (htT : T ^ ε ≤ |t|) (ht1 : 1 ≤ |t|) {M : ℕ} (hM1 : 1 ≤ M)
    (hMx : |t| ^ (1 + ε) / N ≤ M) (hM : (M : ℝ) ≤ 2 * T ^ 2) {j : ℕ} (hj : 2 ≤ j)
    (hjε : 104 ≤ ε ^ 2 * j) :
    cglGMFrequencyTailWeight w j t N M ≤
      8 * 2 ^ j * (cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j) *
        cglGMInverseSquareMass * T ^ (-100 : ℝ) := by
  set A : ℝ := cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j with hA
  have hA0 : 0 ≤ A := div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w j) (by positivity)
  have hZ := cglGMInverseSquareMass_nonneg
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < |t| := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hN0 : 0 < N := by linarith
  -- `|t|^ε ≥ T^{ε²}`
  have hte : T ^ (ε ^ 2) ≤ |t| ^ ε := by
    rw [sq, Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow (by positivity) htT hε.le
  -- `N M ≥ |t| |t|^ε`
  have hNM : |t| * |t| ^ ε ≤ N * M := by
    rw [← Real.rpow_one_add' ht0.le (by linarith), add_comm] at *
    have := (div_le_iff₀ hN0).mp hMx
    rw [Real.rpow_add ht0, Real.rpow_one] at this
    linarith
  -- the ratio `(1+|t|)/(NM) ≤ 2/T^{ε²}`
  have hratio : (1 + |t|) / (N * M) ≤ 2 / T ^ (ε ^ 2) := by
    have hTe : 0 < T ^ (ε ^ 2) := Real.rpow_pos_of_pos hT0 _
    rw [div_le_div_iff₀ (by positivity) hTe]
    calc (1 + |t|) * T ^ (ε ^ 2) ≤ (2 * |t|) * |t| ^ ε := by
          gcongr
          linarith
      _ = 2 * (|t| * |t| ^ ε) := by ring
      _ ≤ 2 * (N * M) := by gcongr
  have hpow : ((1 + |t|) / (N * M)) ^ j ≤ 2 ^ j / T ^ 104 := by
    calc ((1 + |t|) / (N * M)) ^ j ≤ (2 / T ^ (ε ^ 2)) ^ j := by gcongr
      _ = 2 ^ j / T ^ (ε ^ 2 * j) := by
          rw [div_pow, Real.rpow_mul_natCast hT0.le]
      _ ≤ 2 ^ j / T ^ 104 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_hundredFour_le_rpow hT hjε)
  -- `(1+|t|)^j/(N^j M^{j−2}) = M² ((1+|t|)/(NM))^j`
  have hsplit : (1 + |t|) ^ j / (N ^ j * (M : ℝ) ^ (j - 2)) =
      (M : ℝ) ^ 2 * ((1 + |t|) / (N * M)) ^ j := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_sub_cancel_left, div_pow, mul_pow, pow_add]
    field_simp
  have hM2 : (M : ℝ) ^ 2 ≤ 4 * T ^ 4 := by
    calc (M : ℝ) ^ 2 ≤ (2 * T ^ 2) ^ 2 := by gcongr
      _ = 4 * T ^ 4 := by ring
  unfold cglGMFrequencyTailWeight
  rw [rpow_neg_hundred T hT0.le, mul_div_assoc, ← hA, hsplit]
  calc 2 * (A * ((M : ℝ) ^ 2 * ((1 + |t|) / (N * M)) ^ j)) * cglGMInverseSquareMass
      ≤ 2 * (A * ((4 * T ^ 4) * (2 ^ j / T ^ 104))) * cglGMInverseSquareMass := by
        gcongr
    _ = 8 * 2 ^ j * A * cglGMInverseSquareMass * (T ^ 100)⁻¹ := by
        field_simp
        ring

/-- A uniform bound for all `t`: `‖Σ_{m≠0} ĥ_t(mN)‖ ≤ 2A₀ + tail₂(M = 1)`. -/
theorem norm_cglGMNonzeroModeSum_le_crude (w : CGLSmoothBump) {t N : ℝ} (hN : 1 ≤ N) :
    ‖cglGMNonzeroModeSum w N t‖ ≤
      2 * cglSmoothBumpHtAllOrderBudget w 0 + cglGMFrequencyTailWeight w 2 t N 1 := by
  have hN0 : 0 < N := by linarith
  set f : ℤ → ℂ := fun m => 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ((m : ℝ) * N) with hf
  have hsplit := tsum_puncturedFrequency_eq_sum_add_tail f
    (summable_fourier_cglSmoothBumpHt_int w t N hN0) 1
  have htail := norm_frequencyTail_le w t N hN0 le_rfl (le_refl 2)
  have h0 : ∀ ξ : ℝ, ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤ cglSmoothBumpHtAllOrderBudget w 0 := by
    intro ξ
    simpa using cglSmoothBumpHt_allOrder_fourier_decay w 0 t ξ
  unfold cglGMNonzeroModeSum
  change ‖∑' m : CGLProposition51PuncturedFrequency, f m‖ ≤ _
  rw [hsplit, Finset.Icc_self, Finset.sum_singleton]
  calc _ ≤ ‖f ((1 : ℕ) : ℤ)‖ + ‖f (-((1 : ℕ) : ℤ))‖ +
        ‖∑' k : ℕ, (f ((k + 1 + 1 : ℕ) : ℤ) + f (-((k + 1 + 1 : ℕ) : ℤ)))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
        have := h0 ((((1 : ℕ) : ℤ) : ℝ) * N)
        have := h0 ((((-((1 : ℕ) : ℤ)) : ℤ) : ℝ) * N)
        simp only [hf] at *
        linarith

/-- For `|t| ≤ 2` and `N ≥ 1` the crude bound is a constant. -/
theorem cglGMFrequencyTailWeight_two_le (w : CGLSmoothBump) {t N : ℝ} (hN : 1 ≤ N)
    (ht : |t| ≤ 2) :
    cglGMFrequencyTailWeight w 2 t N 1 ≤
      18 * (cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2) * cglGMInverseSquareMass := by
  have hA0 : 0 ≤ cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 :=
    div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w 2) (by positivity)
  have hZ := cglGMInverseSquareMass_nonneg
  unfold cglGMFrequencyTailWeight
  have h1 : (1 + |t|) ^ 2 ≤ 9 := by nlinarith [abs_nonneg t]
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  simp only [Nat.cast_one, one_pow, mul_one, Nat.sub_self, pow_zero]
  calc 2 * (cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 / N ^ 2) *
        cglGMInverseSquareMass
      ≤ 2 * (cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 * 9 / 1) *
          cglGMInverseSquareMass := by gcongr
    _ = _ := by ring

/-- **Guth–Maynard Lemma 6.2 for `ζ`.** For every `ε ∈ (0,1]` there is `C ≥ 0` such that for
all `T ≥ 1`, `N ≥ 1` and `T^ε ≤ |t| ≤ T`,
`‖Σ_{m ≠ 0} ĥ_t(mN)‖ ≤ C |t|^{−1/2} ∫_{−T^ε/2}^{T^ε/2} ‖Σ_{m=1}^{M} m^{−i(t+u)}‖ du + C T^{−100}`
with `M = ⌈|t|^{1+ε}/N⌉`. -/
theorem cglGM_lemma62_zeta (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T t : ℝ) (N : ℕ), 1 ≤ T → 1 ≤ N → T ^ ε ≤ |t| → |t| ≤ T →
      ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤
        C * |t| ^ (-(1 / 2 : ℝ)) *
            (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
              ‖cglGMHeadPoly ⌈|t| ^ (1 + ε) / N⌉₊ (t + u)‖) +
          C * T ^ (-100 : ℝ) := by
  set n : ℕ := ⌈104 / ε⌉₊ with hn
  set j : ℕ := ⌈104 / ε ^ 2⌉₊ + 2 with hj
  have hnε : 104 ≤ ε * n := by
    have := Nat.le_ceil (104 / ε)
    rw [← hn] at this
    rw [div_le_iff₀ hε] at this
    linarith
  have hjε : 104 ≤ ε ^ 2 * j := by
    have := Nat.le_ceil (104 / ε ^ 2)
    rw [div_le_iff₀ (by positivity)] at this
    have hj' : ((⌈104 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ j := by rw [hj]; push_cast; linarith
    nlinarith [sq_nonneg ε]
  have hj2 : 2 ≤ j := by omega
  -- constants
  set c₁ : ℝ := 56 * cglGMMellinBudget w 0 / Real.pi with hc₁
  set c₂ : ℝ := 8 * 2 ^ n * (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) with hc₂
  set c₃ : ℝ := 8 * 2 ^ j * (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump j /
    (2 * Real.pi) ^ j) * cglGMInverseSquareMass with hc₃
  set K : ℝ := 2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 +
    18 * (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
      cglGMInverseSquareMass with hK
  set P : ℝ := ((2 : ℝ) ^ (1 / ε)) ^ 100 with hP
  have hB0 := cglGMMellinBudget_nonneg w 0
  have hBn := cglGMMellinBudget_nonneg w n
  have hBn2 := cglGMMellinBudget_nonneg w (n + 2)
  have hA0 := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 0
  have hA2 := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2
  have hAj := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump j
  have hZ := cglGMInverseSquareMass_nonneg
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hP0 : 0 ≤ P := by positivity
  refine ⟨c₁ + c₂ + c₃ + K * P, by positivity, ?_⟩
  intro T t N hT hN htT htT'
  have hT0 : 0 < T := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTe1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have ht1 : 1 ≤ |t| := hTe1.trans htT
  have hint0 : 0 ≤ ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
      ‖cglGMHeadPoly ⌈|t| ^ (1 + ε) / N⌉₊ (t + u)‖ :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _
  have hrp : 0 ≤ |t| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg t) _
  have hTr : 0 ≤ T ^ (-100 : ℝ) := Real.rpow_nonneg hT0.le _
  have hmain0 : 0 ≤ (c₁ + c₂ + c₃ + K * P) * |t| ^ (-(1 / 2 : ℝ)) *
      (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
        ‖cglGMHeadPoly ⌈|t| ^ (1 + ε) / N⌉₊ (t + u)‖) := by positivity
  by_cases ht2 : 2 ≤ |t|
  · -- main case
    set M : ℕ := ⌈|t| ^ (1 + ε) / N⌉₊ with hM
    have hx0 : 0 < |t| ^ (1 + ε) / N :=
      div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hx0))
    have hMx : |t| ^ (1 + ε) / N ≤ M := Nat.le_ceil _
    have hMT : (M : ℝ) ≤ 2 * T ^ 2 := by
      have h1 := Nat.ceil_lt_add_one hx0.le
      have h2 : |t| ^ (1 + ε) / N ≤ T ^ 2 := by
        calc |t| ^ (1 + ε) / N ≤ |t| ^ (1 + ε) := div_le_self (by positivity) hN1
          _ ≤ T ^ (1 + ε) := Real.rpow_le_rpow (by positivity) htT' (by linarith)
          _ ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
          _ = T ^ 2 := Real.rpow_two T
      have h3 : 1 ≤ T ^ 2 := one_le_pow₀ hT
      rw [← hM] at h1
      linarith
    have hU : 0 < T ^ ε / 2 := by positivity
    have hUt : T ^ ε / 2 ≤ |t| / 2 := by linarith
    have hbound := norm_cglGMNonzeroModeSum_le w hN1 hM1 hU hUt ht2 n hj2
    have hw := cglGMWindowWeight_div_pi_le w (t := t) (by linarith)
    have htw := cglGMTailWeight_le_rpow w hT hnε hM1 hMT
    have hfw := cglGMFrequencyTailWeight_le_rpow w.toCGLSmoothBump hT hε hN1 htT ht1 hM1 hMx
      hMT hj2 hjε
    rw [← hc₁] at hw
    rw [← hc₂] at htw
    rw [← hc₃] at hfw
    have hU' : -(T ^ ε / 2) = -(T ^ ε / 2) := rfl
    calc ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖
        ≤ cglGMWindowWeight w t / Real.pi *
              (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) +
            cglGMTailWeight w n (T ^ ε / 2) M +
              cglGMFrequencyTailWeight w.toCGLSmoothBump j t N M := hbound
      _ ≤ c₁ * |t| ^ (-(1 / 2 : ℝ)) *
              (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) +
            c₂ * T ^ (-100 : ℝ) + c₃ * T ^ (-100 : ℝ) := by
          gcongr
      _ ≤ (c₁ + c₂ + c₃ + K * P) * |t| ^ (-(1 / 2 : ℝ)) *
              (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) +
            (c₁ + c₂ + c₃ + K * P) * T ^ (-100 : ℝ) := by
          have hc : c₁ ≤ c₁ + c₂ + c₃ + K * P := by linarith [mul_nonneg hK0 hP0]
          have hc' : c₂ + c₃ ≤ c₁ + c₂ + c₃ + K * P := by linarith [mul_nonneg hK0 hP0]
          have hI0 : 0 ≤ |t| ^ (-(1 / 2 : ℝ)) *
              (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) := by
            rw [hM]; positivity
          nlinarith [mul_le_mul_of_nonneg_right hc hI0, mul_le_mul_of_nonneg_right hc' hTr]
  · -- small case: `|t| < 2`, so `T < 2^{1/ε}`
    have ht2' : |t| ≤ 2 := (not_le.mp ht2).le
    have hcrude := norm_cglGMNonzeroModeSum_le_crude w.toCGLSmoothBump (t := t) hN1
    have hcon := cglGMFrequencyTailWeight_two_le w.toCGLSmoothBump hN1 ht2'
    have hTP : T ^ 100 ≤ P := by
      have hTle : T ≤ (2 : ℝ) ^ (1 / ε) := by
        have h := Real.rpow_le_rpow (by positivity) (htT.trans ht2') (by positivity : 0 ≤ 1 / ε)
        rwa [← Real.rpow_mul hT0.le, mul_one_div_cancel hε.ne', Real.rpow_one] at h
      exact pow_le_pow_left₀ hT0.le hTle 100
    have hKT : K ≤ K * P * T ^ (-100 : ℝ) := by
      rw [rpow_neg_hundred T hT0.le, mul_assoc, ← div_eq_mul_inv]
      have hT100 : 0 < T ^ 100 := by positivity
      rw [le_mul_iff_one_le_right' hK0 |>.mpr ?_] <;> [skip; exact (one_le_div hT100).mpr hTP]
      · exact le_rfl
    have hLHS : ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤ K := by
      rw [hK]; linarith
    have hKP : K * P * T ^ (-100 : ℝ) ≤ (c₁ + c₂ + c₃ + K * P) * T ^ (-100 : ℝ) := by
      gcongr
      linarith
    linarith

end RHTower
