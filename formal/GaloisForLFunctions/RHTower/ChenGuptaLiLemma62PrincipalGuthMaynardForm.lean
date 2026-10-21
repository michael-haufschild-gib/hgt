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

/-- The Mellin tail: `c₂ ≤ 128 · 2^n (B_n + B_{n+2}) T^{−100}` for `U = T^ε/2`, `εn ≥ 104`,
`M ≤ 8T²`. -/
theorem cglGMTailWeight_le_rpow (w : CGLRealSmoothBump) {T ε : ℝ} (hT : 1 ≤ T) {n : ℕ}
    (hn : 104 ≤ ε * n) {M : ℕ} (hM1 : 1 ≤ M) (hM : (M : ℝ) ≤ 8 * T ^ 2) :
    cglGMTailWeight w n (T ^ ε / 2) M ≤
      128 * 2 ^ n * (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) * T ^ (-100 : ℝ) := by
  set B : ℝ := cglGMMellinBudget w n + cglGMMellinBudget w (n + 2) with hB
  have hB0 : 0 ≤ B := add_nonneg (cglGMMellinBudget_nonneg w n) (cglGMMellinBudget_nonneg w _)
  have hT0 : 0 < T := by linarith
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hU : T ^ 104 / 2 ^ n ≤ (T ^ ε / 2) ^ n := by
    rw [div_pow, ← Real.rpow_mul_natCast hT0.le]
    gcongr
    exact pow_hundredFour_le_rpow hT hn
  have hlog : (M : ℝ) * Real.log (2 * M) ≤ 128 * T ^ 4 := by
    have h1 : Real.log (2 * M) ≤ 2 * M := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * M)
      linarith
    have h2 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
    calc (M : ℝ) * Real.log (2 * M) ≤ (8 * T ^ 2) * (2 * (8 * T ^ 2)) := by
          gcongr
          linarith
      _ = 128 * T ^ 4 := by ring
  unfold cglGMTailWeight
  rw [← hB, rpow_neg_hundred T hT0.le]
  have hML : 0 ≤ (M : ℝ) * Real.log (2 * M) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  calc B / (T ^ ε / 2) ^ n * ((M : ℝ) * Real.log (2 * M))
      ≤ B / (T ^ 104 / 2 ^ n) * (128 * T ^ 4) :=
        mul_le_mul (div_le_div_of_nonneg_left hB0 (by positivity) hU) hlog hML
          (div_nonneg hB0 (by positivity))
    _ = 128 * 2 ^ n * B * (T ^ 100)⁻¹ := by
        field_simp

/-- The frequency tail: for `N M ≥ |t|^{1+ε}`, `|t| ≥ T^ε`, `ε² j ≥ 104`, `M ≤ 8T²`,
`tail_j ≤ 128 · 2^j A_j Z T^{−100}`. -/
theorem cglGMFrequencyTailWeight_le_rpow (w : CGLSmoothBump) {T ε t N : ℝ} (hT : 1 ≤ T)
    (hε : 0 < ε) (hN : 1 ≤ N) (htT : T ^ ε ≤ |t|) (ht1 : 1 ≤ |t|) {M : ℕ} (hM1 : 1 ≤ M)
    (hMx : |t| ^ (1 + ε) / N ≤ M) (hM : (M : ℝ) ≤ 8 * T ^ 2) {j : ℕ} (hj : 2 ≤ j)
    (hjε : 104 ≤ ε ^ 2 * j) :
    cglGMFrequencyTailWeight w j t N M ≤
      128 * 2 ^ j * (cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j) *
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
    have h1 := (div_le_iff₀ hN0).mp hMx
    rw [Real.rpow_add ht0, Real.rpow_one] at h1
    calc |t| * |t| ^ ε ≤ M * N := h1
      _ = N * M := mul_comm _ _
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
    ring
  have hM2 : (M : ℝ) ^ 2 ≤ 64 * T ^ 4 := by
    calc (M : ℝ) ^ 2 ≤ (8 * T ^ 2) ^ 2 := by gcongr
      _ = 64 * T ^ 4 := by ring
  unfold cglGMFrequencyTailWeight
  rw [rpow_neg_hundred T hT0.le, mul_div_assoc, ← hA, hsplit]
  calc 2 * (A * ((M : ℝ) ^ 2 * ((1 + |t|) / (N * M)) ^ j)) * cglGMInverseSquareMass
      ≤ 2 * (A * ((64 * T ^ 4) * (2 ^ j / T ^ 104))) * cglGMInverseSquareMass := by
        gcongr
    _ = 128 * 2 ^ j * A * cglGMInverseSquareMass * (T ^ 100)⁻¹ := by
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
  simp only [Nat.cast_one, mul_one, Nat.sub_self, pow_zero]
  calc 2 * (cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 / N ^ 2) *
        cglGMInverseSquareMass
      ≤ 2 * (cglSmoothBumpHtAllOrderBudget w 2 / (2 * Real.pi) ^ 2 * 9 / 1) *
          cglGMInverseSquareMass := by gcongr
    _ = _ := by ring

/-! ### The paper's parameters -/

/-- Mellin decay order `n = ⌈104/ε⌉`, so that `ε n ≥ 104`. -/
def cglGMLemma62MellinOrder (ε : ℝ) : ℕ := ⌈104 / ε⌉₊

/-- Fourier decay order `j = ⌈104/ε²⌉ + 2`, so that `ε² j ≥ 104` and `j ≥ 2`. -/
def cglGMLemma62FourierOrder (ε : ℝ) : ℕ := ⌈104 / ε ^ 2⌉₊ + 2

theorem cglGMLemma62MellinOrder_spec {ε : ℝ} (hε : 0 < ε) :
    104 ≤ ε * cglGMLemma62MellinOrder ε := by
  have h := Nat.le_ceil (104 / ε)
  rw [div_le_iff₀ hε] at h
  unfold cglGMLemma62MellinOrder
  linarith

theorem cglGMLemma62FourierOrder_spec {ε : ℝ} (hε : 0 < ε) :
    2 ≤ cglGMLemma62FourierOrder ε ∧ 104 ≤ ε ^ 2 * cglGMLemma62FourierOrder ε := by
  refine ⟨by unfold cglGMLemma62FourierOrder; omega, ?_⟩
  have h := Nat.le_ceil (104 / ε ^ 2)
  rw [div_le_iff₀ (by positivity)] at h
  unfold cglGMLemma62FourierOrder
  push_cast
  nlinarith [sq_nonneg ε]

/-- The window constant `56 B₀/π`. -/
def cglGMLemma62WindowConst (w : CGLRealSmoothBump) : ℝ :=
  56 * cglGMMellinBudget w 0 / Real.pi

/-- The error constant of the large-time case: Mellin tail plus frequency tail. -/
def cglGMLemma62ErrorConst (w : CGLRealSmoothBump) (ε : ℝ) : ℝ :=
  128 * 2 ^ cglGMLemma62MellinOrder ε * (cglGMMellinBudget w (cglGMLemma62MellinOrder ε) +
      cglGMMellinBudget w (cglGMLemma62MellinOrder ε + 2)) +
    128 * 2 ^ cglGMLemma62FourierOrder ε *
      (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump (cglGMLemma62FourierOrder ε) /
        (2 * Real.pi) ^ cglGMLemma62FourierOrder ε) * cglGMInverseSquareMass

/-- The small-time constant `(2A₀ + 18 A₂ Z) (2^{1/ε})^{100}`. -/
def cglGMLemma62SmallTimeConst (w : CGLRealSmoothBump) (ε : ℝ) : ℝ :=
  (2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 +
    18 * (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
      cglGMInverseSquareMass) * ((2 : ℝ) ^ (1 / ε)) ^ 100

theorem cglGMLemma62WindowConst_nonneg (w : CGLRealSmoothBump) :
    0 ≤ cglGMLemma62WindowConst w := by
  have := cglGMMellinBudget_nonneg w 0
  unfold cglGMLemma62WindowConst
  positivity

theorem cglGMLemma62ErrorConst_nonneg (w : CGLRealSmoothBump) (ε : ℝ) :
    0 ≤ cglGMLemma62ErrorConst w ε := by
  have := cglGMMellinBudget_nonneg w (cglGMLemma62MellinOrder ε)
  have := cglGMMellinBudget_nonneg w (cglGMLemma62MellinOrder ε + 2)
  have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump (cglGMLemma62FourierOrder ε)
  have := cglGMInverseSquareMass_nonneg
  unfold cglGMLemma62ErrorConst
  positivity

theorem cglGMLemma62SmallTimeConst_nonneg (w : CGLRealSmoothBump) (ε : ℝ) :
    0 ≤ cglGMLemma62SmallTimeConst w ε := by
  have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 0
  have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2
  have := cglGMInverseSquareMass_nonneg
  unfold cglGMLemma62SmallTimeConst
  positivity

/-- The length `M = ⌈|t|^{1+ε}/N⌉` satisfies `1 ≤ M`, `|t|^{1+ε}/N ≤ M` and `M ≤ 2T²`. -/
theorem cglGMLemma62Length_spec {ε T t N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 1 ≤ T)
    (hN : 1 ≤ N)
    (ht1 : 1 ≤ |t|) (htT : |t| ≤ T) :
    1 ≤ ⌈|t| ^ (1 + ε) / N⌉₊ ∧ |t| ^ (1 + ε) / N ≤ ⌈|t| ^ (1 + ε) / N⌉₊ ∧
      (⌈|t| ^ (1 + ε) / N⌉₊ : ℝ) ≤ 2 * T ^ 2 := by
  have hx0 : 0 < |t| ^ (1 + ε) / N :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hx0)),
    Nat.le_ceil _, ?_⟩
  have h1 := Nat.ceil_lt_add_one hx0.le
  have h2 : |t| ^ (1 + ε) / N ≤ T ^ 2 := by
    calc |t| ^ (1 + ε) / N ≤ |t| ^ (1 + ε) := div_le_self (by positivity) hN
      _ ≤ T ^ (1 + ε) := Real.rpow_le_rpow (by positivity) htT (by linarith)
      _ ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T ^ 2 := Real.rpow_two T
  have h3 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  linarith

/-- Large-time case `|t| ≥ 2` with an admissible length `|t|^{1+ε}/N ≤ M ≤ 8T²`. -/
theorem cglGM_lemma62_zeta_largeTime (w : CGLRealSmoothBump) {ε T t N : ℝ} (hε : 0 < ε)
    (hT : 1 ≤ T) (hN : 1 ≤ N) (htT : T ^ ε ≤ |t|) (ht2 : 2 ≤ |t|) {M : ℕ} (hM1 : 1 ≤ M)
    (hMx : |t| ^ (1 + ε) / N ≤ M) (hMT : (M : ℝ) ≤ 8 * T ^ 2) :
    ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤
      cglGMLemma62WindowConst w * |t| ^ (-(1 / 2 : ℝ)) *
          (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) +
        cglGMLemma62ErrorConst w ε * T ^ (-100 : ℝ) := by
  obtain ⟨hj2, hjε⟩ := cglGMLemma62FourierOrder_spec hε
  have hU : 0 < T ^ ε / 2 := by positivity
  have hUt : T ^ ε / 2 ≤ |t| / 2 := by linarith
  have hbound := norm_cglGMNonzeroModeSum_le w hN hM1 hU hUt ht2
    (cglGMLemma62MellinOrder ε) hj2
  have hw := cglGMWindowWeight_div_pi_le w (t := t) (by linarith)
  have htw := cglGMTailWeight_le_rpow w hT (cglGMLemma62MellinOrder_spec hε) hM1 hMT
  have hfw := cglGMFrequencyTailWeight_le_rpow w.toCGLSmoothBump hT hε hN htT (by linarith)
    hM1 hMx hMT hj2 hjε
  have hI0 : 0 ≤ ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖ :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _
  have hmain := mul_le_mul_of_nonneg_right hw hI0
  unfold cglGMLemma62ErrorConst
  unfold cglGMLemma62WindowConst
  linarith

/-- Small-time case `|t| ≤ 2`: then `T ≤ 2^{1/ε}`, and the crude bound is `≪ T^{−100}`. -/
theorem cglGM_lemma62_zeta_smallTime (w : CGLRealSmoothBump) {ε T t N : ℝ} (hε : 0 < ε)
    (hT : 1 ≤ T) (hN : 1 ≤ N) (htT : T ^ ε ≤ |t|) (ht2 : |t| ≤ 2) :
    ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤
      cglGMLemma62SmallTimeConst w ε * T ^ (-100 : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hcrude := norm_cglGMNonzeroModeSum_le_crude w.toCGLSmoothBump (t := t) hN
  have hcon := cglGMFrequencyTailWeight_two_le w.toCGLSmoothBump hN ht2
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 0 +
      18 * (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        cglGMInverseSquareMass := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 0
    have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2
    have := cglGMInverseSquareMass_nonneg
    rw [hK]; positivity
  have hLHS : ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤ K := by
    rw [hK]; linarith
  have hTle : T ≤ (2 : ℝ) ^ (1 / ε) := by
    have h := Real.rpow_le_rpow (by positivity) (htT.trans ht2) (by positivity : 0 ≤ 1 / ε)
    rwa [← Real.rpow_mul hT0.le, mul_one_div_cancel hε.ne', Real.rpow_one] at h
  have hTP : T ^ 100 ≤ ((2 : ℝ) ^ (1 / ε)) ^ 100 := pow_le_pow_left₀ hT0.le hTle 100
  have hT100 : 0 < T ^ 100 := by positivity
  rw [cglGMLemma62SmallTimeConst, ← hK, rpow_neg_hundred T hT0.le]
  calc ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤ K := hLHS
    _ = K * T ^ 100 * (T ^ 100)⁻¹ := by field_simp
    _ ≤ K * ((2 : ℝ) ^ (1 / ε)) ^ 100 * (T ^ 100)⁻¹ := by gcongr

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
  have h₁ := cglGMLemma62WindowConst_nonneg w
  have h₂ := cglGMLemma62ErrorConst_nonneg w ε
  have h₃ := cglGMLemma62SmallTimeConst_nonneg w ε
  refine ⟨cglGMLemma62WindowConst w + cglGMLemma62ErrorConst w ε +
    cglGMLemma62SmallTimeConst w ε, by positivity, ?_⟩
  intro T t N hT hN htT htT'
  have hT0 : 0 < T := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : 1 ≤ |t| := (Real.one_le_rpow hT hε.le).trans htT
  have hI0 : 0 ≤ ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
      ‖cglGMHeadPoly ⌈|t| ^ (1 + ε) / N⌉₊ (t + u)‖ :=
    intervalIntegral.integral_nonneg (by have := Real.rpow_pos_of_pos hT0 ε; linarith)
      fun _ _ => norm_nonneg _
  have hrp : 0 ≤ |t| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg t) _
  have hTr : 0 ≤ T ^ (-100 : ℝ) := Real.rpow_nonneg hT0.le _
  have hmain0 := mul_nonneg hrp hI0
  rcases le_or_gt 2 |t| with ht2 | ht2
  · obtain ⟨hM1, hMx, hMT⟩ := cglGMLemma62Length_spec hε hε1 hT hN1 ht1 htT'
    have h := cglGM_lemma62_zeta_largeTime w hε hT hN1 htT ht2 hM1 hMx (by linarith)
    nlinarith [mul_nonneg h₃ hmain0, mul_nonneg h₂ hmain0, mul_nonneg h₁ hTr,
      mul_nonneg h₃ hTr]
  · have h := cglGM_lemma62_zeta_smallTime w hε hT hN1 htT ht2.le
    nlinarith [mul_nonneg h₁ hmain0, mul_nonneg h₂ hmain0, mul_nonneg h₃ hmain0,
      mul_nonneg h₁ hTr, mul_nonneg h₂ hTr]

/-- **Lemma 6.2 for `ζ` with a free admissible length.**  For every `ε ∈ (0,1]` there is `C ≥ 0`
such that for all `T ≥ 1`, real `N ≥ 1`, `T^ε ≤ |t| ≤ T` and every `M` with
`|t|^{1+ε}/N ≤ M ≤ 8T²`,
`‖Σ_{m ≠ 0} ĥ_t(mN)‖ ≤ C |t|^{−1/2} ∫_{−T^ε/2}^{T^ε/2} ‖Σ_{m=1}^{M} m^{−i(t+u)}‖ du + C T^{−100}`. -/
theorem cglGM_lemma62_zeta_of_length (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T t N : ℝ) (M : ℕ), 1 ≤ T → 1 ≤ N → T ^ ε ≤ |t| → |t| ≤ T → 1 ≤ M →
      |t| ^ (1 + ε) / N ≤ M → (M : ℝ) ≤ 8 * T ^ 2 →
      ‖cglGMNonzeroModeSum w.toCGLSmoothBump N t‖ ≤
        C * |t| ^ (-(1 / 2 : ℝ)) *
            (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) +
          C * T ^ (-100 : ℝ) := by
  have h₁ := cglGMLemma62WindowConst_nonneg w
  have h₂ := cglGMLemma62ErrorConst_nonneg w ε
  have h₃ := cglGMLemma62SmallTimeConst_nonneg w ε
  refine ⟨cglGMLemma62WindowConst w + cglGMLemma62ErrorConst w ε +
    cglGMLemma62SmallTimeConst w ε, by positivity, ?_⟩
  intro T t N M hT hN htT _ hM1 hMx hMT
  have hT0 : 0 < T := by linarith
  have hI0 : 0 ≤ ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖ :=
    intervalIntegral.integral_nonneg (by have := Real.rpow_pos_of_pos hT0 ε; linarith)
      fun _ _ => norm_nonneg _
  have hrp : 0 ≤ |t| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg t) _
  have hTr : 0 ≤ T ^ (-100 : ℝ) := Real.rpow_nonneg hT0.le _
  have hmain0 := mul_nonneg hrp hI0
  rcases le_or_gt 2 |t| with ht2 | ht2
  · have h := cglGM_lemma62_zeta_largeTime w hε hT hN htT ht2 hM1 hMx hMT
    nlinarith [mul_nonneg h₃ hmain0, mul_nonneg h₂ hmain0, mul_nonneg h₁ hTr,
      mul_nonneg h₃ hTr]
  · have h := cglGM_lemma62_zeta_smallTime w hε hT hN htT ht2.le
    nlinarith [mul_nonneg h₁ hmain0, mul_nonneg h₂ hmain0, mul_nonneg h₃ hmain0,
      mul_nonneg h₁ hTr, mul_nonneg h₂ hTr]

end RHTower
