import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectionIdentity
import GaloisForLFunctions.RHTower.L2FourierConjugation
import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51FrequencyTail
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# Guth–Maynard Lemma 6.2 for `ζ`: the explicit two-sided bound

From the exact reflection identity (`cglGM_sum_fourier_eq_reflected`) and the uniform phase bound
`‖K(ρ)‖ ≤ 28/√|ρ|`, for `N ≥ 1`, `M ≥ 1`, `2 ≤ |t|`, `0 < U ≤ |t|/2` and every `n`:

`‖Σ_{m=1}^{M} ĥ_t(±mN)‖ ≤ (28 B₀ / (2π √(|t|/2))) ∫_{−U}^{U} ‖Σ_{m ≤ M} m^{−i(t+u)}‖ du
    + (B_n + B_{n+2}) U^{−n} M log(2M) / 2`,

where `B_n` is the all-order Mellin decay budget of `H(1+iy)`.  Mechanism: for `|y| ≤ U` the
phase integral is `≤ 28/√(|t|/2)` and `‖H‖ ≤ B₀`; for `|y| > U`, `‖H(1+iy)‖ ≤ (B_n+B_{n+2}) /
((1+y²) U^n)` while the Dirichlet head is `≤ M` and the phase integral `≤ log 2M`.  Negative
frequencies follow from `ĥ_t(−ξ) = conj ĥ_{−t}(ξ)` (real bump).  The frequencies `|m| > M` cost
`2 A_j (1+|t|)^j N^{−j} M^{2−j} Σ_k (k+1)^{−2}` by the all-order decay of Lemma 4.3.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- The Dirichlet head `Σ_{m=1}^{M} m^{−iτ}` in the Sieve convention. -/
def cglGMHeadPoly (M : ℕ) (τ : ℝ) : ℂ :=
  Sieve.dirPoly M (fun _ => 1) (-τ)

theorem norm_cglGMHeadPoly_le (M : ℕ) (τ : ℝ) : ‖cglGMHeadPoly M τ‖ ≤ M := by
  unfold cglGMHeadPoly Sieve.dirPoly
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp only [one_mul, Complex.norm_exp_ofReal_mul_I, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem continuous_cglGMHeadPoly (M : ℕ) : Continuous (cglGMHeadPoly M) := by
  unfold cglGMHeadPoly Sieve.dirPoly
  fun_prop

/-- `‖Σ m^{−i(−τ)}‖ = ‖Σ m^{−iτ}‖`: the head with unit coefficients is conjugation-symmetric. -/
theorem norm_cglGMHeadPoly_neg (M : ℕ) (τ : ℝ) :
    ‖cglGMHeadPoly M (-τ)‖ = ‖cglGMHeadPoly M τ‖ := by
  unfold cglGMHeadPoly
  have h := Sieve.dirPoly_conj_neg M (fun _ => (1 : ℂ)) τ
  simp only [map_one] at h
  rw [neg_neg, h, RCLike.norm_conj]

/-- `Σ_{m=1}^{M} e^{−iτ log(mN)} = e^{−iτ log N} Σ_{m ≤ M} m^{−iτ}`. -/
theorem sum_Icc_exp_log_mul_eq_head (τ N : ℝ) (hN : 0 < N) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, Complex.exp (((-(τ * Real.log ((m : ℝ) * N)) : ℝ) : ℂ) * I) =
      Complex.exp (((-(τ * Real.log N) : ℝ) : ℂ) * I) * cglGMHeadPoly M τ := by
  rw [cglGMHeadPoly, Sieve.dirPoly, Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    ← Fin.sum_univ_eq_sum_range (fun k => Complex.exp
      (((-(τ * Real.log (((1 + k : ℕ) : ℝ) * N)) : ℝ) : ℂ) * I))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) < ((1 + (k : ℕ) : ℕ) : ℝ) := by positivity
  rw [Real.log_mul hk.ne' hN.ne', one_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Pointwise form of the reflected integrand summed over `m`. -/
theorem sum_cglGMReflectedTerm_eq (w : CGLRealSmoothBump) (t N : ℝ) (hN : 0 < N) (M : ℕ)
    (y : ℝ) :
    ∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y =
      cglGMMellinLine w y * ((Complex.exp (((-((t - y) * Real.log N) : ℝ) : ℂ) * I) *
        cglGMHeadPoly M (t - y)) *
          cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))) := by
  rw [← sum_Icc_exp_log_mul_eq_head (t - y) N hN M, Finset.sum_mul, Finset.mul_sum]
  rfl

theorem norm_sum_cglGMReflectedTerm (w : CGLRealSmoothBump) (t N : ℝ) (hN : 0 < N) (M : ℕ)
    (y : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y‖ =
      ‖cglGMMellinLine w y‖ * (‖cglGMHeadPoly M (t - y)‖ *
        ‖cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))‖) := by
  rw [sum_cglGMReflectedTerm_eq w t N hN M y, norm_mul, norm_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The all-order budget `B_n` of `|y|^n ‖H(1+iy)‖`. -/
def cglGMMellinBudget (w : CGLRealSmoothBump) (n : ℕ) : ℝ :=
  cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n

theorem abs_pow_mul_norm_cglGMMellinLine_le (w : CGLRealSmoothBump) (n : ℕ) (y : ℝ) :
    |y| ^ n * ‖cglGMMellinLine w y‖ ≤ cglGMMellinBudget w n :=
  cglLemma62_mellinTransform_one_add_it_rapidDecay w n y

theorem norm_cglGMMellinLine_le (w : CGLRealSmoothBump) (y : ℝ) :
    ‖cglGMMellinLine w y‖ ≤ cglGMMellinBudget w 0 := by
  simpa using abs_pow_mul_norm_cglGMMellinLine_le w 0 y

/-- Off the window: `‖H(1+iy)‖ ≤ (B_n + B_{n+2}) / ((1+y²) U^n)` for `|y| ≥ U > 0`. -/
theorem norm_cglGMMellinLine_le_of_le_abs (w : CGLRealSmoothBump) (n : ℕ) {U y : ℝ}
    (hU : 0 < U) (hy : U ≤ |y|) :
    ‖cglGMMellinLine w y‖ ≤
      (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) / U ^ n * (1 + y ^ 2)⁻¹ := by
  have h0 := abs_pow_mul_norm_cglGMMellinLine_le w n y
  have h2 := abs_pow_mul_norm_cglGMMellinLine_le w (n + 2) y
  have hUn : 0 < U ^ n := pow_pos hU n
  have hyn : U ^ n ≤ |y| ^ n := pow_le_pow_left₀ hU.le hy n
  have hsq : |y| ^ (n + 2) = |y| ^ n * y ^ 2 := by rw [pow_add, sq_abs]
  have hsum : U ^ n * ((1 + y ^ 2) * ‖cglGMMellinLine w y‖) ≤
      cglGMMellinBudget w n + cglGMMellinBudget w (n + 2) := by
    calc U ^ n * ((1 + y ^ 2) * ‖cglGMMellinLine w y‖)
        ≤ |y| ^ n * ((1 + y ^ 2) * ‖cglGMMellinLine w y‖) := by gcongr
      _ = |y| ^ n * ‖cglGMMellinLine w y‖ + |y| ^ (n + 2) * ‖cglGMMellinLine w y‖ := by
          rw [hsq]; ring
      _ ≤ _ := add_le_add h0 h2
  have hpos : 0 < 1 + y ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hUn, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- The window weight `c₁ = 28 B₀ / √(|t|/2)` of the main term. -/
def cglGMWindowWeight (w : CGLRealSmoothBump) (t : ℝ) : ℝ :=
  cglGMMellinBudget w 0 * (28 / Real.sqrt (|t| / 2))

/-- The tail weight `c₂ = (B_n + B_{n+2}) U^{−n} M log 2M`. -/
def cglGMTailWeight (w : CGLRealSmoothBump) (n : ℕ) (U : ℝ) (M : ℕ) : ℝ :=
  (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) / U ^ n * (M * Real.log (2 * M))

theorem cglGMMellinBudget_nonneg (w : CGLRealSmoothBump) (n : ℕ) :
    0 ≤ cglGMMellinBudget w n :=
  (mul_nonneg (pow_nonneg (abs_nonneg 1) n) (norm_nonneg _)).trans
    (abs_pow_mul_norm_cglGMMellinLine_le w n 1)

/-- Pointwise domination of the reflected integrand. -/
theorem norm_sum_cglGMReflectedTerm_le (w : CGLRealSmoothBump) {t N U : ℝ} (hN : 1 ≤ N)
    {M : ℕ} (hM : 1 ≤ M) (hU : 0 < U) (hUt : U ≤ |t| / 2) (ht : 2 ≤ |t|) (n : ℕ) (y : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y‖ ≤
      (Icc (-U) U).indicator (fun y => cglGMWindowWeight w t * ‖cglGMHeadPoly M (t - y)‖) y +
        cglGMTailWeight w n U M * (1 + y ^ 2)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlen : |Real.log (2 * M * N) - Real.log N| = Real.log (2 * M) := by
    rw [Real.log_mul (by positivity) hN0.ne', add_sub_cancel_right,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
  have hB0 := cglGMMellinBudget_nonneg w 0
  have htail0 : 0 ≤ cglGMTailWeight w n U M * (1 + y ^ 2)⁻¹ := by
    unfold cglGMTailWeight
    have := cglGMMellinBudget_nonneg w n
    have := cglGMMellinBudget_nonneg w (n + 2)
    have : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
    positivity
  rw [norm_sum_cglGMReflectedTerm w t N hN0 M y]
  by_cases hy : y ∈ Icc (-U) U
  · rw [indicator_of_mem hy]
    have hyU : |y| ≤ U := abs_le.mpr hy
    have hty : |t| / 2 ≤ |t - y| := by
      have := abs_sub_abs_le_abs_sub t y
      linarith
    have hρ : 1 ≤ |t - y| := by linarith
    have hK := norm_cglGMReflectionPhaseIntegral_le hρ (Real.log N) (Real.log (2 * M * N))
    have hK' : ‖cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))‖ ≤
        28 / Real.sqrt (|t| / 2) :=
      hK.trans (div_le_div_of_nonneg_left (by norm_num)
        (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt hty))
    refine le_add_of_le_of_nonneg ?_ htail0
    unfold cglGMWindowWeight
    calc ‖cglGMMellinLine w y‖ * (‖cglGMHeadPoly M (t - y)‖ *
          ‖cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))‖)
        ≤ cglGMMellinBudget w 0 * (‖cglGMHeadPoly M (t - y)‖ * (28 / Real.sqrt (|t| / 2))) := by
          gcongr
          exact norm_cglGMMellinLine_le w y
      _ = _ := by ring
  · rw [indicator_of_notMem hy, zero_add]
    have hyU : U ≤ |y| := by
      by_contra h
      exact hy (abs_le.mp (not_le.mp h).le)
    have hH := norm_cglGMMellinLine_le_of_le_abs w n hU hyU
    have hD := norm_cglGMHeadPoly_le M (t - y)
    have hK := norm_cglGMReflectionPhaseIntegral_le_length (t - y) (Real.log N)
      (Real.log (2 * M * N))
    rw [hlen] at hK
    unfold cglGMTailWeight
    have hX0 : 0 ≤ (cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) / U ^ n *
        (1 + y ^ 2)⁻¹ := (norm_nonneg _).trans hH
    calc ‖cglGMMellinLine w y‖ * (‖cglGMHeadPoly M (t - y)‖ *
          ‖cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N))‖)
        ≤ ((cglGMMellinBudget w n + cglGMMellinBudget w (n + 2)) / U ^ n * (1 + y ^ 2)⁻¹) *
            (M * Real.log (2 * M)) :=
          mul_le_mul hH (mul_le_mul hD hK (norm_nonneg _) (Nat.cast_nonneg _))
            (by positivity) hX0
      _ = _ := by ring

/-- **Positive frequencies.** `‖Σ_{m=1}^{M} ĥ_t(mN)‖ ≤ (c₁/2π) ∫_{−U}^{U} ‖head(t+u)‖ du + c₂/2`. -/
theorem cglGM_norm_sum_fourier_pos_le (w : CGLRealSmoothBump) {t N U : ℝ} (hN : 1 ≤ N)
    {M : ℕ} (hM : 1 ≤ M) (hU : 0 < U) (hUt : U ≤ |t| / 2) (ht : 2 ≤ |t|) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N)‖ ≤
      cglGMWindowWeight w t / (2 * Real.pi) *
          ∫ u in (-U)..U, ‖cglGMHeadPoly M (t + u)‖ +
        cglGMTailWeight w n U M / 2 := by
  have hN0 : 0 < N := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  set g : ℝ → ℝ := fun y =>
    (Icc (-U) U).indicator (fun y => cglGMWindowWeight w t * ‖cglGMHeadPoly M (t - y)‖) y +
      cglGMTailWeight w n U M * (1 + y ^ 2)⁻¹ with hg
  have hcont : Continuous fun y => cglGMWindowWeight w t * ‖cglGMHeadPoly M (t - y)‖ :=
    continuous_const.mul ((continuous_cglGMHeadPoly M).comp (by fun_prop)).norm
  have hgint : Integrable g :=
    (hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc).add
      (integrable_inv_one_add_sq.const_mul _)
  have hint : ∫ y, ‖∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y‖ ≤ ∫ y, g y :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hgint
      (Filter.Eventually.of_forall fun y =>
        norm_sum_cglGMReflectedTerm_le w hN hM hU hUt ht n y)
  have hgval : ∫ y, g y = cglGMWindowWeight w t * ∫ u in (-U)..U, ‖cglGMHeadPoly M (t + u)‖ +
      cglGMTailWeight w n U M * Real.pi := by
    rw [hg, integral_add (hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc)
      (integrable_inv_one_add_sq.const_mul _), integral_indicator measurableSet_Icc,
      integral_const_mul (cglGMTailWeight w n U M), integral_univ_inv_one_add_sq,
      integral_const_mul (cglGMWindowWeight w t),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    congr 2
    have h := intervalIntegral.integral_comp_neg (a := -U) (b := U)
      (fun u => ‖cglGMHeadPoly M (t + u)‖)
    simp only [neg_neg, ← sub_eq_add_neg] at h
    exact h
  rw [cglGM_sum_fourier_eq_reflected w t N hN0 M, norm_mul]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hc]
  calc 1 / (2 * Real.pi) * ‖∫ y, ∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y‖
      ≤ 1 / (2 * Real.pi) * ∫ y, g y := by
        gcongr
        exact (norm_integral_le_integral_norm _).trans hint
    _ = _ := by
        rw [hgval]
        field_simp

/-- For a real bump `h_{−t} = conj h_t`, hence `ĥ_t(−ξ) = conj ĥ_{−t}(ξ)`. -/
theorem cglGM_fourier_neg_eq_conj (w : CGLRealSmoothBump) (t ξ : ℝ) :
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) (-ξ) =
      (starRingEnd ℂ) (𝓕 (cglSmoothBumpHt w.toCGLSmoothBump (-t) : ℝ → ℂ) ξ) := by
  have hconj : (cglSmoothBumpHt w.toCGLSmoothBump (-t) : ℝ → ℂ) =
      fun x => (starRingEnd ℂ) (cglSmoothBumpHt w.toCGLSmoothBump t x) := by
    funext x
    simp only [cglSmoothBumpHt_apply, cglSmoothBumpHtValue, cglMellinPhase, map_mul,
      w.value_eq_realValue, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    congr 2
    push_cast
    ring
  rw [hconj, conj_fourierIntegral_conj]

/-- **Negative frequencies.** The same bound for `Σ_{m=1}^{M} ĥ_t(−mN)`. -/
theorem cglGM_norm_sum_fourier_neg_le (w : CGLRealSmoothBump) {t N U : ℝ} (hN : 1 ≤ N)
    {M : ℕ} (hM : 1 ≤ M) (hU : 0 < U) (hUt : U ≤ |t| / 2) (ht : 2 ≤ |t|) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) (-((m : ℝ) * N))‖ ≤
      cglGMWindowWeight w t / (2 * Real.pi) *
          ∫ u in (-U)..U, ‖cglGMHeadPoly M (t + u)‖ +
        cglGMTailWeight w n U M / 2 := by
  simp_rw [cglGM_fourier_neg_eq_conj w t, ← map_sum, RCLike.norm_conj]
  have h := cglGM_norm_sum_fourier_pos_le w (t := -t) hN hM hU (by rwa [abs_neg])
    (by rwa [abs_neg]) n
  rw [show cglGMWindowWeight w (-t) = cglGMWindowWeight w t by
    simp [cglGMWindowWeight]] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  -- `‖head(−t + u)‖ = ‖head(t − u)‖`, then `u ↦ −u`
  have h1 : ∀ u, ‖cglGMHeadPoly M (-t + u)‖ = ‖cglGMHeadPoly M (t + -u)‖ := by
    intro u
    rw [← norm_cglGMHeadPoly_neg, neg_add, neg_neg]
  simp_rw [h1]
  have h2 := intervalIntegral.integral_comp_neg (a := -U) (b := U)
    (fun u => ‖cglGMHeadPoly M (t + u)‖)
  simpa only [neg_neg] using h2

/-- Lemma 4.3 decay at a nonzero frequency: `‖ĥ_t(ξ)‖ ≤ A_j (1+|t|)^j / |ξ|^j`. -/
theorem norm_fourier_cglSmoothBumpHt_le_div (w : CGLSmoothBump) (j : ℕ) (t : ℝ) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤
      cglSmoothBumpHtAllOrderBudget w j / (2 * Real.pi) ^ j * (1 + |t|) ^ j / |ξ| ^ j := by
  have h := cglSmoothBumpHt_allOrder_fourier_decay w j t ξ
  rw [le_div_iff₀ (pow_pos (abs_pos.mpr hξ) j), mul_comm]
  exact h

end RHTower
