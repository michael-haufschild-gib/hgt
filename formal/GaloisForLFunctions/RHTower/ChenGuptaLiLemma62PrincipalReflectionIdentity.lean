import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectionPhaseBound

/-!
# Guth–Maynard Lemma 6.2 for `ζ`: the exact reflection identity

Guth–Maynard (arXiv:2405.20552, proof of Lemma 6.2, p. 19) write, for `1 ≤ m ≤ M`,

`ĥ_t(mN) = ∫_{1/m}^{2M/m} w(u)² u^{it} e(−mNu) du`

(the range contains the support `[1,2]` of `w`), insert the Mellin inversion
`w(u)² = (1/2π) ∫ H(1+iy) u^{−1−iy} dy` with `H(s) = ∫ w(u)² u^{s−1} du`, and substitute
`v = Nmu`; the `v`-range `[N, 2NM]` no longer depends on `m`, so the `m`-sum becomes a
Dirichlet polynomial.  In the logarithmic variable this is the exact identity

`Σ_{m=1}^{M} ĥ_t(mN) = (1/2π) ∫ H(1+iy) (Σ_{m=1}^{M} e^{−i(t−y) log(mN)}) K(t−y; log N, log 2MN) dy`

with `K(ρ; α, β) = ∫_α^β exp(i(ρx − 2πeˣ)) dx` (`cglGMReflectionPhaseIntegral`).

Mechanism: the corpus bridge `cglSmoothBumpHt_fourier_eq_logFourier` writes `ĥ_t(ξ)` as a
Fourier integral of the compact profile `e^{−u} w(e^{−u})² e(−ξe^{−u})`; mathlib's
`mellinInv_mellin_eq` on `Re s = 1` gives `e^{−u} w(e^{−u})² = (1/2π) ∫ e^{iuy} H(1+iy) dy`;
Fubini on `[a,b] × ℝ` is justified by `|integrand| = |H(1+iy)|`; the translation
`x = log(mN) − u` produces `K`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- `H(1+iy)`, the Mellin kernel of `w²` on the line `Re s = 1`. -/
def cglGMMellinLine (w : CGLRealSmoothBump) (y : ℝ) : ℂ :=
  cglLemma62MellinTransform w (1 + (y : ℂ) * I)

theorem continuous_cglGMMellinLine (w : CGLRealSmoothBump) :
    Continuous (cglGMMellinLine w) := by
  have hH : Continuous (cglLemma62MellinTransform w) :=
    continuousOn_univ.mp (cglLemma62_mellinTransform_analyticOnNhd w).continuousOn
  exact hH.comp (by fun_prop)

theorem integrable_cglGMMellinLine (w : CGLRealSmoothBump) :
    Integrable (cglGMMellinLine w) := by
  have h := cglLemma62_mellinTransform_verticalIntegrable w 1
  change Integrable (fun y : ℝ => cglLemma62MellinTransform w (1 + (y : ℂ) * I))
  simpa [Complex.VerticalIntegrable] using h

/-- `(e^{−u})^s = e^{−us}` for the complex power of a positive real. -/
theorem cpow_ofReal_exp_neg (u : ℝ) (s : ℂ) :
    ((Real.exp (-u) : ℝ) : ℂ) ^ s = Complex.exp (-(u : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  push_cast
  ring_nf

/-- **Mellin inversion of `w²` on `Re s = 1`, logarithmic form.**
`e^{−u} w(e^{−u})² = (1/2π) ∫ e^{iuy} H(1+iy) dy`. -/
theorem cglGM_logSquaredCutoff_eq_mellinLine (w : CGLRealSmoothBump) (u : ℝ) :
    ((Real.exp (-u) : ℝ) : ℂ) * (w.toCGLSmoothBump.value (Real.exp (-u)) *
        w.toCGLSmoothBump.value (Real.exp (-u))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, Complex.exp (((u * y : ℝ) : ℂ) * I) * cglGMMellinLine w y := by
  have hx : 0 < Real.exp (-u) := Real.exp_pos _
  have hsq : (cglSmoothBumpSquare w.toCGLSmoothBump : ℝ → ℂ) =
      fun y : ℝ => w.toCGLSmoothBump.value y * w.toCGLSmoothBump.value y := by
    funext y
    exact cglSmoothBumpSquare_apply w.toCGLSmoothBump y
  have hinv := mellinInv_mellin_eq (1 : ℝ)
    (fun y : ℝ => w.toCGLSmoothBump.value y * w.toCGLSmoothBump.value y) hx
    (by rw [← hsq]; exact mellinConvergent_schwartz _ (by norm_num))
    (cglLemma62_mellinTransform_verticalIntegrable w 1)
    (by rw [← hsq]; exact (cglSmoothBumpSquare w.toCGLSmoothBump).continuous.continuousAt)
  rw [← hinv, mellinInv, Complex.real_smul, ← mul_assoc, mul_comm _ ((1 / (2 * Real.pi) : ℝ) : ℂ),
    mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, cpow_ofReal_exp_neg, cglGMMellinLine, cglLemma62MellinTransform]
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The phase of `ĥ_t` in the logarithmic variable. -/
def cglGMLogPhase (t ξ u : ℝ) : ℂ :=
  Complex.exp (((-(t * u) : ℝ) : ℂ) * I) *
    Complex.exp (((-2 * Real.pi * ξ * Real.exp (-u) : ℝ) : ℂ) * I)

theorem continuous_cglGMLogPhase (t ξ : ℝ) : Continuous (cglGMLogPhase t ξ) := by
  unfold cglGMLogPhase
  fun_prop

theorem norm_cglGMLogPhase (t ξ u : ℝ) : ‖cglGMLogPhase t ξ u‖ = 1 := by
  rw [cglGMLogPhase, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    one_mul]

/-- **Support restriction.** For `a ≤ −log 2` and `0 ≤ b`,
`ĥ_t(ξ) = ∫_a^b e^{−itu} e(−ξe^{−u}) · e^{−u} w(e^{−u})² du`. -/
theorem cglGM_fourier_eq_intervalIntegral (w : CGLRealSmoothBump) (t ξ a b : ℝ)
    (ha : a ≤ -Real.log 2) (hb : 0 ≤ b) :
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ξ =
      ∫ u in a..b, cglGMLogPhase t ξ u * (((Real.exp (-u) : ℝ) : ℂ) *
        (w.toCGLSmoothBump.value (Real.exp (-u)) * w.toCGLSmoothBump.value (Real.exp (-u)))) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hab : a ≤ b := by linarith
  rw [cglSmoothBumpHt_fourier_eq_logFourier, Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
  · refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    simp only [cglLogFourierAmplitude, cglFourierAmplitude, cglGMLogPhase, smul_eq_mul,
      Complex.real_smul]
    have harg : (-2 * Real.pi * u * (t / (2 * Real.pi)) : ℝ) = -(t * u) := by
      field_simp
    rw [harg]
    ring
  · intro u hu
    have hzero := cglLogFourierAmplitude_eq_zero_of_not_mem w.toCGLSmoothBump ξ u
      (fun hmem => hu ⟨ha.trans hmem.1, hmem.2.trans hb⟩)
    rw [hzero, smul_zero]

/-- The Fubini integrand `e^{−itu} e(−ξe^{−u}) e^{iuy} H(1+iy)`. -/
def cglGMFubiniIntegrand (w : CGLRealSmoothBump) (t ξ u y : ℝ) : ℂ :=
  cglGMLogPhase t ξ u * (Complex.exp (((u * y : ℝ) : ℂ) * I) * cglGMMellinLine w y)

theorem continuous_cglGMFubiniIntegrand (w : CGLRealSmoothBump) (t ξ : ℝ) :
    Continuous (Function.uncurry (cglGMFubiniIntegrand w t ξ)) := by
  unfold cglGMFubiniIntegrand
  have h1 : Continuous fun p : ℝ × ℝ => cglGMLogPhase t ξ p.1 :=
    (continuous_cglGMLogPhase t ξ).comp continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => cglGMMellinLine w p.2 :=
    (continuous_cglGMMellinLine w).comp continuous_snd
  exact h1.mul ((by fun_prop : Continuous fun p : ℝ × ℝ =>
    Complex.exp (((p.1 * p.2 : ℝ) : ℂ) * I)).mul h2)

theorem norm_cglGMFubiniIntegrand (w : CGLRealSmoothBump) (t ξ u y : ℝ) :
    ‖cglGMFubiniIntegrand w t ξ u y‖ = ‖cglGMMellinLine w y‖ := by
  rw [cglGMFubiniIntegrand, norm_mul, norm_mul, norm_cglGMLogPhase,
    Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]

/-- The Fubini integrand is integrable on `[a,b] × ℝ`. -/
theorem integrable_cglGMFubiniIntegrand (w : CGLRealSmoothBump) (t ξ a b : ℝ) :
    Integrable (Function.uncurry (cglGMFubiniIntegrand w t ξ))
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hdom : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖cglGMMellinLine w p.2‖)
      ((volume.restrict (Ioc a b)).prod volume) :=
    (integrable_const (1 : ℝ)).mul_prod (integrable_cglGMMellinLine w).norm
  refine hdom.mono' (continuous_cglGMFubiniIntegrand w t ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  simp [Function.uncurry, norm_cglGMFubiniIntegrand]

/-- **Fubini.** For `a ≤ −log 2 ≤ 0 ≤ b`,
`ĥ_t(ξ) = (1/2π) ∫ H(1+iy) ∫_a^b e^{−i(t−y)u} e(−ξe^{−u}) du dy`. -/
theorem cglGM_fourier_eq_mellinLine_integral (w : CGLRealSmoothBump) (t ξ a b : ℝ)
    (ha : a ≤ -Real.log 2) (hb : 0 ≤ b) :
    𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ξ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, cglGMMellinLine w y * ∫ u in a..b, cglGMLogPhase (t - y) ξ u := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hab : a ≤ b := by linarith
  rw [cglGM_fourier_eq_intervalIntegral w t ξ a b ha hb]
  simp_rw [cglGM_logSquaredCutoff_eq_mellinLine]
  -- pull the constant and the `u`-phase inside the `y`-integral
  have hin : ∀ u : ℝ, cglGMLogPhase t ξ u * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ y : ℝ, Complex.exp (((u * y : ℝ) : ℂ) * I) * cglGMMellinLine w y) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, cglGMFubiniIntegrand w t ξ u y := by
    intro u
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [cglGMFubiniIntegrand]
    ring
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab,
    integral_integral_swap (integrable_cglGMFubiniIntegrand w t ξ a b)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [cglGMFubiniIntegrand, cglGMLogPhase]
  have hphase : Complex.exp (((-(t * u) : ℝ) : ℂ) * I) * Complex.exp (((u * y : ℝ) : ℂ) * I) =
      Complex.exp (((-((t - y) * u) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hphase]
  ring

/-- **Translation.** For `m, N > 0`, `x = log(mN) − u` turns the inner integral over
`[log m − log 2M, log m]` into `e^{−iρ log(mN)} K(ρ; log N, log 2MN)`. -/
theorem cglGM_innerIntegral_eq_phaseIntegral (ρ m N M : ℝ) (hm : 0 < m) (hN : 0 < N)
    (hM : 0 < M) :
    ∫ u in (Real.log m - Real.log (2 * M))..(Real.log m), cglGMLogPhase ρ (m * N) u =
      Complex.exp (((-(ρ * Real.log (m * N)) : ℝ) : ℂ) * I) *
        cglGMReflectionPhaseIntegral ρ (Real.log N) (Real.log (2 * M * N)) := by
  set d : ℝ := Real.log (m * N) with hd
  have hdm : d = Real.log m + Real.log N := by
    rw [hd, Real.log_mul hm.ne' hN.ne']
  have h2MN : Real.log (2 * M * N) = Real.log N + Real.log (2 * M) := by
    rw [Real.log_mul (by positivity) hN.ne']; ring
  unfold cglGMReflectionPhaseIntegral
  rw [← intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_left (a := Real.log m - Real.log (2 * M))
    (b := Real.log m)
    (fun x => Complex.exp (((-(ρ * d) : ℝ) : ℂ) * I) *
      Complex.exp ((cglGMReflectionPhase ρ x : ℂ) * I)) d
  rw [show d - Real.log m = Real.log N by rw [hdm]; ring,
    show d - (Real.log m - Real.log (2 * M)) = Real.log (2 * M * N) by rw [hdm, h2MN]; ring]
    at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [cglGMLogPhase, cglGMReflectionPhase]
  have hexp : Real.exp (d - u) = m * N * Real.exp (-u) := by
    rw [sub_eq_add_neg, Real.exp_add, hd, Real.exp_log (by positivity)]
  rw [hexp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `K(ρ; log N, log 2MN)` is continuous in `ρ`. -/
theorem continuous_cglGMReflectionPhaseIntegral (α β : ℝ) :
    Continuous fun ρ => cglGMReflectionPhaseIntegral ρ α β := by
  unfold cglGMReflectionPhaseIntegral cglGMReflectionPhase
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) α β

/-- The `m`-th reflected integrand `H(1+iy) e^{−i(t−y) log(mN)} K(t−y)`. -/
def cglGMReflectedTerm (w : CGLRealSmoothBump) (t N M m y : ℝ) : ℂ :=
  cglGMMellinLine w y * (Complex.exp (((-((t - y) * Real.log (m * N)) : ℝ) : ℂ) * I) *
    cglGMReflectionPhaseIntegral (t - y) (Real.log N) (Real.log (2 * M * N)))

theorem integrable_cglGMReflectedTerm (w : CGLRealSmoothBump) (t N M m : ℝ) :
    Integrable (cglGMReflectedTerm w t N M m) := by
  set L : ℝ := |Real.log (2 * M * N) - Real.log N|
  have hdom : Integrable fun y => L * ‖cglGMMellinLine w y‖ :=
    (integrable_cglGMMellinLine w).norm.const_mul L
  have hcont : Continuous (cglGMReflectedTerm w t N M m) := by
    unfold cglGMReflectedTerm
    have hphase : Continuous fun y : ℝ =>
        Complex.exp (((-((t - y) * Real.log (m * N)) : ℝ) : ℂ) * I) := by fun_prop
    exact (continuous_cglGMMellinLine w).mul (hphase.mul
      ((continuous_cglGMReflectionPhaseIntegral _ _).comp (by fun_prop)))
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [cglGMReflectedTerm, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_cglGMReflectionPhaseIntegral_le_length _ _ _)
    (norm_nonneg _)

/-- **Exact reflection identity (Guth–Maynard, proof of Lemma 6.2).** For `N > 0`,
`Σ_{m=1}^{M} ĥ_t(mN) = (1/2π) ∫ H(1+iy) (Σ_{m=1}^{M} e^{−i(t−y) log(mN)}) K(t−y; log N, log 2MN) dy`. -/
theorem cglGM_sum_fourier_eq_reflected (w : CGLRealSmoothBump) (t N : ℝ) (hN : 0 < N)
    (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ) ((m : ℝ) * N) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, ∑ m ∈ Finset.Icc 1 M, cglGMReflectedTerm w t N M m y := by
  rw [integral_finsetSum _ fun (m : ℕ) _ => integrable_cglGMReflectedTerm w t N M m,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hm1.trans hmM
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have ha : Real.log m - Real.log (2 * M) ≤ -Real.log 2 := by
    have : Real.log (2 * m) ≤ Real.log (2 * M) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hm0.ne'] at this
    linarith
  have hb : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  rw [cglGM_fourier_eq_mellinLine_integral w t _ _ _ ha hb]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [cglGMReflectedTerm, cglGM_innerIntegral_eq_phaseIntegral (t - y) m N M hm0 hN hM0]

end RHTower
