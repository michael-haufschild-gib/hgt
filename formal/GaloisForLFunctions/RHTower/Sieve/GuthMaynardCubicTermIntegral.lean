import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum
import GaloisForLFunctions.RHTower.ChenGuptaLiHt

/-!
# The cubic term `I_m` as an oscillatory integral (Guth–Maynard (7.3) and (7.4))

For the CGL bump `w` (support `[1, 2]`), `h_t(u) = w(u)² u^{it}` and a finite `W ⊂ ℝ`, the
nonzero-frequency terms of the cubic trace (Lemma 4.5 of arXiv 2405.20552) are

`I_m = N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)`   (`cubicTerm`).

Expanding the three Fourier integrals and summing over `W` gives (7.3)

`I_m = N³ ∫_{ℝ³} e(−N m·u) w(u₁)²w(u₂)²w(u₃)² R(u₁/u₃) R(u₂/u₁) R(u₃/u₂) du`,

and the substitution `u₁ = u₃v₁`, `u₂ = u₃v₂` (Jacobian `u₃²`) followed by Fubini gives (7.4)

`I_m = N³ ∫_{ℝ²} J(v, N(m₁v₁ + m₂v₂ + m₃)) R(v₁) R(v₂/v₁) R(1/v₂) dv`,
`J(v, ξ) = ∫ e(−ξu) u² w(u)² w(uv₁)² w(uv₂)² du`,

the form in which the `u₃`-integral is isolated for the non-stationary phase argument of
Proposition 7.1. Both identities are proved for each triple `(t₁, t₂, t₃)` with continuous,
compactly supported integrands (so Fubini needs no information on `R`), and then summed.
-/

set_option autoImplicit false

open MeasureTheory Set Complex
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Definitions -/

/-- `ĥ_t(ξ) = ∫ e(−ξu) w(u)² u^{it} du` for the CGL bump `w`. -/
def bumpFourier (w : CGLSmoothBump) (t ξ : ℝ) : ℂ :=
  𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ

/-- `I_m = N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)`. -/
def cubicTerm (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) : ℂ :=
  (N : ℂ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    bumpFourier w (t₁ - t₂) (m₁ * N) * bumpFourier w (t₂ - t₃) (m₂ * N) *
      bumpFourier w (t₃ - t₁) (m₃ * N)

/-- The Fourier kernel `e(−uξ) = exp(−2πiuξ)`. -/
def fourierKernel (u ξ : ℝ) : ℂ :=
  Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I)

/-- The Mellin phase `v^{it} = exp(i t log v)`, the summand of `R(v)`. -/
def lagPhase (t v : ℝ) : ℂ :=
  Complex.exp (Complex.I * t * Real.log v)

/-- The amplitude `w₂(u, v₁, v₂) = u² w(u)² w(uv₁)² w(uv₂)²` of (7.4). -/
def cubicAmplitude (w : CGLSmoothBump) (p : ℝ × ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ 2 * w.value p.1 ^ 2 * w.value (p.1 * p.2.1) ^ 2 * w.value (p.1 * p.2.2) ^ 2

/-- The inner integral `J(v, ξ) = ∫ e(−ξu) w₂(u, v) du` of (7.4). -/
def cubicPhaseIntegral (w : CGLSmoothBump) (v : ℝ × ℝ) (ξ : ℝ) : ℂ :=
  𝓕 (fun u => cubicAmplitude w (u, v)) ξ

/-- The linear form `m₁v₁ + m₂v₂ + m₃` whose size decides the cancellation in `J`. -/
def cubicLinearForm (m₁ m₂ m₃ : ℤ) (v : ℝ × ℝ) : ℝ :=
  m₁ * v.1 + m₂ * v.2 + m₃

/-- `R(v₁) R(v₂/v₁) R(1/v₂)`, the lag-sum factor of (7.4). -/
def lagTriple (W : Finset ℝ) (v : ℝ × ℝ) : ℂ :=
  lagSum W v.1 * lagSum W (v.2 / v.1) * lagSum W v.2⁻¹

/-! ### Elementary identities -/

theorem fourier_eq_integral_fourierKernel (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ u, fourierKernel u ξ * f u := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rfl

theorem continuous_fourierKernel (ξ : ℝ) : Continuous fun u => fourierKernel u ξ := by
  unfold fourierKernel; fun_prop

/-- `e(−u₁ξ₁) e(−u₂ξ₂) e(−u₃ξ₃)` collapses on the ray `u₁ = u₃v₁`, `u₂ = u₃v₂`. -/
theorem fourierKernel_mul_mul (u v₁ v₂ ξ₁ ξ₂ ξ₃ : ℝ) :
    fourierKernel (u * v₁) ξ₁ * fourierKernel (u * v₂) ξ₂ * fourierKernel u ξ₃ =
      fourierKernel u (ξ₁ * v₁ + ξ₂ * v₂ + ξ₃) := by
  simp only [fourierKernel, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `e(−u₁m₁N) e(−u₂m₂N) e(−u₃m₃N) = e(−N m·u)`. -/
theorem fourierKernel_mul_mul_eq (u₁ u₂ u₃ a₁ a₂ a₃ N : ℝ) :
    fourierKernel u₁ (a₁ * N) * fourierKernel u₂ (a₂ * N) * fourierKernel u₃ (a₃ * N) =
      fourierKernel (a₁ * u₁ + a₂ * u₂ + a₃ * u₃) N := by
  simp only [fourierKernel, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem lagSum_eq_sum_lagPhase (W : Finset ℝ) (v : ℝ) : lagSum W v = ∑ t ∈ W, lagPhase t v := rfl

/-- `h_t(x) = w(x)² x^{it}`. -/
theorem cglSmoothBumpHt_eq (w : CGLSmoothBump) (t x : ℝ) :
    cglSmoothBumpHt w t x = w.value x ^ 2 * lagPhase t x := by
  rw [cglSmoothBumpHt_apply, cglSmoothBumpHtValue, cglMellinPhase, lagPhase, sq]
  congr 2; ring

theorem bump_value_zero (w : CGLSmoothBump) : w.value 0 = 0 :=
  w.outside_support 0 (by norm_num)

theorem cglSmoothBumpHt_eq_zero (w : CGLSmoothBump) (t : ℝ) {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) :
    cglSmoothBumpHt w t x = 0 := by
  rw [cglSmoothBumpHt_eq, w.outside_support x hx]; simp

/-- If `u ∈ [1, 2]` and `uv ∈ [1, 2]` then `v ∈ [1/2, 2]`. -/
theorem mem_Icc_half_two_of_mul {u v : ℝ} (hu : u ∈ Icc (1 : ℝ) 2) (huv : u * v ∈ Icc (1 : ℝ) 2) :
    v ∈ Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨hu₁, hu₂⟩ := hu
  obtain ⟨h₁, h₂⟩ := huv
  constructor <;> nlinarith

/-- `w₂(u, v)` vanishes unless `u ∈ [1, 2]` and `v ∈ [1/2, 2]²`. -/
theorem cubicAmplitude_eq_zero (w : CGLSmoothBump) {p : ℝ × ℝ × ℝ}
    (hp : p ∉ Icc (1 : ℝ) 2 ×ˢ (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2)) :
    cubicAmplitude w p = 0 := by
  unfold cubicAmplitude
  by_cases h1 : p.1 ∈ Icc (1 : ℝ) 2
  · by_cases h2 : p.1 * p.2.1 ∈ Icc (1 : ℝ) 2
    · have h3 : p.1 * p.2.2 ∉ Icc (1 : ℝ) 2 := fun h3 =>
        hp ⟨h1, mem_Icc_half_two_of_mul h1 h2, mem_Icc_half_two_of_mul h1 h3⟩
      rw [w.outside_support _ h3]; simp
    · rw [w.outside_support _ h2]; simp
  · rw [w.outside_support _ h1]; simp

theorem contDiff_cubicAmplitude (w : CGLSmoothBump) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cubicAmplitude w) := by
  unfold cubicAmplitude
  have hw := w.smooth
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) fun p : ℝ × ℝ × ℝ => w.value p.1 := hw.comp contDiff_fst
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) fun p : ℝ × ℝ × ℝ => w.value (p.1 * p.2.1) :=
    hw.comp (contDiff_fst.mul (contDiff_fst.comp contDiff_snd))
  have h3 : ContDiff ℝ (↑(⊤ : ℕ∞)) fun p : ℝ × ℝ × ℝ => w.value (p.1 * p.2.2) :=
    hw.comp (contDiff_fst.mul (contDiff_snd.comp contDiff_snd))
  have h0 : ContDiff ℝ (↑(⊤ : ℕ∞)) fun p : ℝ × ℝ × ℝ => (p.1 : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact ((h0.pow 2).mul (h1.pow 2)).mul (h2.pow 2) |>.mul (h3.pow 2)

theorem hasCompactSupport_cubicAmplitude (w : CGLSmoothBump) :
    HasCompactSupport (cubicAmplitude w) :=
  HasCompactSupport.intro (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    fun _ hp => cubicAmplitude_eq_zero w hp

/-- `J(v, ξ) = 0` unless `v ∈ [1/2, 2]²`. -/
theorem cubicPhaseIntegral_eq_zero (w : CGLSmoothBump) {v : ℝ × ℝ}
    (hv : v ∉ Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2) (ξ : ℝ) :
    cubicPhaseIntegral w v ξ = 0 := by
  have hzero : (fun u => cubicAmplitude w (u, v)) = fun _ => 0 := by
    funext u
    exact cubicAmplitude_eq_zero w fun hp => hv hp.2
  rw [cubicPhaseIntegral, hzero, fourier_eq_integral_fourierKernel]
  simp

/-- The phase identity `u^{ic} (uv₁)^{ia} (uv₂)^{ib} = v₁^{ia} v₂^{ib}` when `a + b + c = 0`. -/
theorem lagPhase_mul_mul {a b c : ℝ} (habc : a + b + c = 0) {u v₁ v₂ : ℝ} (hu : u ≠ 0)
    (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) :
    lagPhase c u * lagPhase a (u * v₁) * lagPhase b (u * v₂) =
      lagPhase a v₁ * lagPhase b v₂ := by
  simp only [lagPhase, ← Complex.exp_add, Real.log_mul hu h₁, Real.log_mul hu h₂]
  congr 1
  have : (c : ℂ) = -a - b := by
    have := congrArg (fun x : ℝ => (x : ℂ)) habc; push_cast at this; linear_combination this
  rw [this]; push_cast; ring

/-- The phase identity `u₁^{i(t₁−t₂)} u₂^{i(t₂−t₃)} u₃^{i(t₃−t₁)} = (u₁/u₃)^{it₁} (u₂/u₁)^{it₂}
(u₃/u₂)^{it₃}`. -/
theorem lagPhase_sub_mul {u₁ u₂ u₃ : ℝ} (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) (h₃ : u₃ ≠ 0)
    (t₁ t₂ t₃ : ℝ) :
    lagPhase (t₁ - t₂) u₁ * lagPhase (t₂ - t₃) u₂ * lagPhase (t₃ - t₁) u₃ =
      lagPhase t₁ (u₁ / u₃) * lagPhase t₂ (u₂ / u₁) * lagPhase t₃ (u₃ / u₂) := by
  simp only [lagPhase, ← Complex.exp_add, Real.log_div h₁ h₃, Real.log_div h₂ h₁,
    Real.log_div h₃ h₂]
  congr 1; push_cast; ring

/-- The phase identity `v₁^{i(t₁−t₂)} v₂^{i(t₂−t₃)} = v₁^{it₁} (v₂/v₁)^{it₂} (1/v₂)^{it₃}`. -/
theorem lagPhase_sub_mul_ray {v₁ v₂ : ℝ} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (t₁ t₂ t₃ : ℝ) :
    lagPhase (t₁ - t₂) v₁ * lagPhase (t₂ - t₃) v₂ =
      lagPhase t₁ v₁ * lagPhase t₂ (v₂ / v₁) * lagPhase t₃ v₂⁻¹ := by
  simp only [lagPhase, ← Complex.exp_add, Real.log_div h₂ h₁, Real.log_inv]
  congr 1; push_cast; ring

/-- `Σ_{t₁,t₂,t₃ ∈ W} f(t₁) g(t₂) h(t₃) = (Σ f)(Σ g)(Σ h)`. -/
theorem sum_sum_sum_mul_mul (W : Finset ℝ) (f g h : ℝ → ℂ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f t₁ * g t₂ * h t₃ =
      (∑ t ∈ W, f t) * (∑ t ∈ W, g t) * ∑ t ∈ W, h t := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [Finset.mul_sum]

/-- A triple finite sum commutes with the integral of integrable summands. -/
theorem integral_sum_sum_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} (W : Finset ℝ)
    {f : ℝ → ℝ → ℝ → α → ℂ} (hf : ∀ a b c, Integrable (f a b c) μ) :
    ∫ x, ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c x ∂μ =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∫ x, f a b c x ∂μ := by
  have h2 : ∀ a b, Integrable (fun x => ∑ c ∈ W, f a b c x) μ := fun a b =>
    integrable_finsetSum W fun c _ => hf a b c
  have h1 : ∀ a, Integrable (fun x => ∑ b ∈ W, ∑ c ∈ W, f a b c x) μ := fun a =>
    integrable_finsetSum W fun b _ => h2 a b
  rw [integral_finsetSum W fun a _ => h1 a]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum W fun b _ => h2 a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum W fun c _ => hf a b c]

/-! ### One triple of frequencies -/

/-- The weighted kernel `e(−uξ) h_t(u)` integrated in `ĥ_t(ξ)`. -/
def kernelTerm (w : CGLSmoothBump) (t ξ u : ℝ) : ℂ :=
  fourierKernel u ξ * cglSmoothBumpHt w t u

theorem continuous_kernelTerm (w : CGLSmoothBump) (t ξ : ℝ) : Continuous (kernelTerm w t ξ) :=
  (continuous_fourierKernel ξ).mul (cglSmoothBumpHt w t).continuous

theorem kernelTerm_eq_zero (w : CGLSmoothBump) (t ξ : ℝ) {u : ℝ} (hu : u ∉ Icc (1 : ℝ) 2) :
    kernelTerm w t ξ u = 0 := by
  rw [kernelTerm, cglSmoothBumpHt_eq_zero w t hu, mul_zero]

theorem bumpFourier_eq_integral (w : CGLSmoothBump) (t ξ : ℝ) :
    bumpFourier w t ξ = ∫ u, kernelTerm w t ξ u :=
  fourier_eq_integral_fourierKernel _ _

/-- The integrand of one frequency triple after the substitution `u₁ = uv₁`, `u₂ = uv₂`. -/
def rayIntegrand (w : CGLSmoothBump) (a b c ξ₁ ξ₂ ξ₃ : ℝ) (p : ℝ × ℝ × ℝ) : ℂ :=
  kernelTerm w c ξ₃ p.1 *
    ((p.1 : ℂ) ^ 2 * (kernelTerm w a ξ₁ (p.1 * p.2.1) * kernelTerm w b ξ₂ (p.1 * p.2.2)))

theorem integrable_rayIntegrand (w : CGLSmoothBump) (a b c ξ₁ ξ₂ ξ₃ : ℝ) :
    Integrable (rayIntegrand w a b c ξ₁ ξ₂ ξ₃) := by
  have hc : Continuous (rayIntegrand w a b c ξ₁ ξ₂ ξ₃) := by
    have k₁ := continuous_kernelTerm w a ξ₁
    have k₂ := continuous_kernelTerm w b ξ₂
    have k₃ := continuous_kernelTerm w c ξ₃
    unfold rayIntegrand
    fun_prop
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc (1 : ℝ) 2 ×ˢ (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2))) fun p hp => ?_)
  unfold rayIntegrand
  by_cases h1 : p.1 ∈ Icc (1 : ℝ) 2
  · by_cases h2 : p.1 * p.2.1 ∈ Icc (1 : ℝ) 2
    · have h3 : p.1 * p.2.2 ∉ Icc (1 : ℝ) 2 := fun h3 =>
        hp ⟨h1, mem_Icc_half_two_of_mul h1 h2, mem_Icc_half_two_of_mul h1 h3⟩
      rw [kernelTerm_eq_zero w b ξ₂ h3]; simp
    · rw [kernelTerm_eq_zero w a ξ₁ h2]; simp
  · rw [kernelTerm_eq_zero w c ξ₃ h1]; simp

/-- Pointwise form of the ray integrand: the phase factors off `u` exactly when `a + b + c = 0`. -/
theorem rayIntegrand_eq (w : CGLSmoothBump) {a b c : ℝ} (habc : a + b + c = 0)
    (ξ₁ ξ₂ ξ₃ u : ℝ) (v : ℝ × ℝ) :
    rayIntegrand w a b c ξ₁ ξ₂ ξ₃ (u, v) = lagPhase a v.1 * lagPhase b v.2 *
      (fourierKernel u (ξ₁ * v.1 + ξ₂ * v.2 + ξ₃) * cubicAmplitude w (u, v)) := by
  have w0 := bump_value_zero w
  unfold rayIntegrand kernelTerm cubicAmplitude
  simp only [cglSmoothBumpHt_eq]
  by_cases hu : u = 0
  · subst hu; simp [w0]
  by_cases h₁ : v.1 = 0
  · simp [h₁, w0]
  by_cases h₂ : v.2 = 0
  · simp [h₂, w0]
  have hK := fourierKernel_mul_mul u v.1 v.2 ξ₁ ξ₂ ξ₃
  have hP := lagPhase_mul_mul habc hu h₁ h₂
  calc fourierKernel u ξ₃ * (w.value u ^ 2 * lagPhase c u) *
        ((u : ℂ) ^ 2 * (fourierKernel (u * v.1) ξ₁ * (w.value (u * v.1) ^ 2 *
          lagPhase a (u * v.1)) * (fourierKernel (u * v.2) ξ₂ * (w.value (u * v.2) ^ 2 *
            lagPhase b (u * v.2)))))
      = (fourierKernel (u * v.1) ξ₁ * fourierKernel (u * v.2) ξ₂ * fourierKernel u ξ₃) *
          (lagPhase c u * lagPhase a (u * v.1) * lagPhase b (u * v.2)) *
            ((u : ℂ) ^ 2 * w.value u ^ 2 * w.value (u * v.1) ^ 2 * w.value (u * v.2) ^ 2) := by
        ring
    _ = _ := by rw [hK, hP]; ring

/-- **One triple of (7.4).** For `a + b + c = 0`,
`ĥ_a(ξ₁) ĥ_b(ξ₂) ĥ_c(ξ₃) = ∫_{ℝ²} J(v, ξ₁v₁ + ξ₂v₂ + ξ₃) v₁^{ia} v₂^{ib} dv`. -/
theorem bumpFourier_mul_mul_eq_integral_ray (w : CGLSmoothBump) {a b c : ℝ} (habc : a + b + c = 0)
    (ξ₁ ξ₂ ξ₃ : ℝ) :
    bumpFourier w a ξ₁ * bumpFourier w b ξ₂ * bumpFourier w c ξ₃ =
      ∫ v : ℝ × ℝ, cubicPhaseIntegral w v (ξ₁ * v.1 + ξ₂ * v.2 + ξ₃) *
        (lagPhase a v.1 * lagPhase b v.2) := by
  have w0 := bump_value_zero w
  set F : ℝ × ℝ × ℝ → ℂ := rayIntegrand w a b c ξ₁ ξ₂ ξ₃ with hF
  -- the product of the first two integrals is one integral over `ℝ²`
  have h12 : bumpFourier w a ξ₁ * bumpFourier w b ξ₂ =
      ∫ x : ℝ × ℝ, kernelTerm w a ξ₁ x.1 * kernelTerm w b ξ₂ x.2 := by
    rw [bumpFourier_eq_integral, bumpFourier_eq_integral]
    exact (integral_prod_mul (μ := volume) (ν := volume) _ _).symm
  -- for fixed `u`, rescale the `ℝ²` integral by `u` (Jacobian `u²`)
  have hray : ∀ u : ℝ, (∫ x : ℝ × ℝ, kernelTerm w a ξ₁ x.1 * kernelTerm w b ξ₂ x.2) *
      kernelTerm w c ξ₃ u = ∫ v : ℝ × ℝ, F (u, v) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [hF, rayIntegrand, kernelTerm, cglSmoothBumpHt_apply, cglSmoothBumpHtValue, w0]
    have hscale := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
      (fun x : ℝ × ℝ => kernelTerm w a ξ₁ x.1 * kernelTerm w b ξ₂ x.2) u
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Module.finrank_prod,
      Module.finrank_self] at hscale
    rw [show (1 + 1 : ℕ) = 2 from rfl, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg u))] at hscale
    have : (∫ x : ℝ × ℝ, kernelTerm w a ξ₁ x.1 * kernelTerm w b ξ₂ x.2) =
        (u : ℂ) ^ 2 * ∫ v : ℝ × ℝ, kernelTerm w a ξ₁ (u * v.1) * kernelTerm w b ξ₂ (u * v.2) := by
      rw [hscale, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [mul_inv_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hu)), one_mul]
    rw [this, hF]
    simp only [rayIntegrand]
    rw [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only; ring
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (ℝ × ℝ))) (f := fun u v => F (u, v))
    (by exact integrable_rayIntegrand w a b c ξ₁ ξ₂ ξ₃)
  calc bumpFourier w a ξ₁ * bumpFourier w b ξ₂ * bumpFourier w c ξ₃
      = ∫ u, (∫ x : ℝ × ℝ, kernelTerm w a ξ₁ x.1 * kernelTerm w b ξ₂ x.2) *
          kernelTerm w c ξ₃ u := by
        rw [h12, bumpFourier_eq_integral w c, integral_const_mul]
    _ = ∫ u, ∫ v : ℝ × ℝ, F (u, v) := integral_congr_ae (Filter.Eventually.of_forall hray)
    _ = ∫ v : ℝ × ℝ, ∫ u, F (u, v) := hswap
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [hF, rayIntegrand_eq w habc, cubicPhaseIntegral,
          fourier_eq_integral_fourierKernel]
        rw [integral_const_mul, mul_comm]

/-- The integrand of one triple of (7.4) is integrable on `ℝ²`. -/
theorem integrable_cubicPhaseIntegral_mul_lagPhase (w : CGLSmoothBump) {a b c : ℝ}
    (habc : a + b + c = 0) (ξ₁ ξ₂ ξ₃ : ℝ) :
    Integrable fun v : ℝ × ℝ => cubicPhaseIntegral w v (ξ₁ * v.1 + ξ₂ * v.2 + ξ₃) *
      (lagPhase a v.1 * lagPhase b v.2) := by
  have h := (integrable_rayIntegrand w a b c ξ₁ ξ₂ ξ₃).integral_prod_right
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [rayIntegrand_eq w habc, cubicPhaseIntegral, fourier_eq_integral_fourierKernel]
  rw [integral_const_mul, mul_comm]

/-! ### The identities (7.4) and (7.3) -/

/-- `J(v, ξ) R(v₁) R(v₂/v₁) R(1/v₂) = Σ_{t₁,t₂,t₃} J(v, ξ) v₁^{i(t₁−t₂)} v₂^{i(t₂−t₃)}`. -/
theorem cubicPhaseIntegral_mul_lagTriple (w : CGLSmoothBump) (W : Finset ℝ) (v : ℝ × ℝ) (ξ : ℝ) :
    cubicPhaseIntegral w v ξ * lagTriple W v = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      cubicPhaseIntegral w v ξ * (lagPhase (t₁ - t₂) v.1 * lagPhase (t₂ - t₃) v.2) := by
  by_cases hv : v ∈ Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2
  · have h₁ : v.1 ≠ 0 := by have := hv.1.1; positivity
    have h₂ : v.2 ≠ 0 := by have := hv.2.1; positivity
    rw [lagTriple, lagSum_eq_sum_lagPhase, lagSum_eq_sum_lagPhase, lagSum_eq_sum_lagPhase,
      ← sum_sum_sum_mul_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ =>
      Finset.sum_congr rfl fun t₃ _ => ?_
    rw [lagPhase_sub_mul_ray h₁ h₂]
  · simp [cubicPhaseIntegral_eq_zero w hv]

/-- **Guth–Maynard (7.4).** `I_m = N³ ∫_{ℝ²} J(v, N(m₁v₁ + m₂v₂ + m₃)) R(v₁) R(v₂/v₁) R(1/v₂) dv`,
with `J(v, ξ) = ∫ e(−ξu) u² w(u)² w(uv₁)² w(uv₂)² du`. -/
theorem cubicTerm_eq_integral_ray (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) :
    cubicTerm w W N m₁ m₂ m₃ = (N : ℂ) ^ 3 * ∫ v : ℝ × ℝ,
      cubicPhaseIntegral w v (N * cubicLinearForm m₁ m₂ m₃ v) * lagTriple W v := by
  have hL : ∀ v : ℝ × ℝ, N * cubicLinearForm m₁ m₂ m₃ v =
      (m₁ * N) * v.1 + (m₂ * N) * v.2 + m₃ * N := fun v => by
    unfold cubicLinearForm; ring
  have habc : ∀ t₁ t₂ t₃ : ℝ, (t₁ - t₂) + (t₂ - t₃) + (t₃ - t₁) = 0 := fun _ _ _ => by ring
  unfold cubicTerm
  congr 1
  simp only [hL, cubicPhaseIntegral_mul_lagTriple]
  rw [integral_sum_sum_sum W fun t₁ t₂ t₃ =>
    integrable_cubicPhaseIntegral_mul_lagPhase w (habc t₁ t₂ t₃) _ _ _]
  refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ =>
    Finset.sum_congr rfl fun t₃ _ => ?_
  exact bumpFourier_mul_mul_eq_integral_ray w (habc t₁ t₂ t₃) _ _ _

/-- The integrand of one triple of (7.3). -/
def tripleIntegrand (w : CGLSmoothBump) (a b c ξ₁ ξ₂ ξ₃ : ℝ) (u : ℝ × ℝ × ℝ) : ℂ :=
  kernelTerm w a ξ₁ u.1 * (kernelTerm w b ξ₂ u.2.1 * kernelTerm w c ξ₃ u.2.2)

theorem integrable_tripleIntegrand (w : CGLSmoothBump) (a b c ξ₁ ξ₂ ξ₃ : ℝ) :
    Integrable (tripleIntegrand w a b c ξ₁ ξ₂ ξ₃) := by
  have hc : Continuous (tripleIntegrand w a b c ξ₁ ξ₂ ξ₃) := by
    have k₁ := continuous_kernelTerm w a ξ₁
    have k₂ := continuous_kernelTerm w b ξ₂
    have k₃ := continuous_kernelTerm w c ξ₃
    unfold tripleIntegrand
    fun_prop
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2))) fun u hu => ?_)
  unfold tripleIntegrand
  by_cases h1 : u.1 ∈ Icc (1 : ℝ) 2
  · by_cases h2 : u.2.1 ∈ Icc (1 : ℝ) 2
    · have h3 : u.2.2 ∉ Icc (1 : ℝ) 2 := fun h3 => hu ⟨h1, h2, h3⟩
      rw [kernelTerm_eq_zero w c ξ₃ h3]; simp
    · rw [kernelTerm_eq_zero w b ξ₂ h2]; simp
  · rw [kernelTerm_eq_zero w a ξ₁ h1]; simp

/-- **Guth–Maynard (7.3).**
`I_m = N³ ∫_{ℝ³} e(−N m·u) w(u₁)² w(u₂)² w(u₃)² R(u₁/u₃) R(u₂/u₁) R(u₃/u₂) du`. -/
theorem cubicTerm_eq_integral (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) (m₁ m₂ m₃ : ℤ) :
    cubicTerm w W N m₁ m₂ m₃ = (N : ℂ) ^ 3 * ∫ u : ℝ × ℝ × ℝ,
      fourierKernel (m₁ * u.1 + m₂ * u.2.1 + m₃ * u.2.2) N *
        (w.value u.1 ^ 2 * w.value u.2.1 ^ 2 * w.value u.2.2 ^ 2) *
          (lagSum W (u.1 / u.2.2) * lagSum W (u.2.1 / u.1) * lagSum W (u.2.2 / u.2.1)) := by
  have w0 := bump_value_zero w
  unfold cubicTerm
  congr 1
  -- each triple of Fourier integrals is one integral over `ℝ³`
  have htriple : ∀ a b c ξ₁ ξ₂ ξ₃ : ℝ, bumpFourier w a ξ₁ * bumpFourier w b ξ₂ *
      bumpFourier w c ξ₃ = ∫ u : ℝ × ℝ × ℝ, tripleIntegrand w a b c ξ₁ ξ₂ ξ₃ u := by
    intro a b c ξ₁ ξ₂ ξ₃
    have e1 := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (kernelTerm w b ξ₂) (kernelTerm w c ξ₃)
    have e2 := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
      (kernelTerm w a ξ₁) fun z => kernelTerm w b ξ₂ z.1 * kernelTerm w c ξ₃ z.2
    rw [← Measure.volume_eq_prod] at e1 e2
    rw [bumpFourier_eq_integral, bumpFourier_eq_integral, bumpFourier_eq_integral, mul_assoc,
      ← e1, ← e2]
    rfl
  simp only [htriple]
  rw [← integral_sum_sum_sum W fun t₁ t₂ t₃ => integrable_tripleIntegrand w _ _ _ _ _ _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [tripleIntegrand, kernelTerm, cglSmoothBumpHt_eq]
  by_cases h₁ : u.1 = 0
  · simp [h₁, w0]
  by_cases h₂ : u.2.1 = 0
  · simp [h₂, w0]
  by_cases h₃ : u.2.2 = 0
  · simp [h₃, w0]
  have hK := fourierKernel_mul_mul_eq u.1 u.2.1 u.2.2 m₁ m₂ m₃ N
  have hsum : ∀ t₁ t₂ t₃ : ℝ,
      fourierKernel u.1 (m₁ * N) * (w.value u.1 ^ 2 * lagPhase (t₁ - t₂) u.1) *
        (fourierKernel u.2.1 (m₂ * N) * (w.value u.2.1 ^ 2 * lagPhase (t₂ - t₃) u.2.1) *
          (fourierKernel u.2.2 (m₃ * N) * (w.value u.2.2 ^ 2 * lagPhase (t₃ - t₁) u.2.2))) =
      fourierKernel (m₁ * u.1 + m₂ * u.2.1 + m₃ * u.2.2) N *
        (w.value u.1 ^ 2 * w.value u.2.1 ^ 2 * w.value u.2.2 ^ 2) *
          (lagPhase t₁ (u.1 / u.2.2) * lagPhase t₂ (u.2.1 / u.1) * lagPhase t₃ (u.2.2 / u.2.1)) := by
    intro t₁ t₂ t₃
    rw [← hK, ← lagPhase_sub_mul h₁ h₂ h₃]
    ring
  rw [lagSum_eq_sum_lagPhase, lagSum_eq_sum_lagPhase, lagSum_eq_sum_lagPhase,
    ← sum_sum_sum_mul_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ =>
    Finset.sum_congr rfl fun t₃ _ => hsum t₁ t₂ t₃

end

end RHTower.GuthMaynard
