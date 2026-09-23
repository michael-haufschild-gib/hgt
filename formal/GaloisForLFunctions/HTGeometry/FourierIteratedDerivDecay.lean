import GaloisForLFunctions.HTGeometry.SmoothBlockWindow

/-!
# Fourier decay from iterated derivatives

For a `K` times continuously differentiable `f : ℝ → ℂ` whose derivatives up to order `K` are
integrable, `K`-fold integration by parts gives

`‖𝓕 f (ξ)‖ ≤ ‖f^{(K)}‖_{L¹} / (2π|ξ|)^K`,   equivalently   `‖∫ f(t) e^{-iξt} dt‖ ≤ ‖f^{(K)}‖_{L¹} / |ξ|^K`.

For a compactly supported smooth `f` every derivative is automatically integrable, and the `L¹`
norm of `f^{(K)}` is at most the length of the support times its supremum there.
-/

open Real MeasureTheory FourierTransform

namespace GaloisForLFunctions.HTGeometry

/-- The height oscillation `∫ f(t) e^{-iξt} dt` is the Fourier transform at `ξ/2π`. -/
theorem integral_mul_cexp_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    ∫ t, f t * Complex.exp (-(ξ * t) * Complex.I) = 𝓕 f (ξ / (2 * π)) := by
  rw [Real.fourier_real_eq]
  congr 1
  funext t
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- **Fourier decay from `K` integrable derivatives.** -/
theorem norm_fourier_le_of_iteratedDeriv (K : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ K f)
    (hint : ∀ n : ℕ, n ≤ K → Integrable (iteratedDeriv n f)) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (∫ t, ‖iteratedDeriv K f t‖) / (2 * π * |ξ|) ^ K := by
  have h := Real.fourier_iteratedDeriv (N := K) hf
    (fun n hn => hint n (by exact_mod_cast hn)) (n := K) le_rfl
  have hK : 𝓕 (iteratedDeriv K f) ξ = (2 * π * Complex.I * ξ) ^ K • 𝓕 f ξ := by rw [h]
  have hnorm : ‖(2 * π * Complex.I * (ξ : ℂ)) ^ K‖ = (2 * π * |ξ|) ^ K := by
    rw [norm_pow, Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  have hpos : 0 < (2 * π * |ξ|) ^ K := by
    have := abs_pos.mpr hξ
    positivity
  rw [le_div_iff₀ hpos, ← hnorm, mul_comm, ← norm_smul, ← hK]
  exact norm_fourier_le_integral_norm_smoothBlockWindow _ _

/-- **Height-oscillation decay from `K` integrable derivatives**, in the `exp(-iξt)`
normalisation. -/
theorem norm_integral_mul_cexp_le_of_iteratedDeriv (K : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ K f)
    (hint : ∀ n : ℕ, n ≤ K → Integrable (iteratedDeriv n f)) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖∫ t, f t * Complex.exp (-(ξ * t) * Complex.I)‖
      ≤ (∫ t, ‖iteratedDeriv K f t‖) / |ξ| ^ K := by
  rw [integral_mul_cexp_eq_fourier]
  have hξ' : ξ / (2 * π) ≠ 0 := div_ne_zero hξ (by positivity)
  refine (norm_fourier_le_of_iteratedDeriv K hf hint hξ').trans (le_of_eq ?_)
  congr 1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

/-- Iterated derivatives of a compactly supported function have compact support. -/
theorem HasCompactSupport.iteratedDeriv_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (n : ℕ) : HasCompactSupport (iteratedDeriv n f) := by
  have h : iteratedDeriv n f = (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ =>
      p (fun _ => (1 : ℝ))) ∘ iteratedFDeriv ℝ n f := by
    funext x
    simp [iteratedDeriv_eq_iteratedFDeriv]
  rw [h]
  exact (hf.iteratedFDeriv n).comp_left (by simp)

/-- Every derivative of a compactly supported `C^K` function is integrable. -/
theorem integrable_iteratedDeriv_of_hasCompactSupport {K : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ K f)
    (hsupp : HasCompactSupport f) {n : ℕ} (hn : n ≤ K) : Integrable (iteratedDeriv n f) :=
  (hf.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
    (HasCompactSupport.iteratedDeriv_of_hasCompactSupport hsupp n)

/-- The `L¹` norm of a function vanishing outside `[a, b]` and bounded by `M` there. -/
theorem integral_norm_le_of_forall_mem_Icc {g : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hint : Integrable g) (hzero : ∀ t, t ∉ Set.Icc a b → g t = 0)
    (hM : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ M) :
    ∫ t, ‖g t‖ ≤ (b - a) * M := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc a b)
    (fun t ht => by rw [hzero t ht, norm_zero])]
  calc ∫ t in Set.Icc a b, ‖g t‖ ≤ ∫ _ in Set.Icc a b, M :=
        setIntegral_mono_on hint.norm.integrableOn (integrableOn_const (by simp))
          measurableSet_Icc hM
    _ = (b - a) * M := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul]

end GaloisForLFunctions.HTGeometry
