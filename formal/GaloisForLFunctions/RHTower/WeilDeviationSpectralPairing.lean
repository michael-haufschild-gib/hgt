import GaloisForLFunctions.RHTower.RiemannAutocorrFourier

/-!
# The spectral pairing of a Weil-positive deviation

Let `lam` be full-cone Weil-positive with summable excess, `a(n) = (lam(n) − Λ(n))/√n`, and
`ψ = K⋆W_a` the Riemann-kernel potential of the deviation measure
`W_a = Σ_n a(n)(δ_{log n} + δ_{−log n})`. By Bochner, `−ψ = charFun σ` for a finite positive
measure `σ`.

**Theorem** (`deviationPairing_fourier_riemannXi_sq_mul`). For every continuous integrable `g`
with integrable transform,

`Σ_n a(n) (𝓕(Ξ²g)(log n) + 𝓕(Ξ²g)(−log n)) = −∫ g(t/2π) dσ(t)`.

**Proof.**
- `𝓕(Ξ²g)(u) = ∫ K(v − u) 𝓕g(v) dv`, by `Ξ² = 𝓕K` and Fubini.
- Pairing with `W_a` gives `∫ ψ 𝓕g`. The interchange of `Σ_n` and `∫` is justified by the
  translation bound on the deficit (kernel domination) and the summable excess.
- `∫ ψ 𝓕g = −∫∫ e^{ivt} 𝓕g(v) dv dσ(t) = −∫ g(t/2π) dσ(t)`, by Fourier inversion.

In particular the deviation pairs nonpositively with `𝓕(Ξ²g)` for every nonnegative `g`. This is
near-null Weil positivity in spectral form.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate

namespace RHTower.WeilExcess

noncomputable section

theorem continuous_fourier_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (u : ℝ) : ‖𝓕 f u‖ ≤ ∫ ξ, ‖f ξ‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem fourierInv_eq_integral (h : ℝ → ℂ) (w : ℝ) :
    𝓕⁻ h w = ∫ v, Complex.exp ((2 * π * v * w : ℝ) * I) * h v := by
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast; ring

/-- **`𝓕(Ξ²g)(u) = ∫ K(v − u) 𝓕g(v) dv`.** -/
theorem fourier_riemannXi_sq_mul {g : ℝ → ℂ} (hg : Integrable g) (u : ℝ) :
    𝓕 (fun ξ => riemannXi ξ ^ 2 * g ξ) u =
      ∫ v, ((riemannAutocorr (v - u) : ℝ) : ℂ) * 𝓕 g v := by
  have hK : Integrable fun y => ((riemannAutocorr y : ℝ) : ℂ) := by
    have : Integrable riemannAutocorr := by
      obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
      refine Integrable.mono' ((integrable_exp_neg_abs.comp_mul_left' (two_ne_zero)).const_mul C₁)
        continuous_riemannAutocorr.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg y)]
      refine (hC₁ y).trans (le_of_eq ?_)
      simp only [abs_mul, abs_two, mul_comm]
    exact this.ofReal
  set F : ℝ → ℝ → ℂ := fun ξ y => Complex.exp (-(2 * π * ξ * (y + u) : ℝ) * I) *
    (((riemannAutocorr y : ℝ) : ℂ) * g ξ) with hF
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * ((riemannAutocorr p.2 : ℝ) : ℂ))
        (volume.prod volume) := hg.mul_prod hK
    refine hprod.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (Continuous.aestronglyMeasurable (by fun_prop))
      · exact AEStronglyMeasurable.mul (hK.aestronglyMeasurable.comp_snd) hg.aestronglyMeasurable.comp_fst
    · simp only [Function.uncurry, hF, norm_mul]
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, mul_comm]
  have hstep1 : 𝓕 (fun ξ => riemannXi ξ ^ 2 * g ξ) u = ∫ ξ, ∫ y, F ξ y := by
    rw [fourier_eq_integral]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [← fourier_riemannAutocorr, fourier_eq_integral, ← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF]
    rw [show -(((2 * π * ξ * (y + u) : ℝ) : ℂ)) * I =
      -((2 * π * ξ * u : ℝ) : ℂ) * I + -((2 * π * y * ξ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add]
    ring
  have hstep2 : (∫ ξ, ∫ y, F ξ y) = ∫ y, ((riemannAutocorr y : ℝ) : ℂ) * 𝓕 g (y + u) := by
    rw [integral_integral_swap hFint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [fourier_eq_integral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF]; ring
  rw [hstep1, hstep2]
  rw [← integral_sub_right_eq_self (μ := volume)
    (fun y => ((riemannAutocorr y : ℝ) : ℂ) * 𝓕 g (y + u)) u]
  simp only [sub_add_cancel]

/-! ## The pairing -/

/-- The pairing of the normalized deviation with a test function on the `u`-line. -/
def deviationPairing (lam : ℕ → ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (weilDeviation lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n))

/-- **The deviation paired with `𝓕(Ξ²g)` is `∫ ψ 𝓕g`.** -/
theorem deviationPairing_fourier_riemannXi_sq_mul_eq_integral {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ)
    {g : ℝ → ℂ} (hg : Integrable g) (hFg : Integrable (𝓕 g)) :
    deviationPairing lam (𝓕 fun ξ => riemannXi ξ ^ 2 * g ξ) =
      ∫ v, (deviationPotential lam v : ℂ) * 𝓕 g v := by
  obtain ⟨Bₑ, hBe⟩ := kernelPotential_le_of_cauchyBounded (deviationExcess_nonneg lam) hexc
  obtain ⟨B, hB0, hB⟩ := exists_kernelPotential_deficit_le hW hBe
  set P : ℝ → ℝ := fun v => ‖𝓕 g v‖ with hP
  have hPc : Continuous P := (continuous_fourier_integrable hg).norm
  have hPi : Integrable P := hFg.norm
  have hP0 : ∀ v, 0 ≤ P v := fun v => norm_nonneg _
  set F : ℕ → ℝ → ℂ := fun n v => (weilDeviation lam n : ℂ) *
    (((riemannAutocorr (v - Real.log n) + riemannAutocorr (v + Real.log n) : ℝ) : ℂ) * 𝓕 g v)
    with hF
  have hKc : ∀ c : ℝ, Continuous fun v => riemannAutocorr (v - c) :=
    fun c => continuous_riemannAutocorr.comp (continuous_id.sub continuous_const)
  have hKi : ∀ c : ℝ, Integrable fun v => ((riemannAutocorr (v - c) : ℝ) : ℂ) * 𝓕 g v := by
    intro c
    refine (hFg.norm.const_mul (riemannAutocorr 0)).mono'
      (((Complex.continuous_ofReal.comp (hKc c)).mul
        (continuous_fourier_integrable hg)).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg _)]
    exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (norm_nonneg _)
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    have h := ((hKi (Real.log n)).add (hKi (-Real.log n))).const_mul (weilDeviation lam n : ℂ)
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [hF, Pi.add_apply, sub_neg_eq_add]; push_cast; ring
  have hterm : ∀ n : ℕ, (weilDeviation lam n : ℂ) *
      (𝓕 (fun ξ => riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ => riemannXi ξ ^ 2 * g ξ) (-Real.log n)) = ∫ v, F n v := by
    intro n
    rw [fourier_riemannXi_sq_mul hg, fourier_riemannXi_sq_mul hg,
      ← integral_add (hKi _) (hKi _), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, sub_neg_eq_add]; push_cast; ring
  -- the norms of the terms
  have hnorm : ∀ n, ∫ v, ‖F n v‖ =
      |weilDeviation lam n| * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n)) := by
    intro n
    have hk1 := integrable_riemannAutocorr_mul hPc hPi (Real.log n)
    have hk2 := integrable_riemannAutocorr_mul hPc hPi (-Real.log n)
    unfold kernelSmooth
    rw [← integral_add hk1 hk2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, hP, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _)),
      show Real.log n - v = -(v - Real.log n) by ring, riemannAutocorr_neg,
      show -Real.log n - v = -(v + Real.log n) by ring, riemannAutocorr_neg]
    ring
  have hks0 : ∀ u, 0 ≤ kernelSmooth P u := fun u =>
    integral_nonneg fun y => mul_nonneg (riemannAutocorr_nonneg _) (hP0 y)
  obtain ⟨hvs, -⟩ := tsum_mul_kernelSmooth_le (deviationDeficit_nonneg lam)
    (summable_deficit_term hW) hB hP0 hPc hPi
  obtain ⟨hes, -⟩ := tsum_mul_kernelSmooth_le (deviationExcess_nonneg lam)
    (summable_excess_term hW) hBe hP0 hPc hPi
  have hsumnorm : Summable fun n => ∫ v, ‖F n v‖ := by
    simp only [hnorm]
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _)
      (add_nonneg (hks0 _) (hks0 _))) (fun n => ?_)
      (hes.add hvs)
    have ha : |weilDeviation lam n| ≤ deviationExcess lam n + deviationDeficit lam n := by
      rw [weilDeviation_eq_sub]
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (deviationExcess_nonneg lam n),
          abs_of_nonneg (deviationDeficit_nonneg lam n)])
    have hs := add_nonneg (hks0 (Real.log n)) (hks0 (-Real.log n))
    calc |weilDeviation lam n| * (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n))
        ≤ (deviationExcess lam n + deviationDeficit lam n) *
            (kernelSmooth P (Real.log n) + kernelSmooth P (-Real.log n)) :=
          mul_le_mul_of_nonneg_right ha hs
      _ = _ := by ring
  unfold deviationPairing
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsumnorm]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hF]
  have hs := summable_deviationPotential_term hW v
  unfold deviationPotential
  rw [Complex.ofReal_tsum, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [add_comm (riemannAutocorr (v - Real.log n))]
  push_cast; ring

/-- `∫ ψ 𝓕g = −∫ g(t/2π) dσ(t)` when `−ψ = charFun σ`. -/
theorem integral_deviationPotential_mul_fourier {lam : ℕ → ℝ} (σ : Measure ℝ)
    [IsFiniteMeasure σ] (hσ : ∀ t, charFun σ t = ((-deviationPotential lam t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) (hFg : Integrable (𝓕 g)) :
    ∫ v, (deviationPotential lam v : ℂ) * 𝓕 g v = -∫ t, g (t / (2 * π)) ∂σ := by
  have hψ : ∀ v, (deviationPotential lam v : ℂ) = -∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) ∂σ := by
    intro v
    rw [← charFun_apply_real, hσ]; push_cast; ring
  have hint : Integrable (Function.uncurry fun (v t : ℝ) => Complex.exp ((v : ℂ) * t * I) * 𝓕 g v)
      (volume.prod σ) := by
    have h1 : Integrable (fun p : ℝ × ℝ => 𝓕 g p.1 * (1 : ℂ)) (volume.prod σ) :=
      hFg.mul_prod (integrable_const (1 : ℂ))
    refine h1.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (continuous_fourier_integrable hg).aestronglyMeasurable.comp_fst)
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, norm_mul, mul_one]
    rw [show (p.1 : ℂ) * p.2 * I = ((p.1 * p.2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv : ∀ t : ℝ, ∫ v : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v = g (t / (2 * π)) := by
    intro t
    have h := hg.fourierInv_fourier_eq hFg (v := t / (2 * π)) hgc.continuousAt
    rw [fourierInv_eq_integral] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    push_cast; field_simp
  calc ∫ v, (deviationPotential lam v : ℂ) * 𝓕 g v
      = ∫ v : ℝ, -(∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v ∂σ) := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hψ, integral_mul_const]; ring
    _ = -∫ v : ℝ, (∫ t : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v ∂σ) := integral_neg _
    _ = -∫ t : ℝ, (∫ v : ℝ, Complex.exp ((v : ℂ) * t * I) * 𝓕 g v) ∂σ := by
        rw [integral_integral_swap hint]
    _ = -∫ t, g (t / (2 * π)) ∂σ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall hinv)

/-- **Near-null positivity in spectral form.** -/
theorem deviationPairing_fourier_riemannXi_sq_mul {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : ∀ t, charFun σ t = ((-deviationPotential lam t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) (hFg : Integrable (𝓕 g)) :
    deviationPairing lam (𝓕 fun ξ => riemannXi ξ ^ 2 * g ξ) = -∫ t, g (t / (2 * π)) ∂σ := by
  rw [deviationPairing_fourier_riemannXi_sq_mul_eq_integral hW hexc hg hFg,
    integral_deviationPotential_mul_fourier σ hσ hgc hg hFg]

/-- The Bochner measure of the negative potential. -/
theorem exists_spectralMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ σ : Measure ℝ, IsFiniteMeasure σ ∧
      ∀ t, charFun σ t = ((-deviationPotential lam t : ℝ) : ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_neg_deviationPotential hW)
    (Complex.continuous_ofReal.comp (continuous_deviationPotential hW).neg)

end

end RHTower.WeilExcess
