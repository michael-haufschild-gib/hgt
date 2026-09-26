import GaloisForLFunctions.RHTower.ConstrainedWeilFourierMultiplier
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The bathtub floor of the pole-vanishing restricted Weil form

For a real smooth test `u` on `(-a, a)` with a vanishing polar moment, whose autocorrelation
vanishes at every prime-power lag `log n ≤ 2a`, the restricted Weil form is the archimedean
multiplier `M_S(η) = A(S) + Λ_S(η)` (`S = 2a`) integrated against the spectral density
`F(ξ) = ‖𝓕 u (ξ)‖²`.  Three elementary facts turn this into a lower bound:

* **Bathtub.**  If `M_S(2πξ) ≥ t − w(ξ)` with `w ≥ 0` bounded, then `Q(u) ≥ t ‖u‖² − ∫ F w`.
* **Pole-constrained Fourier bound.**  If both polar moments `∫ e^{±x/2} u` vanish, then for all
  real `α, β` the moments of `u` against `cosh(x/2)` and `sinh(x/2)` vanish, so Cauchy–Schwarz gives
  `F(ξ) ≤ ‖u‖² ∫_{-a}^{a} [(cos 2πξx − α cosh(x/2))² + (sin 2πξx − β sinh(x/2))²] dx`.
* **Bands.**  If `F ≤ G T_j` on the band `p_j ≤ c|ξ| ≤ q_j`, then the band weight
  `w = Σ_j w_j 1_{band j}` has `∫ F w ≤ G Σ_j w_j T_j · 2(q_j − p_j)/c`.

The two constraint directions suppress the low frequencies where `M_S` is negative; the bathtub
spends the remaining mass where `M_S` is largest.
-/

open MeasureTheory Set FourierTransform SchwartzMap Real

namespace RHTower

open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry

/-- The archimedean part `M_S(η) = A(S) + Λ_S(η)` of the constrained multiplier. -/
noncomputable def weilArchimedeanConstrainedMultiplier (S η : ℝ) : ℝ :=
  weilConstrainedConstant S + weilConstrainedMultiplierEnergy S η

/-- **Archimedean multiplier form.**  When the autocorrelation vanishes at every visible
prime-power lag, `Q(u) = ∫ F(ξ) M_S(2πξ) dξ`. -/
theorem suzukiRestrictedWeilForm_eq_integral_archimedeanMultiplier (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1)
    (hmom : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0 ∨ (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0)
    (hprime : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊,
      suzukiCoreAutocorrelation u (Real.log n) = 0) :
    suzukiRestrictedWeilForm A.1 u u =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        weilArchimedeanConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ) := by
  rw [suzukiRestrictedWeilForm_eq_constrainedKernelForm_of_moment_eq_zero A u hmom,
    weilPrimeBlock_suzukiRestrictedWeilIndices_eq_autocorrelation,
    integral_weilPositiveKernel_mul_defect_eq_fourier]
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊,
      criticalMellinAtomWeight n * suzukiCoreAutocorrelation u (Real.log n) = 0 :=
    Finset.sum_eq_zero (fun n hn => by rw [hprime n hn, mul_zero])
  have hF := integrable_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hΛ := integrable_spectralDensity_mul_multiplierEnergy A u
  have hg0 : suzukiCoreAutocorrelation u 0 =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) := by
    rw [suzukiCoreAutocorrelation_eq_integral_fourier_cos u 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hsum, hg0, ← integral_const_mul, ← integral_add (hF.const_mul _) hΛ]
  simp only [mul_zero, add_zero]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  unfold weilArchimedeanConstrainedMultiplier
  ring

/-- **The bathtub floor.**  A pointwise lower bound `M_S(2πξ) ≥ t − w(ξ)` with a nonnegative
bounded measurable deficit `w` gives `Q(u) ≥ t ‖u‖² − ∫ F w`. -/
theorem suzukiRestrictedWeilForm_ge_bathtub (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1)
    (hmom : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0 ∨ (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0)
    (hprime : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊,
      suzukiCoreAutocorrelation u (Real.log n) = 0)
    {t W : ℝ} {w : ℝ → ℝ} (hw0 : ∀ ξ, 0 ≤ w ξ) (hwm : Measurable w) (hwW : ∀ ξ, w ξ ≤ W)
    (hM : ∀ ξ, t - w ξ ≤ weilArchimedeanConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ)) :
    t * suzukiCoreAutocorrelation u 0 -
        ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) * w ξ ≤
      suzukiRestrictedWeilForm A.1 u u := by
  rw [suzukiRestrictedWeilForm_eq_integral_archimedeanMultiplier A u hmom hprime]
  have hF := integrable_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hΛ := integrable_spectralDensity_mul_multiplierEnergy A u
  have hFM : Integrable (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      weilArchimedeanConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ)) := by
    refine ((hF.const_mul (weilConstrainedConstant (2 * A.1))).add hΛ).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply]
    unfold weilArchimedeanConstrainedMultiplier
    ring
  have hFw : Integrable (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      w ξ) := by
    refine (hF.mul_const W).mono' (hF.aestronglyMeasurable.mul hwm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 ξ),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left (hwW ξ) (by positivity)
  have hg0 : suzukiCoreAutocorrelation u 0 =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) := by
    rw [suzukiCoreAutocorrelation_eq_integral_fourier_cos u 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hg0, ← integral_const_mul, ← integral_sub (hF.const_mul t) hFw]
  refine integral_mono ((hF.const_mul t).sub hFw) hFM (fun ξ => ?_)
  simp only
  have hnn : 0 ≤ ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (hM ξ) hnn]

/-! ## The pole-constrained pointwise Fourier bound -/

theorem fourier_suzukiRestrictedWeilCoreSchwartz_re {a : ℝ} (u : SuzukiRestrictedWeilCore a)
    (ξ : ℝ) :
    (𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ).re =
      ∫ x : ℝ, u x * Real.cos (2 * Real.pi * ξ * x) := by
  have hcont : Continuous fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * (u x : ℂ) := by
    have := u.continuous
    fun_prop
  have hint : Integrable (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * (u x : ℂ)) :=
    hcont.integrable_of_hasCompactSupport
      ((u.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left)
  rw [fourier_real_eq_integral_exp_smul]
  simp only [suzukiRestrictedWeilCoreSchwartz_apply, smul_eq_mul]
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show -2 * Real.pi * x * ξ = -(2 * Real.pi * ξ * x) by ring, Real.cos_neg]
  ring

theorem fourier_suzukiRestrictedWeilCoreSchwartz_im {a : ℝ} (u : SuzukiRestrictedWeilCore a)
    (ξ : ℝ) :
    (𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ).im =
      -∫ x : ℝ, u x * Real.sin (2 * Real.pi * ξ * x) := by
  have hcont : Continuous fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * (u x : ℂ) := by
    have := u.continuous
    fun_prop
  have hint : Integrable (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) * (u x : ℂ)) :=
    hcont.integrable_of_hasCompactSupport
      ((u.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left)
  rw [fourier_real_eq_integral_exp_smul]
  simp only [suzukiRestrictedWeilCoreSchwartz_apply, smul_eq_mul]
  have h := integral_im hint
  simp only [RCLike.im_to_complex] at h
  rw [← h, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  rw [show -2 * Real.pi * x * ξ = -(2 * Real.pi * ξ * x) by ring, Real.sin_neg]
  ring

/-- Integrals of a core against a continuous function live on the aperture interval. -/
theorem integral_core_mul_eq_intervalIntegral (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) (f : ℝ → ℝ) :
    (∫ x : ℝ, u x * f x) = ∫ x in (-A.1)..A.1, u x * f x := by
  rw [intervalIntegral.integral_of_le (by linarith [A.property])]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  have hu : u x = 0 := by
    by_contra hne
    have hmem := u.support_subset_aperture hne
    exact hx ⟨hmem.1, hmem.2.le⟩
  rw [hu, zero_mul]

/-- Cauchy–Schwarz on the aperture interval. -/
theorem sq_integral_core_mul_le (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x : ℝ, u x * f x) ^ (2 : ℕ) ≤
      suzukiCoreAutocorrelation u 0 * ∫ x in (-A.1)..A.1, f x ^ (2 : ℕ) := by
  have hle : -A.1 ≤ A.1 := by linarith [A.property]
  rw [integral_core_mul_eq_intervalIntegral, intervalIntegral.integral_of_le hle,
    ← integral_interval_sq_suzukiRestrictedWeilCore_eq_autocorrelation_zero A u,
    intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
  have hu2 : Integrable (fun x => u x ^ 2) (volume.restrict (Ioc (-A.1) A.1)) :=
    ((u.continuous.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict (Ioc (-A.1) A.1)) :=
    ((hf.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  exact sq_integral_mul_le u.continuous.aestronglyMeasurable hf.aestronglyMeasurable hu2 hf2

/-- **Pole-constrained pointwise Fourier bound.**  If both polar moments of `u` vanish, then for
all real `α, β`,
`‖𝓕u(ξ)‖² ≤ ‖u‖² ∫_{-a}^{a} [(cos 2πξx − α cosh(x/2))² + (sin 2πξx − β sinh(x/2))²] dx`. -/
theorem sq_norm_fourier_le_of_polarMoments (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1)
    (hp : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0) (hm : (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0)
    (α β ξ : ℝ) :
    ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) ≤
      suzukiCoreAutocorrelation u 0 *
        ∫ x in (-A.1)..A.1, ((Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2)) ^ (2 : ℕ) +
          (Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2)) ^ (2 : ℕ)) := by
  have hcu : Continuous fun x : ℝ => Real.exp (x / 2) * u x := by
    have := u.continuous; fun_prop
  have hcu' : Continuous fun x : ℝ => Real.exp (-(x / 2)) * u x := by
    have := u.continuous; fun_prop
  have hi1 : Integrable fun x : ℝ => Real.exp (x / 2) * u x :=
    hcu.integrable_of_hasCompactSupport u.hasCompactSupport.mul_left
  have hi2 : Integrable fun x : ℝ => Real.exp (-(x / 2)) * u x :=
    hcu'.integrable_of_hasCompactSupport u.hasCompactSupport.mul_left
  have hcosh : (∫ x : ℝ, u x * Real.cosh (x / 2)) = 0 := by
    have : (fun x : ℝ => u x * Real.cosh (x / 2)) =
        fun x => (Real.exp (x / 2) * u x + Real.exp (-(x / 2)) * u x) / 2 := by
      funext x; rw [Real.cosh_eq]; ring
    rw [this, integral_div, integral_add hi1 hi2, hp, hm]
    simp
  have hsinh : (∫ x : ℝ, u x * Real.sinh (x / 2)) = 0 := by
    have : (fun x : ℝ => u x * Real.sinh (x / 2)) =
        fun x => (Real.exp (x / 2) * u x - Real.exp (-(x / 2)) * u x) / 2 := by
      funext x; rw [Real.sinh_eq]; ring
    rw [this, integral_div, integral_sub hi1 hi2, hp, hm]
    simp
  have hcompact : ∀ g : ℝ → ℝ, Continuous g → Integrable fun x : ℝ => u x * g x := by
    intro g hg
    exact (u.continuous.mul hg).integrable_of_hasCompactSupport u.hasCompactSupport.mul_right
  have hre : (∫ x : ℝ, u x * Real.cos (2 * Real.pi * ξ * x)) =
      ∫ x : ℝ, u x * (Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2)) := by
    have h1 := hcompact (fun x => Real.cos (2 * Real.pi * ξ * x)) (by fun_prop)
    have h2 := hcompact (fun x => Real.cosh (x / 2)) (by fun_prop)
    have : (fun x : ℝ => u x * (Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2))) =
        fun x => u x * Real.cos (2 * Real.pi * ξ * x) - α * (u x * Real.cosh (x / 2)) := by
      funext x; ring
    rw [this, integral_sub h1 (h2.const_mul α), integral_const_mul, hcosh]
    ring
  have him : (∫ x : ℝ, u x * Real.sin (2 * Real.pi * ξ * x)) =
      ∫ x : ℝ, u x * (Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2)) := by
    have h1 := hcompact (fun x => Real.sin (2 * Real.pi * ξ * x)) (by fun_prop)
    have h2 := hcompact (fun x => Real.sinh (x / 2)) (by fun_prop)
    have : (fun x : ℝ => u x * (Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2))) =
        fun x => u x * Real.sin (2 * Real.pi * ξ * x) - β * (u x * Real.sinh (x / 2)) := by
      funext x; ring
    rw [this, integral_sub h1 (h2.const_mul β), integral_const_mul, hsinh]
    ring
  have hnorm : ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) =
      (𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ).re ^ 2 +
        (𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hnorm, fourier_suzukiRestrictedWeilCoreSchwartz_re, fourier_suzukiRestrictedWeilCoreSchwartz_im,
    neg_sq, hre, him]
  have hc1 := sq_integral_core_mul_le A u
    (f := fun x => Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2)) (by fun_prop)
  have hc2 := sq_integral_core_mul_le A u
    (f := fun x => Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2)) (by fun_prop)
  have hi1' : IntervalIntegrable (fun x : ℝ =>
      (Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2)) ^ (2 : ℕ)) volume (-A.1) A.1 :=
    (by fun_prop : Continuous fun x : ℝ =>
      (Real.cos (2 * Real.pi * ξ * x) - α * Real.cosh (x / 2)) ^ (2 : ℕ)).intervalIntegrable _ _
  have hi2' : IntervalIntegrable (fun x : ℝ =>
      (Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2)) ^ (2 : ℕ)) volume (-A.1) A.1 :=
    (by fun_prop : Continuous fun x : ℝ =>
      (Real.sin (2 * Real.pi * ξ * x) - β * Real.sinh (x / 2)) ^ (2 : ℕ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1' hi2', mul_add]
  exact add_le_add hc1 hc2

/-! ## Band integration -/

/-- The band `{ξ : p ≤ c|ξ| ≤ q}`. -/
def spectralBand (c p q : ℝ) : Set ℝ := {ξ | p ≤ c * |ξ| ∧ c * |ξ| ≤ q}

theorem measurableSet_spectralBand (c p q : ℝ) : MeasurableSet (spectralBand c p q) := by
  unfold spectralBand
  exact (measurableSet_le measurable_const (measurable_const.mul measurable_abs)).inter
    (measurableSet_le (measurable_const.mul measurable_abs) measurable_const)

theorem volume_spectralBand_le {c p q : ℝ} (hc : 0 < c) (hpq : p ≤ q) :
    volume (spectralBand c p q) ≤ ENNReal.ofReal (2 * (q - p) / c) := by
  have hsub : spectralBand c p q ⊆ Icc (p / c) (q / c) ∪ Icc (-(q / c)) (-(p / c)) := by
    intro ξ hξ
    obtain ⟨h1, h2⟩ := hξ
    rcases le_total 0 ξ with hξ0 | hξ0
    · left
      rw [abs_of_nonneg hξ0] at h1 h2
      exact ⟨by rw [div_le_iff₀ hc]; linarith, by rw [le_div_iff₀ hc]; linarith⟩
    · right
      rw [abs_of_nonpos hξ0] at h1 h2
      constructor
      · have : -ξ ≤ q / c := by rw [le_div_iff₀ hc]; linarith
        linarith
      · have : p / c ≤ -ξ := by rw [div_le_iff₀ hc]; linarith
        linarith
  calc volume (spectralBand c p q)
      ≤ volume (Icc (p / c) (q / c) ∪ Icc (-(q / c)) (-(p / c))) := measure_mono hsub
    _ ≤ volume (Icc (p / c) (q / c)) + volume (Icc (-(q / c)) (-(p / c))) := measure_union_le _ _
    _ = ENNReal.ofReal (q / c - p / c) + ENNReal.ofReal (-(p / c) - -(q / c)) := by
        rw [Real.volume_Icc, Real.volume_Icc]
    _ = ENNReal.ofReal (2 * (q - p) / c) := by
        rw [← ENNReal.ofReal_add (by rw [sub_nonneg]; gcongr)
          (by rw [sub_nonneg, neg_le_neg_iff]; gcongr)]
        congr 1
        field_simp
        ring

/-- The band deficit `w(ξ) = Σ_j w_j 1_{p_j ≤ c|ξ| ≤ q_j}`. -/
noncomputable def bandDeficit {n : ℕ} (c : ℝ) (p q wt : Fin n → ℝ) (ξ : ℝ) : ℝ :=
  ∑ j, wt j * (spectralBand c (p j) (q j)).indicator (fun _ => (1 : ℝ)) ξ

theorem bandDeficit_nonneg {n : ℕ} (c : ℝ) (p q wt : Fin n → ℝ) (hwt : ∀ j, 0 ≤ wt j) (ξ : ℝ) :
    0 ≤ bandDeficit c p q wt ξ := by
  unfold bandDeficit
  refine Finset.sum_nonneg (fun j _ => mul_nonneg (hwt j) ?_)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) ξ

theorem bandDeficit_le {n : ℕ} (c : ℝ) (p q wt : Fin n → ℝ) (hwt : ∀ j, 0 ≤ wt j) (ξ : ℝ) :
    bandDeficit c p q wt ξ ≤ ∑ j, wt j := by
  unfold bandDeficit
  refine Finset.sum_le_sum (fun j _ => ?_)
  calc wt j * (spectralBand c (p j) (q j)).indicator (fun _ => (1 : ℝ)) ξ ≤ wt j * 1 := by
        gcongr
        · exact hwt j
        · exact Set.indicator_le_self' (fun _ _ => zero_le_one) ξ |>.trans (le_refl _)
    _ = wt j := mul_one _

theorem measurable_bandDeficit {n : ℕ} (c : ℝ) (p q wt : Fin n → ℝ) :
    Measurable (bandDeficit c p q wt) := by
  unfold bandDeficit
  refine Finset.measurable_sum _ (fun j _ => measurable_const.mul ?_)
  exact measurable_const.indicator (measurableSet_spectralBand c (p j) (q j))

theorem mem_spectralBand_bandDeficit_ge {n : ℕ} {c : ℝ} {p q wt : Fin n → ℝ}
    (hwt : ∀ j, 0 ≤ wt j) {j : Fin n} {ξ : ℝ} (hξ : ξ ∈ spectralBand c (p j) (q j)) :
    wt j ≤ bandDeficit c p q wt ξ := by
  unfold bandDeficit
  have hterm : wt j = wt j * (spectralBand c (p j) (q j)).indicator (fun _ => (1 : ℝ)) ξ := by
    rw [Set.indicator_of_mem hξ, mul_one]
  rw [hterm]
  exact Finset.single_le_sum (f := fun i => wt i *
    (spectralBand c (p i) (q i)).indicator (fun _ => (1 : ℝ)) ξ)
    (fun i _ => mul_nonneg (hwt i) (Set.indicator_nonneg (fun _ _ => zero_le_one) ξ))
    (Finset.mem_univ j)

/-- **Band integration.**  A bandwise bound `F ≤ G T_j` integrates to
`∫ F w ≤ G Σ_j w_j T_j · 2(q_j − p_j)/c`. -/
theorem integral_mul_bandDeficit_le {n : ℕ} {F : ℝ → ℝ} (hF : Integrable F)
    {c G : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (p q wt T : Fin n → ℝ)
    (hpq : ∀ j, p j ≤ q j) (hwt : ∀ j, 0 ≤ wt j) (hT : ∀ j, 0 ≤ T j)
    (hband : ∀ j, ∀ ξ ∈ spectralBand c (p j) (q j), F ξ ≤ G * T j) :
    (∫ ξ : ℝ, F ξ * bandDeficit c p q wt ξ) ≤
      G * ∑ j, wt j * T j * (2 * (q j - p j) / c) := by
  have hsplit : (fun ξ => F ξ * bandDeficit c p q wt ξ) = fun ξ => ∑ j, wt j *
      (spectralBand c (p j) (q j)).indicator F ξ := by
    funext ξ
    unfold bandDeficit
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hξ : ξ ∈ spectralBand c (p j) (q j)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]; ring
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]; ring
  have hint : ∀ j : Fin n, Integrable ((spectralBand c (p j) (q j)).indicator F) :=
    fun j => hF.indicator (measurableSet_spectralBand c (p j) (q j))
  rw [hsplit, integral_finsetSum _ (fun j _ => (hint j).const_mul _), Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [integral_const_mul, integral_indicator (measurableSet_spectralBand c (p j) (q j))]
  have hvol := volume_spectralBand_le hc (hpq j)
  have hfin : volume (spectralBand c (p j) (q j)) < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have hbound : (∫ ξ in spectralBand c (p j) (q j), F ξ) ≤
      G * T j * (2 * (q j - p j) / c) := by
    calc (∫ ξ in spectralBand c (p j) (q j), F ξ)
        ≤ ∫ ξ in spectralBand c (p j) (q j), G * T j := by
          refine setIntegral_mono_on hF.integrableOn (integrableOn_const hfin.ne)
            (measurableSet_spectralBand c (p j) (q j)) (fun ξ hξ => hband j ξ hξ)
      _ = (volume (spectralBand c (p j) (q j))).toReal * (G * T j) := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def]
      _ ≤ (2 * (q j - p j) / c) * (G * T j) := by
          gcongr
          · exact mul_nonneg hG (hT j)
          · rw [← ENNReal.ofReal_toReal hfin.ne] at hvol
            have h2 : 0 ≤ 2 * (q j - p j) / c := div_nonneg (by linarith [hpq j]) hc.le
            exact (ENNReal.ofReal_le_ofReal_iff h2).1 hvol
      _ = G * T j * (2 * (q j - p j) / c) := by ring
  calc wt j * ∫ ξ in spectralBand c (p j) (q j), F ξ
      ≤ wt j * (G * T j * (2 * (q j - p j) / c)) := mul_le_mul_of_nonneg_left hbound (hwt j)
    _ = G * (wt j * T j * (2 * (q j - p j) / c)) := by ring

end RHTower
