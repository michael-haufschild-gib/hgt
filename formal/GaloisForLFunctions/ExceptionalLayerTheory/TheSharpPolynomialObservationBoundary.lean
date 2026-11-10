import GaloisForLFunctions.ExceptionalLayerTheory.PolynomialDampingReadsTheDivisor
import GaloisForLFunctions.SelbergClass.DegreeOne.VerticalStirling

/-!
# The sharp polynomial observation boundary

Exact vertical Stirling asymptotics cancel against boundary rotation.
The surviving amplitude depends only on horizontal depth. Polynomial
contraction therefore has a sharp growth, finite-limit and decay boundary.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory


/-- The boundary-mode calibration is independent of the zero ordinate. -/
def boundaryModeAmplitude (x : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (2 * Real.pi) * (1 / 2 : ℝ) ^ (x / 2 - 1 / 2) * Real.exp (-(1 / 2))

theorem boundaryModeAmplitude_pos (x : ℝ) : 0 < boundaryModeAmplitude x := by
  unfold boundaryModeAmplitude
  positivity

/-- The exact power spent by radius, height and spacing. -/
def polynomialObservationExponent (d : ℕ) (κ x A : ℝ) : ℝ :=
  (A + 1) * x / 2 - 1 / 2 - (d : ℝ) * κ

private theorem norm_stirlingShape {τ : ℝ} (hτ : 0 < τ) (a : ℝ) :
    ‖SelbergClass.DegreeOne.stirlingShape a τ‖ =
      τ ^ (a - 1 / 2) * Real.exp (-(Real.pi * τ / 2)) := by
  rw [SelbergClass.DegreeOne.stirlingShape, norm_mul, Complex.norm_exp]
  have he : (I * (((Real.pi * (a - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ))).re = 0 := by
    simp
  rw [he, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _))]

private theorem tendsto_Gamma_modulus_stirling (a : ℝ) :
    Tendsto (fun τ : ℝ => ‖Complex.Gamma ((a : ℂ) + τ * I)‖ /
      (τ ^ (a - 1 / 2) * Real.exp (-(Real.pi * τ / 2)))) atTop
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have hn := (SelbergClass.DegreeOne.tendsto_Gamma_div_stirlingShape a).norm
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  apply hn.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [norm_div, norm_stirlingShape hτ]

private theorem normalized_boundary_kernel_line (x γ : ℝ) {t y : ℝ}
    (ht : 0 < t) (hγ : γ < t) (hy : 0 < y) :
    let τ := (t - γ) / 2
    ‖rotatedGaussianKernel y (boundaryDampingAngle t) ((x : ℂ) + (γ - t : ℝ) * I)‖ /
        (y ^ (-(x / 2)) * t ^ (x / 2 - 1 / 2)) =
      (1 / 2) * (‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + τ * I)‖ /
        (τ ^ (x / 2 - 1 / 2) * Real.exp (-(Real.pi * τ / 2)))) *
          (τ / t) ^ (x / 2 - 1 / 2) * Real.exp (-(τ / t)) := by
  let τ := (t - γ) / 2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  dsimp only
  change _ = (1 / 2) * (‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + τ * I)‖ /
    (τ ^ (x / 2 - 1 / 2) * Real.exp (-(Real.pi * τ / 2)))) *
      (τ / t) ^ (x / 2 - 1 / 2) * Real.exp (-(τ / t))
  rw [norm_rotatedGaussianKernel, norm_gaussianMBKernel_line hy]
  have him : ((x : ℂ) + (γ - t : ℝ) * I).im = γ - t := by simp
  have hconj : ((x / 2 : ℝ) : ℂ) + ((γ - t) / 2 : ℝ) * I =
      (starRingEnd ℂ) (((x / 2 : ℝ) : ℂ) + τ * I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    dsimp only [τ]
    push_cast
    ring
  rw [him, hconj, Complex.Gamma_conj, Complex.norm_conj]
  have hphase : boundaryDampingAngle t * (γ - t) / 2 = Real.pi * τ / 2 - τ / t := by
    dsimp only [boundaryDampingAngle, τ]
    field_simp [ht.ne']
    ring
  rw [hphase, Real.div_rpow hτ.le ht.le]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp [(Real.rpow_pos_of_pos hy (-(x / 2))).ne',
    (Real.rpow_pos_of_pos ht (x / 2 - 1 / 2)).ne',
    (Real.rpow_pos_of_pos hτ (x / 2 - 1 / 2)).ne', Real.exp_ne_zero]

/-- The exact boundary-mode modulus is uniform over every positive radius
schedule, with no restriction on its rate of change or contraction. -/
theorem tendsto_boundary_mode_normalized_modulus (ρ : ℂ) (σ : ℝ)
    {y : ℝ → ℝ} (hy : ∀ᶠ t : ℝ in atTop, 0 < y t) :
    Tendsto (fun t : ℝ =>
      ‖rotatedGaussianKernel (y t) (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I))‖ /
        ((y t) ^ (-((ρ.re - σ) / 2)) * t ^ ((ρ.re - σ) / 2 - 1 / 2)))
      atTop (𝓝 (boundaryModeAmplitude (ρ.re - σ))) := by
  let x := ρ.re - σ
  let τ : ℝ → ℝ := fun t => (t - ρ.im) / 2
  have hτ : Tendsto τ atTop atTop := by
    have hh := tendsto_atTop_add_const_right atTop (-ρ.im / 2)
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
    convert hh using 1
    funext t
    dsimp only [τ, id]
    ring
  have hr : Tendsto (fun t : ℝ => τ t / t) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hd : Tendsto (fun t : ℝ => ρ.im / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hh : Tendsto (fun t : ℝ => (1 - ρ.im / t) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      (tendsto_const_nhds.sub hd).div_const 2
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [τ]
    field_simp [ht.ne']
  have hp : Tendsto (fun t : ℝ => (τ t / t) ^ (x / 2 - 1 / 2)) atTop
      (𝓝 ((1 / 2 : ℝ) ^ (x / 2 - 1 / 2))) :=
    (continuousAt_id.rpow_const (p := x / 2 - 1 / 2)
      (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hr
  have he : Tendsto (fun t : ℝ => Real.exp (-(τ t / t))) atTop (𝓝 (Real.exp (-(1 / 2)))) := by
    simpa only [Function.comp_def] using (Real.continuous_exp.tendsto (-(1 / 2))).comp hr.neg
  have hm := ((((tendsto_Gamma_modulus_stirling (x / 2)).comp hτ).const_mul (1 / 2)).mul hp).mul he
  change Tendsto _ atTop (𝓝 (boundaryModeAmplitude x)) at hm
  apply hm.congr'
  filter_upwards [hy, eventually_gt_atTop (0 : ℝ), eventually_gt_atTop ρ.im] with t hyt ht hγ
  have hz : ρ - ((σ : ℂ) + t * I) = ((ρ.re - σ : ℝ) : ℂ) + (ρ.im - t : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [hz]
  exact (normalized_boundary_kernel_line x ρ.im ht hγ hyt).symm


/-- The selected mode after polynomial spacing contraction. -/
def polynomialContractedMode (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A t : ℝ) : ℂ :=
  ((t ^ (-κ) : ℝ) : ℂ) ^ d * rotatedGaussianKernel (t ^ (-A))
    (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I))

/-- Exact polynomial modulus law, with an ordinate-independent positive
constant and no sign restriction on the radius or contraction exponents. -/
theorem tendsto_polynomial_mode_modulus (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A : ℝ) :
    Tendsto (fun t : ℝ => ‖polynomialContractedMode d κ ρ σ A t‖ /
      t ^ polynomialObservationExponent d κ (ρ.re - σ) A) atTop
      (𝓝 (boundaryModeAmplitude (ρ.re - σ))) := by
  have hh := tendsto_boundary_mode_normalized_modulus ρ σ (y := fun t => t ^ (-A))
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        exact Real.rpow_pos_of_pos ht _)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have he : (t ^ (-κ)) ^ d *
      ((t ^ (-A)) ^ (-((ρ.re - σ) / 2)) * t ^ ((ρ.re - σ) / 2 - 1 / 2)) =
      t ^ polynomialObservationExponent d κ (ρ.re - σ) A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
      ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    dsimp only [polynomialObservationExponent]
    ring
  rw [polynomialContractedMode, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _), ← he]
  have hp := (pow_pos (Real.rpow_pos_of_pos ht (-κ)) d).ne'
  have hb := (mul_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos ht (-A)) (-((ρ.re - σ) / 2)))
    (Real.rpow_pos_of_pos ht ((ρ.re - σ) / 2 - 1 / 2))).ne'
  field_simp [hp, hb]

private theorem tendsto_zero_of_power_quotient {f : ℝ → ℝ} {r C : ℝ}
    (hf : Tendsto (fun t : ℝ => f t / t ^ r) atTop (𝓝 C)) (hr : r < 0) :
    Tendsto f atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg] using _root_.tendsto_rpow_neg_atTop (neg_pos.mpr hr)
  have hm := hf.mul hp
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht r).ne'

private theorem tendsto_atTop_of_power_quotient {f : ℝ → ℝ} {r C : ℝ}
    (hf : Tendsto (fun t : ℝ => f t / t ^ r) atTop (𝓝 C)) (hC : 0 < C) (hr : 0 < r) :
    Tendsto f atTop atTop := by
  have hp := Filter.Tendsto.const_mul_atTop (by positivity : 0 < C / 2)
    (_root_.tendsto_rpow_atTop hr)
  apply tendsto_atTop_mono' atTop _ hp
  filter_upwards [hf.eventually (lt_mem_nhds (by linarith only [hC] : C / 2 < C)),
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ht0 r)).mp ht.le

/-- Negative polynomial exponent gives decay of the contracted mode. -/
theorem tendsto_polynomial_mode_zero (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A : ℝ)
    (hr : polynomialObservationExponent d κ (ρ.re - σ) A < 0) :
    Tendsto (fun t : ℝ => ‖polynomialContractedMode d κ ρ σ A t‖) atTop (𝓝 0) :=
  tendsto_zero_of_power_quotient (tendsto_polynomial_mode_modulus d κ ρ σ A) hr

/-- Positive polynomial exponent gives growth of the contracted mode. -/
theorem tendsto_polynomial_mode_atTop (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A : ℝ)
    (hr : 0 < polynomialObservationExponent d κ (ρ.re - σ) A) :
    Tendsto (fun t : ℝ => ‖polynomialContractedMode d κ ρ σ A t‖) atTop atTop :=
  tendsto_atTop_of_power_quotient (tendsto_polynomial_mode_modulus d κ ρ σ A)
    (boundaryModeAmplitude_pos _) hr

/-- The critical exponent has a positive finite limiting modulus. -/
theorem tendsto_polynomial_mode_critical (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A : ℝ)
    (hr : polynomialObservationExponent d κ (ρ.re - σ) A = 0) :
    Tendsto (fun t : ℝ => ‖polynomialContractedMode d κ ρ σ A t‖) atTop
      (𝓝 (boundaryModeAmplitude (ρ.re - σ))) := by
  simpa only [hr, Real.rpow_zero, div_one] using tendsto_polynomial_mode_modulus d κ ρ σ A

/-- The growth threshold is necessary as well as sufficient. -/
theorem polynomial_mode_growth_iff (d : ℕ) (κ : ℝ) (ρ : ℂ) (σ A : ℝ) :
    Tendsto (fun t : ℝ => ‖polynomialContractedMode d κ ρ σ A t‖) atTop atTop ↔
      0 < polynomialObservationExponent d κ (ρ.re - σ) A := by
  constructor
  · intro hg
    by_contra hh
    rcases lt_or_eq_of_le (le_of_not_gt hh) with hl | he
    · exact (not_tendsto_atTop_of_tendsto_nhds (tendsto_polynomial_mode_zero d κ ρ σ A hl)) hg
    · exact (not_tendsto_atTop_of_tendsto_nhds (tendsto_polynomial_mode_critical d κ ρ σ A he)) hg
  · exact tendsto_polynomial_mode_atTop d κ ρ σ A

/-- No bounded spacing can make a selected mode grow while radius is at
least reciprocal height and horizontal depth is below one half. -/
theorem boundary_mode_zero_of_short_damping_scale (d : ℕ) (ρ : ℂ) (σ : ℝ)
    (hρσ : σ < ρ.re) (hdepth : ρ.re - σ < 1 / 2) {h y : ℝ → ℝ}
    (hscale : ∀ᶠ t : ℝ in atTop, 0 ≤ h t ∧ h t ≤ 1 ∧ t⁻¹ ≤ y t) :
    Tendsto (fun t : ℝ => ((h t : ℝ) : ℂ) ^ d *
      rotatedGaussianKernel (y t) (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I)))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ =>
      ‖rotatedGaussianKernel (t ^ (-(1 : ℝ))) (boundaryDampingAngle t)
        (ρ - ((σ : ℂ) + t * I))‖) atTop (𝓝 0) := by
    have hr : polynomialObservationExponent 0 0 (ρ.re - σ) 1 < 0 := by
      dsimp only [polynomialObservationExponent]
      norm_num
      linarith only [hdepth]
    simpa only [polynomialContractedMode, pow_zero, one_mul] using
      tendsto_polynomial_mode_zero 0 0 ρ σ 1 hr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbase
  filter_upwards [hscale, eventually_gt_atTop (0 : ℝ)] with t hh ht
  have hy : 0 < y t := (inv_pos.mpr ht).trans_le hh.2.2
  have hpow : ‖((h t : ℝ) : ℂ) ^ d‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh.1]
    simpa only [one_pow] using pow_le_pow_left₀ hh.1 hh.2.1 d
  have hp : (y t) ^ (-((ρ.re - σ) / 2)) ≤ (t⁻¹) ^ (-((ρ.re - σ) / 2)) := by
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos (inv_pos.mpr ht)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right (Real.log_le_log (inv_pos.mpr ht) hh.2.2)
      (by linarith only [hρσ])
  have hz : ρ - ((σ : ℂ) + t * I) = ((ρ.re - σ : ℝ) : ℂ) + (ρ.im - t : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖rotatedGaussianKernel (y t) (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I))‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul, Real.rpow_neg ht.le, Real.rpow_one, hz,
        norm_rotatedGaussianKernel, norm_rotatedGaussianKernel,
        norm_gaussianMBKernel_line hy, norm_gaussianMBKernel_line (inv_pos.mpr ht)]
      gcongr


/-- Above the divisor-recovery threshold, the literal prime filter has the
same exact polynomial exponent, multiplied by the full divisor amplitude. -/
theorem exists_sharp_polynomial_prime_modulus_threshold
    (F : Finset XiZeroCopy) {θ σ β : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ κ : ℝ, 0 < κ →
      Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
        (divisorDampingFilter F ρ β (t ^ (-κ))) σ β (polynomialDampingSpeed A t)
          (t ^ (-κ)) (boundaryDampingAngle t) t‖ /
        t ^ polynomialObservationExponent (1 + (F.filter (fun q => xiZero q ≠ ρ)).card)
          κ (ρ.re - σ) A) atTop
        (𝓝 (‖-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))‖ *
            boundaryModeAmplitude (ρ.re - σ))) := by
  classical
  obtain ⟨A₀, hA₀, hread⟩ := exists_polynomial_prime_filter_divisor_threshold
    F hσ hgap hrest ρ hρσ hρ1 hρ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA κ hκ
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < t ^ (-κ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact Real.rpow_pos_of_pos ht _
  have hr := hread A hA (fun t => t ^ (-κ)) (_root_.tendsto_rpow_neg_atTop hκ) hpos
  have hm := hr.norm.mul (tendsto_polynomial_mode_modulus d κ ρ σ A)
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hg : polynomialContractedMode d κ ρ σ A t ≠ 0 :=
    mul_ne_zero (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht (-κ)).ne'))
      (rotatedGaussianKernel_ne_zero (Real.rpow_pos_of_pos ht (-A)) _
        (by simpa using sub_pos.mpr hρσ))
  change ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (t ^ (-κ)))
    σ β (polynomialDampingSpeed A t) (t ^ (-κ)) (boundaryDampingAngle t) t /
      polynomialContractedMode d κ ρ σ A t‖ *
      (‖polynomialContractedMode d κ ρ σ A t‖ /
        t ^ polynomialObservationExponent d κ (ρ.re - σ) A) = _
  rw [norm_div]
  field_simp [(norm_pos_iff.mpr hg).ne',
    (Real.rpow_pos_of_pos ht (polynomialObservationExponent d κ (ρ.re - σ) A)).ne']
  rfl

/-- The complete prime filter has growth, decay and a positive finite
critical modulus according to the exact polynomial exponent. -/
theorem exists_polynomial_prime_modulus_trichotomy
    (F : Finset XiZeroCopy) {θ σ β : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
    let L := ‖-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))‖ *
        boundaryModeAmplitude (ρ.re - σ)
    0 < L ∧ ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ κ : ℝ, 0 < κ →
      let r := polynomialObservationExponent d κ (ρ.re - σ) A
      let U := fun t : ℝ => ‖rotatedPrimeDampingFilter
        (divisorDampingFilter F ρ β (t ^ (-κ))) σ β (polynomialDampingSpeed A t)
          (t ^ (-κ)) (boundaryDampingAngle t) t‖
      (r < 0 → Tendsto U atTop (𝓝 0)) ∧
      (r = 0 → Tendsto U atTop (𝓝 L)) ∧
      (0 < r → Tendsto U atTop atTop) := by
  classical
  dsimp only
  have hC := divisorDampingFilter_limit_constant_ne_zero F ρ
    (by linarith only [hσ, hρσ]) hρ1 hρ
  have hL := mul_pos (norm_pos_iff.mpr hC) (boundaryModeAmplitude_pos (ρ.re - σ))
  refine ⟨hL, ?_⟩
  obtain ⟨A₀, hA₀, hsharp⟩ := exists_sharp_polynomial_prime_modulus_threshold
    F hσ hgap hrest ρ hρσ hρ1 hρ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA κ hκ
  have hh := hsharp A hA κ hκ
  refine ⟨fun hr => tendsto_zero_of_power_quotient hh hr, ?_,
    fun hr => tendsto_atTop_of_power_quotient hh hL hr⟩
  intro hr
  simpa only [hr, Real.rpow_zero, div_one] using hh

/-- Either AAL holds, or actual top zeros supply a family of prime filters
with a fixed positive critical modulus, independent of the radius exponent. -/
theorem asymptoticAbscissaLaw_or_critical_polynomial_prime_levels :
    AsymptoticAbscissaLaw ∨
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β →
          let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
          let L := ‖-((analyticOrderAt zetaResidueUnit (xiZero q)).toNat : ℂ) *
            ((xiZero q - 1) * ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
              (xiZero q - xiZero p))‖ * boundaryModeAmplitude (β - σ)
          0 < L ∧ ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
            let κ := ((A + 1) * (β - σ) - 1) / (2 * (d : ℝ))
            0 < κ ∧ Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
              (divisorDampingFilter F (xiZero q) β (t ^ (-κ))) σ β (polynomialDampingSpeed A t)
                (t ^ (-κ)) (boundaryDampingAngle t) t‖) atTop (𝓝 L) := by
  classical
  by_cases h : AsymptoticAbscissaLaw
  · exact Or.inl h
  right
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, htop, hmax, hrest, _⟩ :=
    not_asymptoticAbscissaLaw_has_escaping_layer_profile h
  have hσ : 1 / 2 < σ := by linarith only [hθ, hgap]
  have hall : ∀ q : XiZeroCopy, (xiZero q).re ≤ β := by
    intro q
    by_cases hq : q ∈ F
    · exact hmax q hq
    · exact (hrest q hq).trans (hgap.trans hσβ).le
  refine ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, ?_⟩
  intro q _ hqβ
  dsimp only
  let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
  have hd : 0 < (d : ℝ) := by dsimp only [d]; positivity
  have hx : 0 < β - σ := sub_pos.mpr hσβ
  obtain ⟨hL, A₁, hA₁, hcases⟩ := exists_polynomial_prime_modulus_trichotomy
    F hσ hgap hrest (xiZero q) (by rwa [hqβ]) (by rwa [hqβ]) (xi_xiZero q)
  simp only [hqβ] at hL hcases
  refine ⟨hL, max A₁ (2 / (β - σ)), hA₁.trans_le (le_max_left _ _), ?_⟩
  intro A hA
  let κ := ((A + 1) * (β - σ) - 1) / (2 * (d : ℝ))
  have hA₂ : 2 ≤ A * (β - σ) := (div_le_iff₀ hx).mp ((le_max_right _ _).trans hA)
  have hκ : 0 < κ := by
    apply div_pos _ (by positivity : 0 < 2 * (d : ℝ))
    nlinarith only [hA₂, hx]
  have hr : polynomialObservationExponent d κ (β - σ) A = 0 := by
    dsimp only [polynomialObservationExponent, κ]
    field_simp [hd.ne']
    ring
  exact ⟨hκ, (hcases A ((le_max_left _ _).trans hA) κ hκ).2.1 hr⟩

#print axioms tendsto_boundary_mode_normalized_modulus
#print axioms tendsto_polynomial_mode_modulus
#print axioms polynomial_mode_growth_iff
#print axioms tendsto_polynomial_mode_critical
#print axioms boundary_mode_zero_of_short_damping_scale
#print axioms exists_sharp_polynomial_prime_modulus_threshold
#print axioms exists_polynomial_prime_modulus_trichotomy
#print axioms asymptoticAbscissaLaw_or_critical_polynomial_prime_levels

end GaloisForLFunctions.ExceptionalLayerTheory
