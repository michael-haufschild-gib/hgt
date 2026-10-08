import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianExtraction
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# Exact Gaussian energy extraction at the actual critical boundary

The squared source has one simple pole in the open right critical half-plane.
Its residue is computed locally, without a zero-free strip premise. Uniform
Gaussian decay and a compact radial majorant pay the shift to the measurable
critical trace. The physical signed energy equals its arithmetic kernel sum
plus the exact polar correction.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial GaussZeroSum WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

/-- The squared-source Gaussian integrand is holomorphic off its actual pole. -/
theorem differentiableAt_quantizationGaussianInteriorIntegrand (hW : WeilPositiveFull lam)
    (T : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (quantizationGaussianInteriorIntegrand hW T) s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hG : Gammaℝ (1 - (1 - s)) ≠ 0 := by
    rw [sub_sub_cancel]
    exact Gammaℝ_ne_zero_of_re_pos (by linarith)
  exact (((zetaChi_analyticAt hG).differentiableAt.comp s
    (by fun_prop)).mul
      ((differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz)
        hs hs0 hs1).pow 2)).mul (differentiable_gaussWeight T s)

/-- The Gaussian squared-source pole has residue minus half its squared residue. -/
theorem tendsto_mul_quantizationGaussianInteriorIntegrand (hW : WeilPositiveFull lam)
    (T : ℝ) :
    Tendsto (fun s : ℂ => (s - 1) * quantizationGaussianInteriorIntegrand hW T s)
      (𝓝[≠] 1) (𝓝 (-(quantizationCompletion hW 1) ^ 2 / 2 * gaussWeight T 1)) := by
  let A (s : ℂ) := quantizationCompletion hW s / (s * Gammaℝ s)
  have hA : ContinuousAt A 1 :=
    (hasDerivAt_quantizationCompletion hW (s := 1) (by norm_num)).continuousAt.div
      (continuousAt_id.mul hasDerivAt_Gammaℝ_one.continuousAt) (by simp [Gammaℝ_one])
  have hp : ContinuousAt zetaResidueFactor 1 := (differentiable_zetaResidueFactor 1).continuousAt
  have hz : ContinuousAt (fun s : ℂ => riemannZeta (1 - s)) 1 :=
    (differentiableAt_riemannZeta (by norm_num : (1 : ℂ) - 1 ≠ 1)).continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hc : ContinuousAt (fun s : ℂ =>
      A s ^ 2 * riemannZeta (1 - s) / zetaResidueFactor s * gaussWeight T s) 1 :=
    (((hA.pow 2).mul hz).div hp (by simp)).mul (differentiable_gaussWeight T 1).continuousAt
  have hv : A 1 ^ 2 * riemannZeta (1 - 1) / zetaResidueFactor 1 * gaussWeight T 1 =
      -(quantizationCompletion hW 1) ^ 2 / 2 * gaussWeight T 1 := by
    simp only [A, Gammaℝ_one, one_mul, div_one, sub_self, riemannZeta_zero,
      zetaResidueFactor_one]
    ring
  rw [← hv]
  refine hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ?_
  have hre' : ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), 1 / 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hre : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), 1 / 2 < s.re :=
    hre'.filter_mono nhdsWithin_le_nhds
  have hpne : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), zetaResidueFactor s ≠ 0 :=
    (hp.eventually_ne (by simp)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hre, hpne] with s hs1 hs hp0
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro hz0
    rw [zetaResidueFactor_of_ne hs1, hz0, mul_zero] at hp0
    exact hp0 rfl
  have hFE : riemannZeta (1 - s) = zetaChi (1 - s) * riemannZeta s := by
    have h1 : 1 - s ≠ (0 : ℂ) := sub_ne_zero.mpr (Ne.symm hs1)
    have h2 : 1 - s ≠ (1 : ℂ) := by intro h; apply hs0; linear_combination -h
    simpa only [sub_sub_cancel] using zeta_eq_zetaChi_mul h1 h2
      (by simpa only [sub_sub_cancel] using Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < s.re))
  change A s ^ 2 * riemannZeta (1 - s) / zetaResidueFactor s * gaussWeight T s =
    (s - 1) * (zetaChi (1 - s) * prodF (quantizationCompletion hW) s ^ 2 * gaussWeight T s)
  rw [hFE, zetaResidueFactor_of_ne hs1]
  dsimp [A, prodF]
  field_simp [hs0, sub_ne_zero.mpr hs1, Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < s.re), hζ]


/-- Gaussian suppression is uniform throughout the actual open critical strip. -/
theorem exists_quantizationGaussianInterior_decay (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖quantizationGaussianInteriorIntegrand hW T s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨A, hA, hF⟩ := exists_quantizationProdF_subpolynomial hW (p := 1) (by norm_num)
  let B := Real.exp 2 * A ^ 2
  have hB : 0 ≤ B := by positivity
  have hpoly (s : ℂ) (hs0 : 1 / 2 < s.re) (hs1 : s.re ≤ 3 / 2) (ht : 2 ≤ |s.im|) :
      ‖zetaChi (1 - s) * prodF (quantizationCompletion hW) s ^ 2‖ ≤
        B * (1 + |s.im|) ^ 3 := by
    have hf := hF s.re s.im hs0 hs1 ht
    simp only [Complex.re_add_im, Real.rpow_one] at hf
    have hc := norm_zetaChi_le_half_strip (σ := 1 - s.re) (t := -s.im)
      (by linarith) (by linarith) (by simpa using ht)
    have he : ((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I = 1 - s := by
      push_cast
      linear_combination -s.re_add_im
    rw [he, abs_neg] at hc
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (Real.exp 2 * (1 + |s.im|)) * (A * (1 + |s.im|)) ^ 2 := by gcongr
      _ = _ := by dsimp [B]; ring
  refine ⟨B * Real.exp 1 * (Nat.factorial 5 * Real.exp (3 / 2) * T ^ 5),
    by positivity, fun s hs0 hs1 ht => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2)]
  change ‖(zetaChi (1 - s) * prodF (quantizationCompletion hW) s ^ 2) *
    gaussWeight T s‖ * (1 + s.im ^ 2) ≤ _
  rw [norm_mul]
  have hg := norm_gaussWeight_le_of_re hT (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hs : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
  have hm := one_add_abs_pow_mul_exp_le 5 hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ (B * (1 + |s.im|) ^ 3) *
        (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) * (1 + |s.im|) ^ 2 := by
      gcongr
      exact hpoly s hs0 hs1 ht
    _ = B * Real.exp 1 * ((1 + |s.im|) ^ 5 * Real.exp (-(s.im ^ 2 / T ^ 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

/-- The simple source pole supplies the complete open-strip Gaussian correction. -/
theorem quantizationGaussian_open_shift (hW : WeilPositiveFull lam)
    {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) (hη1 : η < 1 / 4) :
    (∫ t : ℝ, quantizationGaussianInteriorIntegrand hW T (tracePoint η t)) =
      quantizationGaussianRightMoment hW T +
        Real.pi * (quantizationCompletion hW 1) ^ 2 * gaussWeight T 1 := by
  obtain ⟨C, _, hC⟩ := exists_quantizationGaussianInterior_decay hW hT
  have hs := GaloisForLFunctions.HTGeometry.integral_line_sub_integral_line_eq
    (F := quantizationGaussianInteriorIntegrand hW T)
    (a := 1 / 2 + η) (b := 3 / 2) (p := 1)
    (by norm_num; linarith) (by norm_num)
    (fun s hs0 _ hs1 => differentiableAt_quantizationGaussianInteriorIntegrand hW T
      (by linarith) hs1)
    (tendsto_mul_quantizationGaussianInteriorIntegrand hW T)
    (fun s hs0 hs1 ht => hC s (by linarith) hs1 ht)
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hs
  change (∫ t : ℝ, quantizationGaussianInteriorIntegrand hW T
    (((1 / 2 + η : ℝ) : ℂ) + t * I)) = _
  unfold quantizationGaussianRightMoment
  linear_combination -hs

private theorem gaussWeight_critical (T y : ℝ) :
    gaussWeight T (tracePoint 0 y) = (quantizationGaussianWeight T y : ℂ) := by
  unfold gaussWeight quantizationGaussianWeight
  rw [Complex.ofReal_exp]
  congr 1
  unfold tracePoint
  push_cast
  simp only [add_zero, add_sub_cancel_left, mul_pow, Complex.I_sq, mul_neg_one]
  ring

/-- A single integrable bound pays the approach to the actual critical trace. -/
theorem exists_quantizationGaussian_radial_majorant (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Ioo (0 : ℝ) (1 / 4), ∀ y : ℝ,
      ‖quantizationGaussianInteriorIntegrand hW T (tracePoint η y)‖ ≤
        C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C, hC, htail⟩ := exists_quantizationGaussianInterior_decay hW hT
  let K : Set ℂ := Icc (1 / 2 : ℝ) (3 / 4) ×ℂ Icc (-2 : ℝ) 2
  let H (s : ℂ) := zetaChi (1 - s) * quantizationRightMajorant hW s ^ 2 * gaussWeight T s
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn H K := by
    intro s hs
    have hs' := Complex.mem_reProdIm.mp hs
    have hΓ : Gammaℝ (1 - (1 - s)) ≠ 0 := by
      rw [sub_sub_cancel]
      exact Gammaℝ_ne_zero_of_re_pos (by linarith [hs'.1.1])
    exact ((((zetaChi_analyticAt hΓ).continuousAt.comp (continuousAt_const.sub continuousAt_id)).mul
      ((continuousAt_quantizationRightMajorant hW hs'.1.1 hs'.1.2).pow 2)).mul
        (differentiable_gaussWeight T s).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C (5 * max B 0), hC.trans (le_max_left _ _), fun η hη y => ?_⟩
  have hr : (tracePoint η y).re = 1 / 2 + η := by simp [tracePoint]
  have hi : (tracePoint η y).im = y := by simp [tracePoint]
  by_cases hy : 2 ≤ |y|
  · have hb := htail (tracePoint η y) (by rw [hr]; linarith [hη.1])
      (by rw [hr]; linarith [hη.2]) (by rwa [hi])
    rw [hi] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hy' : |y| ≤ 2 := (lt_of_not_ge hy).le
    have hmem : tracePoint η y ∈ K := by
      apply Complex.mem_reProdIm.mpr
      rw [hr, hi]
      exact ⟨⟨by linarith [hη.1], by linarith [hη.2]⟩, abs_le.mp hy'⟩
    have hb : ‖quantizationGaussianInteriorIntegrand hW T (tracePoint η y)‖ ≤ max B 0 := by
      apply le_trans _ ((hB _ hmem).trans (le_max_left _ _))
      simp only [quantizationGaussianInteriorIntegrand, H, norm_mul, norm_pow]
      gcongr
      exact norm_quantizationProdF_le_rightMajorant hW (by rw [hr]; linarith [hη.1])
        (by rw [hr]; linarith [hη.2])
    apply hb.trans
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + y ^ 2)]
    have hsq : y ^ 2 ≤ 4 := by nlinarith [sq_abs y, abs_nonneg y]
    calc
      _ ≤ 5 * max B 0 := by nlinarith [le_max_right B 0]
      _ ≤ _ := le_max_right _ _

/-- Dominated convergence retains the entire physical trace, including its zeros. -/
theorem tendsto_integral_quantizationGaussian (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    Tendsto (fun η : ℝ => ∫ y : ℝ,
      quantizationGaussianInteriorIntegrand hW T (tracePoint η y)) (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y)) := by
  obtain ⟨C, _, hb⟩ := exists_quantizationGaussian_radial_majorant hW hT
  have hη : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  apply tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => C * (1 + y ^ 2)⁻¹)
  · filter_upwards [hη] with η hη
    have hc : Continuous (fun y : ℝ => quantizationGaussianInteriorIntegrand hW T (tracePoint η y)) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hr : (tracePoint η y).re = 1 / 2 + η := by simp [tracePoint]
      have hs1 : tracePoint η y ≠ 1 := by
        intro he
        rw [he] at hr
        norm_num at hr
        linarith [hη.2]
      exact (differentiableAt_quantizationGaussianInteriorIntegrand hW T
        (by rw [hr]; linarith [hη.1]) hs1).continuousAt.comp (by unfold tracePoint; fun_prop)
    exact hc.aestronglyMeasurable
  · filter_upwards [hη] with η hη
    exact Eventually.of_forall (hb η hη)
  · exact _root_.integrable_inv_one_add_sq.const_mul C
  · refine Eventually.of_forall fun y => ?_
    have hp : Continuous (fun η : ℝ => tracePoint η y) := by unfold tracePoint; fun_prop
    have ht : Tendsto (fun η : ℝ => tracePoint η y) (𝓝[>] 0) (𝓝 (tracePoint 0 y)) :=
      (hp.tendsto 0).mono_left nhdsWithin_le_nhds
    have hΓ : Gammaℝ (1 - (1 - tracePoint 0 y)) ≠ 0 := by
      rw [sub_sub_cancel]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num [tracePoint])
    have hc := (zetaChi_analyticAt hΓ).continuousAt.tendsto.comp (tendsto_const_nhds.sub ht)
    have hg := (differentiable_gaussWeight T (tracePoint 0 y)).continuousAt.tendsto.comp ht
    rw [gaussWeight_critical] at hg
    simpa only [Function.comp_def, quantizationGaussianInteriorIntegrand,
      quantizationGaussianSignedIntegrand, tracePoint] using (hc.mul ((tendsto_quantizationTraceF hW y).pow 2)).mul hg

/-- Exact Gaussian shift to the measurable critical boundary with its residue retained. -/
theorem quantizationGaussian_boundary_shift (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y) =
      quantizationGaussianRightMoment hW T +
        Real.pi * (quantizationCompletion hW 1) ^ 2 * gaussWeight T 1 := by
  apply tendsto_nhds_unique (tendsto_integral_quantizationGaussian hW hT)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with η hη
  exact (quantizationGaussian_open_shift hW hT hη.1 hη.2).symm

/-- The actual physical energy has an exact arithmetic kernel formula. -/
theorem quantizationGaussian_energy_kernel (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ((2 * quantizationGaussianEnergy hW T - quantizationGaussianDefect hW T : ℝ) : ℂ) =
      2 * Real.pi * (∑' n : ℕ, quantizationSquareCoeff lam n * (leftKernel T n : ℂ)) +
        Real.pi * (quantizationCompletion hW 1) ^ 2 * gaussWeight T 1 := by
  rw [← quantizationGaussian_signed_energy_complex hW (lt_of_lt_of_le zero_lt_one hT),
    quantizationGaussian_boundary_shift hW hT, quantizationGaussianRightMoment_eq_kernelSum hW hT]

/-- Gaussian arithmetic extraction applies directly to the actual physical energy. -/
theorem quantizationGaussian_energy_extraction (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ‖((2 * quantizationGaussianEnergy hW T - quantizationGaussianDefect hW T : ℝ) : ℂ) -
          Real.pi * (quantizationCompletion hW 1) ^ 2 * gaussWeight T 1 -
          4 * Real.pi * quantizationGaussianCoefficientSum lam T‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := quantizationGaussianRightMoment_extraction hW
  refine ⟨C, hC, fun T hT => ?_⟩
  rw [← quantizationGaussian_signed_energy_complex hW (lt_of_lt_of_le zero_lt_one hT),
    quantizationGaussian_boundary_shift hW hT, add_sub_cancel_right]
  exact hb T hT

end RHTower.WeilSpectral
