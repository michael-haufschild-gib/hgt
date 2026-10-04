import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation
import GaloisForLFunctions.RHTower.CCMCoherentGammaModulationRecurrence
import GaloisForLFunctions.RHTower.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarOperatorDomain

/-!
# Full supported Weil energy recovers the finite prime phase law

Fixed frequency modulation preserves the exact Gamma form domain. The Gamma
energy increment tends to zero at high carrier, as do both polar charges.
Consequently one simultaneous prime-phase recurrence clock recovers every
finite-prime quadratic difference from the complete supported source energy.

For the literal sum of the two pole profiles, the recovered difference is the
nonnegative Schur phase energy. Prime two makes it strictly positive at its
half-period whenever its support overlap is nonempty. The same full source has
both signs of fixed-step increments arbitrarily far out in frequency.

This excludes eventual frequency monotonicity. It does not prove a negative
source energy, canonical-head positivity, or the Riemann hypothesis.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RHTower

private theorem gamma_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv gammaHardyPhaseRate x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv gammaHardyPhaseRate)
    (continuous_deriv_gammaHardyPhaseRate.continuousOn :
      ContinuousOn (deriv gammaHardyPhaseRate) (Icc (-1 : ℝ) 1))
  refine ⟨max C (1 + Real.pi / 4), le_trans (by positivity) (le_max_right _ _), fun x => ?_⟩
  by_cases hx : |x| ≤ 1
  · exact (hC x (abs_le.mp hx)).trans (le_max_left _ _)
  have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
  have hx0 : 0 < |x| := lt_of_lt_of_le zero_lt_one hx1
  have he : |deriv gammaHardyPhaseRate x| = |deriv gammaHardyPhaseRate (|x|)| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, deriv_gammaHardyPhaseRate_neg, abs_neg]
  rw [he]
  apply (abs_deriv_gammaHardyPhaseRate_le hx0).trans
  apply le_trans _ (le_max_right _ _)
  have hsq : (1 : ℝ) ≤ |x| ^ 2 := by nlinarith
  have h1 : 1 / |x| ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
  have h2 : Real.pi / (4 * |x|) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  linarith

private theorem gamma_increment_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ,
      |gammaHardyPhaseRate (x+h) - gammaHardyPhaseRate x| ≤ C * |h| := by
  obtain ⟨C,hC,hbound⟩ := gamma_deriv_bounded
  refine ⟨C,hC,fun x h => ?_⟩
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ))
    (fun x _ => differentiable_gammaHardyPhaseRate x)
    (fun x _ => hbound x) convex_univ (mem_univ x) (mem_univ (x+h))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hm

private theorem gamma_increment_tendsto (h : ℝ) :
    Tendsto (fun t : ℝ => gammaHardyPhaseRate (t+h)-gammaHardyPhaseRate t)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t+h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have he := (gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.comp ht).sub
    gammaHardyPhaseRate_sub_log_conductor_tendsto_zero
  have hl := (Real.tendsto_log_comp_add_sub_log h).div_const 2
  have hh := he.add hl
  simp only [sub_zero, add_zero, zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-h)] with t ht0 hth
  dsimp
  rw [Real.log_div (by linarith : t+h ≠ 0) (by positivity : (2*Real.pi : ℝ) ≠ 0),
    Real.log_div ht0.ne' (by positivity : (2*Real.pi : ℝ) ≠ 0)]
  ring

/-- Actual Gamma increment, integrated against an arbitrary physical Fourier mass. -/
theorem tendsto_ccmGamma_modulation_increment (F : SoninL2) (h : ℝ) :
    Tendsto (fun t : ℝ => ∫ ξ : ℝ,
      2 * (gammaHardyPhaseRate (2*Real.pi*(ξ+t+h)) -
        gammaHardyPhaseRate (2*Real.pi*(ξ+t))) * ‖F ξ‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := gamma_increment_bounded
  let B : ℝ → ℝ := fun ξ => (2*C*|2*Real.pi*h|)*‖F ξ‖^2
  have hB : Integrable B :=
    ((Lp.memLp F).integrable_norm_pow (by norm_num)).const_mul _
  have hm (t : ℝ) : AEStronglyMeasurable (fun ξ : ℝ =>
      2*(gammaHardyPhaseRate (2*Real.pi*(ξ+t+h))-
        gammaHardyPhaseRate (2*Real.pi*(ξ+t)))*‖F ξ‖^2) := by
    exact ((continuous_const.mul ((continuous_gammaHardyPhaseRate.comp
      (continuous_const.mul ((continuous_id.add continuous_const).add continuous_const))).sub
      (continuous_gammaHardyPhaseRate.comp
      (continuous_const.mul (continuous_id.add continuous_const))))).aestronglyMeasurable).mul
      ((Lp.memLp F).aestronglyMeasurable.norm.pow 2)
  have hb (t ξ : ℝ) :
      ‖2*(gammaHardyPhaseRate (2*Real.pi*(ξ+t+h))-
        gammaHardyPhaseRate (2*Real.pi*(ξ+t)))*‖F ξ‖^2‖ ≤ B ξ := by
    have hh := hbound (2*Real.pi*(ξ+t)) (2*Real.pi*h)
    rw [show 2*Real.pi*(ξ+t)+2*Real.pi*h = 2*Real.pi*(ξ+t+h) by ring] at hh
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖F ξ‖)]
    change |(2 : ℝ)| * _ * _ ≤ _
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖F ξ‖)]
  have hp (ξ : ℝ) : Tendsto (fun t : ℝ =>
      2*(gammaHardyPhaseRate (2*Real.pi*(ξ+t+h))-
        gammaHardyPhaseRate (2*Real.pi*(ξ+t)))*‖F ξ‖^2) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => 2*Real.pi*(ξ+t)) atTop atTop :=
      ((tendsto_const_nhds (x := ξ)).add_atTop tendsto_id).const_mul_atTop (by positivity)
    have hh := (((gamma_increment_tendsto (2*Real.pi*h)).comp ht).const_mul 2).mul_const
      (‖F ξ‖^2)
    simp only [mul_zero, zero_mul] at hh
    apply hh.congr'
    filter_upwards with t
    dsimp only [Function.comp_def]
    rw [show 2*Real.pi*(ξ+t)+2*Real.pi*h = 2*Real.pi*(ξ+t+h) by ring]
  have hh := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall hm) (Eventually.of_forall fun t => Eventually.of_forall (hb t))
    hB (Eventually.of_forall hp)
  simpa only [integral_zero] using hh

open Complex
open scoped InnerProduct ENNReal FourierTransform
open GaloisForLFunctions.HTGeometry

private theorem fourier_modulation (t : ℝ) (f : SoninL2) :
    fourierUnitary (modulationMul t f) = translateL2 (-t) (fourierUnitary f) := by
  have hm : modulationMul t f = MellinL2.fourierPhaseMulUnitary t f := by
    apply Lp.ext
    filter_upwards [coeFn_modulationMul t f, MellinL2.fourierPhaseMulAux_ae t f]
      with x hx hy
    change (modulationMul t f) x = MellinL2.fourierPhaseMulAux t f x
    rw [hx, hy, MellinL2.fourierPhase, fourierChar_eq_modulationSymbol]
  rw [hm]
  exact MellinL2.fourier_fourierPhaseMulUnitary t f

private theorem form_weight_increment_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ t : ℝ,
      |ccmArchimedeanFormWeight (ξ+t) - ccmArchimedeanFormWeight ξ| ≤ C*|t| := by
  obtain ⟨C,hC,hbound⟩ := gamma_increment_bounded
  refine ⟨4*Real.pi*C, by positivity, fun ξ t => ?_⟩
  have h := hbound (2*Real.pi*ξ) (2*Real.pi*t)
  rw [show 2*Real.pi*ξ+2*Real.pi*t=2*Real.pi*(ξ+t) by ring] at h
  rw [ccmArchimedeanFormWeight_eq_linearArgument,
    ccmArchimedeanFormWeight_eq_linearArgument]
  rw [show 1+2*(gammaHardyPhaseRate (2*Real.pi*(ξ+t))-gammaHardyPhaseRate 0)-
      (1+2*(gammaHardyPhaseRate (2*Real.pi*ξ)-gammaHardyPhaseRate 0)) =
      2*(gammaHardyPhaseRate (2*Real.pi*(ξ+t))-gammaHardyPhaseRate (2*Real.pi*ξ)) by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at h
  nlinarith

private theorem form_fourier_density (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ => ccmArchimedeanFormWeight ξ *
      ‖(fourierUnitary (ccmArchimedeanFormToAperture a u).1) ξ‖^2) := by
  have hi : Integrable (fun ξ => ‖(u.1 : ℝ → ℂ) ξ‖^2)
      ccmArchimedeanFormMeasure := (Lp.memLp u.1).integrable_norm_pow (by norm_num)
  unfold ccmArchimedeanFormMeasure at hi
  rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal] at hi
  have hF : fourierUnitary (ccmArchimedeanFormToAperture a u).1 =
      ccmArchimedeanWeightedToL2 u.1 := fourierUnitary_ccmArchimedeanFourierToTime u.1
  rw [hF]
  apply hi.congr
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal, hξ]
  rfl

private theorem translated_form_density (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    Integrable (fun ξ => ccmArchimedeanFormWeight (ξ+t) *
      ‖(fourierUnitary (ccmArchimedeanFormToAperture a u).1) ξ‖^2) := by
  let F := fourierUnitary (ccmArchimedeanFormToAperture a u).1
  obtain ⟨C,hC,hbound⟩ := form_weight_increment_bounded
  have hi := (form_fourier_density a u).add
    (((Lp.memLp F).integrable_norm_pow (by norm_num)).const_mul (C*|t|))
  apply hi.mono'
    (((measurable_ccmArchimedeanFormWeight.comp (measurable_add_const t)).aestronglyMeasurable).mul
      ((Lp.memLp F).aestronglyMeasurable.norm.pow 2))
  filter_upwards with ξ
  have h := le_trans (le_abs_self _) (hbound ξ t)
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖F ξ‖)
  change ‖ccmArchimedeanFormWeight (ξ+t) * ‖F ξ‖^2‖ ≤
    ccmArchimedeanFormWeight ξ * ‖F ξ‖^2 + C * |t| * ‖F ξ‖^2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ccmArchimedeanFormWeight_pos _).le
    (sq_nonneg _))]
  nlinarith

/-- Physical modulation stays in the exact Gamma form domain at the same aperture. -/
theorem exists_ccmArchimedeanFormDomain_modulation
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    ∃ v : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormToAperture a v =
        ccmApertureModulation a t (ccmArchimedeanFormToAperture a u) := by
  let f := ccmArchimedeanFormToAperture a u
  let F := fourierUnitary f.1
  let g := ccmApertureModulation a t f
  have hG : fourierUnitary g.1 = translateL2 (-t) F := fourier_modulation t f.1
  have hGa : (fourierUnitary g.1 : ℝ → ℂ) =ᵐ[volume] fun ξ => F (ξ-t) := by
    rw [hG]
    simpa only [sub_eq_add_neg] using coeFn_translateL2 (-t) F
  have hi : Integrable (fun ξ => ccmArchimedeanFormWeight ξ * ‖F (ξ-t)‖^2) := by
    have hh := (measurePreserving_add_right volume (-t)).integrable_comp_of_integrable
      (translated_form_density a u t)
    simpa [Function.comp_def, F, f, add_assoc, sub_eq_add_neg] using hh
  have hweight : Integrable (fun ξ => ccmArchimedeanFormWeight ξ *
      ‖(fourierUnitary g.1) ξ‖^2) := hi.congr (by
    filter_upwards [hGa] with ξ hξ
    rw [hξ])
  apply exists_ccmArchimedeanFormDomain_of_fourier_memLp a g
  apply (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable _).aestronglyMeasurable).2
  unfold ccmArchimedeanFormMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal]
  apply hweight.congr
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

/-- Canonical modulation of an actual supported form vector. -/
def ccmArchimedeanFormModulation (a : SuzukiPositiveAperture)
    (t : ℝ) (u : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain a :=
  (exists_ccmArchimedeanFormDomain_modulation a u t).choose

theorem ccmArchimedeanFormModulation_physical (a : SuzukiPositiveAperture)
    (t : ℝ) (u : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormToAperture a (ccmArchimedeanFormModulation a t u) =
      ccmApertureModulation a t (ccmArchimedeanFormToAperture a u) :=
  (exists_ccmArchimedeanFormDomain_modulation a u t).choose_spec

private theorem modulation_form_norm (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (t : ℝ) :
    ‖ccmArchimedeanFormModulation a t u‖^2 =
      ∫ ξ, ccmArchimedeanFormWeight (ξ+t)*
        ‖(fourierUnitary (ccmArchimedeanFormToAperture a u).1) ξ‖^2 := by
  let v := ccmArchimedeanFormModulation a t u
  let F := fourierUnitary (ccmArchimedeanFormToAperture a u).1
  have hF : fourierUnitary (ccmArchimedeanFormToAperture a v).1 =
      ccmArchimedeanWeightedToL2 v.1 := fourierUnitary_ccmArchimedeanFourierToTime v.1
  have hv : (v.1 : ℝ → ℂ) =ᵐ[volume] fun ξ => F (ξ-t) := by
    have hh := ccmArchimedeanFormModulation_physical a t u
    rw [hh] at hF
    change fourierUnitary (modulationMul t (ccmArchimedeanFormToAperture a u).1) = _ at hF
    rw [fourier_modulation] at hF
    have hc := ccmArchimedeanWeightedToL2_coeFn v.1
    rw [← hF] at hc
    exact hc.symm.trans (by simpa only [sub_eq_add_neg] using coeFn_translateL2 (-t) F)
  change ‖v.1‖^2 = _
  rw [norm_sq_ccmArchimedeanFourierL2]
  calc
    _ = ∫ ξ, ccmArchimedeanFormWeight ξ * ‖F (ξ-t)‖^2 :=
      integral_congr_ae (by filter_upwards [hv] with ξ hξ; rw [hξ])
    _ = ∫ ξ, ccmArchimedeanFormWeight (ξ+t) * ‖F ξ‖^2 := by
      have hh := integral_add_right_eq_self (μ := volume)
        (fun ξ => ccmArchimedeanFormWeight ξ * ‖F (ξ-t)‖^2) t
      simpa only [add_sub_cancel_right] using hh.symm

/-- The actual form-norm increment under a fixed modulation tends to zero. -/
theorem tendsto_ccmArchimedeanFormModulation_norm_increment
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (h : ℝ) :
    Tendsto (fun t : ℝ => ‖ccmArchimedeanFormModulation a (t+h) u‖^2 -
      ‖ccmArchimedeanFormModulation a t u‖^2) atTop (𝓝 0) := by
  have hh := tendsto_ccmGamma_modulation_increment
    (fourierUnitary (ccmArchimedeanFormToAperture a u).1) h
  apply hh.congr'
  filter_upwards with t
  rw [modulation_form_norm, modulation_form_norm, ← integral_sub
    (translated_form_density a u (t+h)) (translated_form_density a u t)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [ccmArchimedeanFormWeight_eq_linearArgument, ccmArchimedeanFormWeight_eq_linearArgument]
  rw [← add_assoc ξ t h]
  ring

private theorem modulation_inner (t : ℝ) (f g : SoninL2) :
    inner ℂ (modulationMul t f) (modulationMul t g) = inner ℂ f g := by
  let U : SoninL2 →ₗᵢ[ℂ] SoninL2 :=
    { (modulationMul t).toLinearMap with
      norm_map' := GaloisForLFunctions.norm_modulationMul_eq t }
  exact U.inner_map_map f g

private theorem polar_modulation_tendsto (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    Tendsto (fun t : ℝ => inner ℂ (ccmPolarOperator a (ccmApertureModulation a t f))
      (ccmApertureModulation a t f)) atTop (𝓝 0) := by
  have hc (s : ℝ) := inner_ccmApertureModulation_tendsto_zero a f
    (ccmPolarApertureVector a s)
  simp_rw [inner_ccmPolarOperator, starRingEnd_apply]
  simpa only [star_zero, zero_mul, add_zero] using
    (((hc (-1/2)).star.mul (hc (1/2))).add ((hc (1/2)).star.mul (hc (-1/2))))

/-- At high carrier, the complete supported source increment is precisely the
negative prime-quadratic increment up to a term tending to zero. -/
theorem tendsto_ccmRestrictedWeil_modulation_increment_prime_compensation
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (h : ℝ) :
    Tendsto (fun t : ℝ =>
      ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (t+h) u) -
        ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a t u) +
      (inner ℂ (ccmFinitePrimeOperator a
        (ccmApertureModulation a (t+h) (ccmArchimedeanFormToAperture a u)))
        (ccmApertureModulation a (t+h) (ccmArchimedeanFormToAperture a u))).re -
      (inner ℂ (ccmFinitePrimeOperator a
        (ccmApertureModulation a t (ccmArchimedeanFormToAperture a u)))
        (ccmApertureModulation a t (ccmArchimedeanFormToAperture a u))).re)
      atTop (𝓝 0) := by
  let f := ccmArchimedeanFormToAperture a u
  have ht : Tendsto (fun t : ℝ => t+h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hp := ((polar_modulation_tendsto a f).comp ht).sub (polar_modulation_tendsto a f)
  have hh := (tendsto_ccmArchimedeanFormModulation_norm_increment a u h).add ((Complex.continuous_re.tendsto _).comp hp)
  simp only [sub_zero, Complex.zero_re, add_zero] at hh
  apply hh.congr'
  filter_upwards with t
  simp only [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal,
    ccmArchimedeanFormModulation_physical, ccmRestrictedWeilBoundedDiagonal,
    inner_ccmRestrictedWeilBoundedRemainder, Complex.add_re, Complex.sub_re]
  have hs (s : ℝ) : inner ℂ (ccmApertureModulation a s f) (ccmApertureModulation a s f) =
      inner ℂ f f := modulation_inner s f.1 f.1
  dsimp only [f] at hs
  rw [hs, hs]
  dsimp only [f, Function.comp_def]
  simp only [Complex.sub_re]
  have hn (v : CCMArchimedeanFormDomain a) : ‖v‖^2 = ‖v.1‖^2 := rfl
  simp only [hn]
  ring

private theorem phase_clock (d : ℕ) (v : Fin d → ℝ) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      ∀ i, Tendsto (fun j => modulationSymbol (κ j) (v i)) atTop (𝓝 1) := by
  have hc (j : ℕ) :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      (Nat.succ_pos j) (fun i => 2*Real.pi*v i)
  choose k hk _ m hm using hc
  let κ : ℕ → ℝ := fun j => (k j : ℝ)
  have hκ : Tendsto κ atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    change (j : ℝ) ≤ (k j : ℝ)
    exact_mod_cast (Nat.le_succ j).trans (hk j)
  refine ⟨κ,hκ,fun i => ?_⟩
  have hb (j : ℕ) :
      ‖modulationSymbol (κ j) (v i)-1‖ ≤ 2*Real.pi / ((j+1 : ℕ) : ℝ) := by
    have h := (norm_exp_I_mul_real_sub_one_le_mod_two_pi
      ((k j : ℝ)*(2*Real.pi*v i)) (m j i)).trans (hm j i)
    have heq : modulationSymbol (κ j) (v i) =
        Complex.exp (Complex.I * (((k j : ℝ)*(2*Real.pi*v i) : ℝ) : ℂ)) := by
      unfold modulationSymbol
      dsimp only [κ]
      congr 1
      push_cast
      ring
    rw [heq]
    simpa only [Nat.succ_eq_add_one] using h
  have hi : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hb0 : Tendsto (fun j : ℕ => 2*Real.pi / ((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using hi.const_mul (2*Real.pi)
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using squeeze_zero (fun j => norm_nonneg _) hb hb0

private theorem prime_recurrence (a : SuzukiPositiveAperture) (κ : ℕ → ℝ)
    (hp : ∀ n ≤ Nat.floor (Real.exp (2*a.1)),
      Tendsto (fun j => modulationSymbol (κ j) (Real.log n)) atTop (𝓝 1))
    (f : suzukiApertureHilbert a) :
    Tendsto (fun j => inner ℂ (ccmFinitePrimeOperator a (ccmApertureModulation a (κ j) f))
      (ccmApertureModulation a (κ j) f))
      atTop (𝓝 (inner ℂ (ccmFinitePrimeOperator a f) f)) := by
  have hm (n : ℕ) (hn : n ≤ Nat.floor (Real.exp (2*a.1))) :
      Tendsto (fun j => modulationSymbol (κ j) (-Real.log n)) atTop (𝓝 1) := by
    have he (t h : ℝ) : modulationSymbol t (-h) = star (modulationSymbol t h) := by
      change modulationSymbol t (-h) = (starRingEnd ℂ) (modulationSymbol t h)
      rw [conj_modulationSymbol]
      unfold modulationSymbol
      congr 1
      push_cast
      ring
    simpa only [he, star_one] using (hp n hn).star
  simp_rw [inner_ccmFinitePrimeOperator, inner_ccmPrimeTransportOperator]
  apply tendsto_finsetSum
  intro n hn
  have hn' := (Finset.mem_Icc.mp hn).2
  change Tendsto (fun j => (ArithmeticFunction.vonMangoldt n : ℂ) *
    (((1 / Real.sqrt n : ℝ) : ℂ) *
      (inner ℂ (logTranslationCLM (Real.log n) (modulationMul (κ j) f.1))
        (modulationMul (κ j) f.1) +
       inner ℂ (logTranslationCLM (-Real.log n) (modulationMul (κ j) f.1))
        (modulationMul (κ j) f.1)))) _ _
  simp_rw [logTranslationCLM_modulationMul_apply, inner_smul_left, modulation_inner,
    starRingEnd_apply]
  simpa only [star_one, one_mul, mul_assoc] using
    (((hp n hn').star.mul_const (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1)).add
      ((hm n hn').star.mul_const (inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1))).const_mul
        ((ArithmeticFunction.vonMangoldt n : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ))

/-- One source-independent recurrent clock recovers every actual finite-prime
energy difference from complete supported Weil energy increments. -/
theorem exists_ccmRestrictedWeil_modulation_prime_phase_clock (a : SuzukiPositiveAperture) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      ∀ (u : CCMArchimedeanFormDomain a) (h : ℝ),
      Tendsto (fun j =>
        ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (κ j+h) u) -
          ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (κ j) u))
        atTop (𝓝 ((inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re -
          (inner ℂ (ccmFinitePrimeOperator a
            (ccmApertureModulation a h (ccmArchimedeanFormToAperture a u)))
            (ccmApertureModulation a h (ccmArchimedeanFormToAperture a u))).re)) := by
  let N := Nat.floor (Real.exp (2*a.1))
  obtain ⟨κ,hκ,hp⟩ := phase_clock (N+1) (fun i => Real.log (i : ℕ))
  have hp' (n : ℕ) (hn : n ≤ N) := hp ⟨n,Nat.lt_succ_of_le hn⟩
  refine ⟨κ,hκ,fun u h => ?_⟩
  let f := ccmArchimedeanFormToAperture a u
  have hbase := (Complex.continuous_re.tendsto _).comp (prime_recurrence a κ hp' f)
  have hshift := (Complex.continuous_re.tendsto _).comp
    (prime_recurrence a κ hp' (ccmApertureModulation a h f))
  have hc (j : ℕ) : ccmApertureModulation a (κ j) (ccmApertureModulation a h f) =
      ccmApertureModulation a (κ j+h) f := by
    apply Subtype.ext
    exact modulationMul_modulationMul (κ j) h f.1
  simp_rw [hc] at hshift
  have he := (tendsto_ccmRestrictedWeil_modulation_increment_prime_compensation a u h).comp hκ
  have hh := (he.sub hshift).add hbase
  simp only [zero_sub, neg_add_eq_sub] at hh
  convert hh using 1
  funext j
  dsimp only [f, Function.comp_def]
  ring

private theorem row_potential_modulation (a : SuzukiPositiveAperture)
    (t : ℝ) (f : suzukiApertureHilbert a) :
    ccmPrimePoleRowPotential a (ccmApertureModulation a t f).1 =
      ccmPrimePoleRowPotential a f.1 := by
  unfold ccmPrimePoleRowPotential
  apply Finset.sum_congr rfl
  intro n _
  have he (h : ℝ) :
      (∫ x, ccmPrimePoleRowDensity a h (ccmApertureModulation a t f).1 x) =
      ∫ x, ccmPrimePoleRowDensity a h f.1 x := by
    apply integral_congr_ae
    filter_upwards [coeFn_modulationMul t f.1] with x hx
    change (modulationMul t f.1) x = _ at hx
    unfold ccmPrimePoleRowDensity
    change _ * ‖(modulationMul t f.1) x‖^2 = _
    rw [hx, norm_mul, norm_modulationSymbol, one_mul]
  rw [he, he]

private theorem pole_energy_zero (a : SuzukiPositiveAperture) :
    ccmPrimePoleSchurEnergy a (ccmSchurPoleVector a).1 = 0 := by
  unfold ccmPrimePoleSchurEnergy
  apply Finset.sum_eq_zero
  intro n _
  have he := ccmPrimePoleEdgeEnergy_modulatedPole a 0 (Real.log n)
  have hm : ccmApertureModulation a 0 (ccmSchurPoleVector a) = ccmSchurPoleVector a :=
    Subtype.ext (modulationMul_zero_apply _)
  simp only [hm, modulationSymbol_zero, sub_self, norm_zero, zero_pow two_ne_zero,
    zero_mul] at he
  rw [he, mul_zero]

private theorem pole_phase_gap (a : SuzukiPositiveAperture) (h : ℝ) :
    (inner ℂ (ccmFinitePrimeOperator a (ccmSchurPoleVector a)) (ccmSchurPoleVector a)).re -
      (inner ℂ (ccmFinitePrimeOperator a (ccmApertureModulation a h (ccmSchurPoleVector a)))
        (ccmApertureModulation a h (ccmSchurPoleVector a))).re =
      ccmPrimePoleSchurEnergy a (ccmApertureModulation a h (ccmSchurPoleVector a)).1 := by
  have h0 := ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential a (ccmSchurPoleVector a)
  have hh := ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential a
    (ccmApertureModulation a h (ccmSchurPoleVector a))
  rw [pole_energy_zero, zero_add] at h0
  rw [row_potential_modulation, ← h0] at hh
  linarith

private theorem pole_phase_gap_neg (a : SuzukiPositiveAperture) (h : ℝ) :
    ccmPrimePoleSchurEnergy a (ccmApertureModulation a (-h) (ccmSchurPoleVector a)).1 =
      ccmPrimePoleSchurEnergy a (ccmApertureModulation a h (ccmSchurPoleVector a)).1 := by
  unfold ccmPrimePoleSchurEnergy
  apply Finset.sum_congr rfl
  intro n _
  rw [ccmPrimePoleEdgeEnergy_modulatedPole, ccmPrimePoleEdgeEnergy_modulatedPole,
    ← conj_modulationSymbol]
  have he : ‖(starRingEnd ℂ) (modulationSymbol h (Real.log n))-1‖ =
      ‖modulationSymbol h (Real.log n)-1‖ := by
    rw [show (starRingEnd ℂ) (modulationSymbol h (Real.log n))-1 =
      (starRingEnd ℂ) (modulationSymbol h (Real.log n)-1) by simp,
      Complex.norm_conj]
  rw [he]

private theorem pole_row_two_pos (a : SuzukiPositiveAperture)
    (ha : Real.log 2 < 2*a.1) :
    0 < ∫ x : ℝ, ccmPrimePoleRowDensity a (Real.log 2) (ccmSchurPoleVector a).1 x := by
  let F := ccmPrimePoleRowDensity a (Real.log 2) (ccmSchurPoleVector a).1
  rw [integral_pos_iff_support_of_nonneg
    (fun x => (ccmPrimePoleRowDensity_bound a (Real.log 2) (ccmSchurPoleVector a).1 x).1)
    (integrable_ccmPrimePoleRowDensity a (Real.log 2) (ccmSchurPoleVector a).1)]
  have hsub : ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) (a.1-Real.log 2) → x ∈ Function.support F := by
    filter_upwards [ccmSchurPoleVector_coeFn a] with x hw hx
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hxi : x ∈ centralInterval a.1 := ⟨hx.1.le, by linarith [hx.2]⟩
    have hxh : x+Real.log 2 ∈ centralInterval a.1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    apply Function.mem_support.mpr
    apply ne_of_gt
    dsimp only [F, ccmPrimePoleRowDensity]
    rw [indicator_of_mem hxh, hw, indicator_of_mem hxi, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (primePoleProfile_pos x)]
    exact mul_pos (div_pos (primePoleProfile_pos _) (primePoleProfile_pos _))
      (sq_pos_of_pos (primePoleProfile_pos _))
  have hv : 0 < volume (Ioo (-a.1) (a.1-Real.log 2)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hv.trans_le (measure_mono_ae hsub)

private theorem pole_half_clock_gap_pos (a : SuzukiPositiveAperture)
    (ha : Real.log 2 < 2*a.1) :
    0 < ccmPrimePoleSchurEnergy a
      (ccmApertureModulation a (1/(2*Real.log 2)) (ccmSchurPoleVector a)).1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hphase : modulationSymbol (1/(2*Real.log 2)) (Real.log 2) = -1 := by
    unfold modulationSymbol
    rw [show 2*Real.pi*(1/(2*Real.log 2)*Real.log 2) = Real.pi by field_simp]
    exact Complex.exp_pi_mul_I
  have hedge : 0 < ccmPrimePoleEdgeEnergy a (Real.log 2)
      (ccmApertureModulation a (1/(2*Real.log 2)) (ccmSchurPoleVector a)).1 := by
    rw [ccmPrimePoleEdgeEnergy_modulatedPole, hphase]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (by norm_num))) (pole_row_two_pos a ha)
  have hvisible : 2 ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊ := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl, (Nat.le_floor_iff (Real.exp_pos _).le).mpr ?_⟩
    have hh := Real.exp_lt_exp.mpr ha
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh.le
  have hw : 0 < (ArithmeticFunction.vonMangoldt 2 : ℝ) / Real.sqrt 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos hl (Real.sqrt_pos.mpr (by norm_num))
  unfold ccmPrimePoleSchurEnergy
  apply (mul_pos hw hedge).trans_le
  exact Finset.single_le_sum
    (s := Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊)
    (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt (n : ℝ) *
      ccmPrimePoleEdgeEnergy a (Real.log n)
        (ccmApertureModulation a (1/(2*Real.log 2)) (ccmSchurPoleVector a)).1)
    (fun n _ => mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (ccmPrimePoleEdgeEnergy_nonneg a (Real.log n) _)) hvisible

/-- A literal supported pole profile has both signs of fixed-step full Weil energy
increments arbitrarily far out in frequency. This does not assert negative energy. -/
theorem ccmRestrictedWeil_pole_modulation_two_increment_signs
    (a : SuzukiPositiveAperture) (ha : Real.log 2 < 2*a.1) (R : ℝ) :
    let u := ccmPolarFormVector a (1/2) + ccmPolarFormVector a (-1/2)
    let h := 1/(2*Real.log 2)
    (∃ t : ℝ, R ≤ t ∧
      ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a t u) <
        ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (t+h) u)) ∧
    (∃ t : ℝ, R ≤ t ∧
      ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (t+h) u) <
        ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a t u)) := by
  let u := ccmPolarFormVector a (1/2) + ccmPolarFormVector a (-1/2)
  let h := 1/(2*Real.log 2)
  have hu : ccmArchimedeanFormToAperture a u = ccmSchurPoleVector a := by
    simp only [u, map_add, ccmArchimedeanFormToAperture_polar, ccmSchurPoleVector]
  obtain ⟨κ,hκ,hphase⟩ := exists_ccmRestrictedWeil_modulation_prime_phase_clock a
  have hp := hphase u h
  have hn := hphase u (-h)
  rw [hu, pole_phase_gap] at hp hn
  rw [pole_phase_gap_neg] at hn
  have hd := pole_half_clock_gap_pos a ha
  have hp0 := hp.eventually (lt_mem_nhds hd)
  have hn0 := hn.eventually (lt_mem_nhds hd)
  constructor
  · obtain ⟨j,hj,hk⟩ := ((hκ.eventually_ge_atTop R).and hp0).exists
    refine ⟨κ j,hj,?_⟩
    change 0 < _ - _ at hk
    exact sub_pos.mp hk
  · obtain ⟨j,hj,hk⟩ := ((hκ.eventually_ge_atTop (R+h)).and hn0).exists
    refine ⟨κ j-h,by linarith,?_⟩
    change 0 < _ - _ at hk
    change ccmRestrictedWeilSourceQuadratic a
        (ccmArchimedeanFormModulation a ((κ j-h)+h) u) <
      ccmRestrictedWeilSourceQuadratic a (ccmArchimedeanFormModulation a (κ j-h) u)
    rw [sub_add_cancel]
    simpa only [sub_eq_add_neg] using (sub_pos.mp hk)

end RHTower
