import GaloisForLFunctions.RHTower.CCMCoherentExteriorMomentTradeoff

/-!
# Spectral realization of arbitrarily small moment corrections

Every outward position gives a literal first-moment-cancelled Fourier field,
the same completed signed current, and an explicit quartic current bound.
The Taylor coefficient is the actual budget appearing in the energy-budget
product identity, so the norm limit does not conceal its cost.
-/

noncomputable section
open Complex MeasureTheory Filter
open scoped InnerProduct BigOperators

namespace RHTower

theorem fourier_ccmMidpointExteriorOddFieldAt_ae (a : SuzukiPositiveAperture)
    (f : SoninL2) (r : ℝ) (n : ℕ) :
    (fourierUnitary (ccmMidpointExteriorOddFieldAt a f r n) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I*MellinL2.fourierPhase (r/2) ξ *
        (Real.sin (ccmMidpointExteriorFrequencyAt a r n*ξ) : ℂ))*fourierUnitary f ξ := by
  have h := fourier_midpointOdd_translation_packet_ae ({()} : Finset Unit)
    (fun _ => 1) (fun _ => ccmMidpointExteriorShiftAt a r n) r f
  simpa only [Finset.sum_singleton, Complex.ofReal_one, one_smul, one_mul,
    ccmMidpointExteriorOddFieldAt, ccmMidpointExteriorFrequencyAt] using h

theorem fourier_ccmActualHeadMomentCancelledFieldAt_ae (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) (n : ℕ) :
    (fourierUnitary (ccmActualHeadMomentCancelledFieldAt a N f r n) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I*MellinL2.fourierPhase (r/2) ξ *
        (ccmActualHeadMomentCancelledSineAt a N r n ξ : ℂ))*fourierUnitary f ξ := by
  let c : ℂ := (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n : ℝ)
  change (fourierUnitary (ccmActualHeadMidpointOddField (2*a.1) N f r -
    c • ccmMidpointExteriorOddFieldAt a f r n) : ℝ → ℂ) =ᵐ[volume] _
  rw [map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (fourierUnitary (ccmActualHeadMidpointOddField (2*a.1) N f r))
      (c • fourierUnitary (ccmMidpointExteriorOddFieldAt a f r n)),
    Lp.coeFn_smul c (fourierUnitary (ccmMidpointExteriorOddFieldAt a f r n)),
    fourier_ccmActualHeadMidpointOddField_ae (2*a.1) N f r,
    fourier_ccmMidpointExteriorOddFieldAt_ae a f r n] with ξ hs hc hO hE
  rw [hs, Pi.sub_apply, hc, Pi.smul_apply, smul_eq_mul, hO, hE]
  simp only [ccmActualHeadMomentCancelledSineAt, Complex.ofReal_sub, Complex.ofReal_mul, c]
  ring

theorem norm_sq_ccmActualHeadMomentCancelledFieldAt_eq_spectral
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) (r : ℝ) (n : ℕ) :
    ‖ccmActualHeadMomentCancelledFieldAt a N f r n‖^2 =
      ∫ ξ : ℝ, (ccmActualHeadMomentCancelledSineAt a N r n ξ)^2*‖fourierUnitary f ξ‖^2 := by
  rw [← fourierUnitary.norm_map (ccmActualHeadMomentCancelledFieldAt a N f r n), norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourier_ccmActualHeadMomentCancelledFieldAt_ae a N f r n] with ξ hξ
  rw [hξ]
  simp only [norm_mul, norm_neg, Complex.norm_I, MellinL2.norm_fourierPhase,
    Complex.norm_real, Real.norm_eq_abs, one_mul, mul_pow, sq_abs]

theorem ccmActualHeadMomentCancelledCubicBudgetAt_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (r : ℝ) (n : ℕ) :
    0 ≤ ccmActualHeadMomentCancelledCubicBudgetAt a N r n := by
  have h := ccmActualHeadMidpointCubicMoment_nonneg (2*a.1) N r
  unfold ccmActualHeadMomentCancelledCubicBudgetAt
  positivity

/-- A true cubic remainder estimate with the exact budget in the conservation product. -/
theorem abs_ccmActualHeadMomentCancelledSineAt_le (a : SuzukiPositiveAperture)
    (N : ℕ) (r : ℝ) (n : ℕ) (ξ : ℝ) :
    |ccmActualHeadMomentCancelledSineAt a N r n ξ| ≤
      |ξ|^3/6 * ccmActualHeadMomentCancelledCubicBudgetAt a N r n := by
  let M := ccmActualHeadMidpointSignedMoment (2*a.1) N r
  let β := ccmMidpointExteriorFrequencyAt a r n
  have hβpos : 0 < β := ccmMidpointExteriorFrequencyAt_pos a r n
  have hβ : β ≠ 0 := ne_of_gt hβpos
  have he : ccmActualHeadMomentCancelledSineAt a N r n ξ =
      (ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ-ξ*M) -
        (M/β)*(Real.sin (β*ξ)-β*ξ) := by
    change ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ-(M/β)*Real.sin (β*ξ) = _
    have hc : M/β*β = M := div_mul_cancel₀ M hβ
    linear_combination -ξ*hc
  rw [he]
  refine (abs_sub _ _).trans ?_
  have hsin := mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (β*ξ)) (abs_nonneg (M/β))
  rw [abs_sub_comm (β*ξ), abs_mul, mul_pow] at hsin
  rw [abs_mul]
  have hS := abs_ccmActualHeadMidpointSineSymbol_sub_moment_le (2*a.1) N r ξ
  have h := add_le_add hS hsin
  have hc : |M/β| * |β|^3 = |M| * β^2 := by
    rw [abs_div, abs_of_pos hβpos]
    field_simp
  calc
    _ ≤ |ξ|^3/6*ccmActualHeadMidpointCubicMoment (2*a.1) N r +
        |M/β| * (|β|^3*|ξ|^3/6) := h
    _ = |ξ|^3/6*(ccmActualHeadMidpointCubicMoment (2*a.1) N r+|M/β| * |β|^3) := by ring
    _ = _ := by rw [hc]; rfl

def ccmActualHeadMomentCancelledCurrentAt (a : SuzukiPositiveAperture) (N : ℕ)
    (r : ℝ) (n : ℕ) (ξ : ℝ) : ℝ :=
  -2*Real.sin (Real.pi*r*ξ)*ccmActualHeadMomentCancelledSineAt a N r n ξ

theorem abs_ccmActualHeadMomentCancelledCurrentAt_le (a : SuzukiPositiveAperture)
    (N : ℕ) (r : ℝ) (n : ℕ) (ξ : ℝ) :
    |ccmActualHeadMomentCancelledCurrentAt a N r n ξ| ≤
      (|Real.pi*r| / 3 * ccmActualHeadMomentCancelledCubicBudgetAt a N r n)*ξ^4 := by
  have hs : |Real.sin (Real.pi*r*ξ)| ≤ |Real.pi*r| * |ξ| := by
    simpa only [abs_mul] using Real.abs_sin_le_abs (x := Real.pi*r*ξ)
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2))
    (abs_ccmActualHeadMomentCancelledSineAt_le a N r n ξ) (abs_nonneg _)
      (by positivity : 0 ≤ 2*(|Real.pi*r| * |ξ|))
  have hpow : |ξ|^4 = ξ^4 := by
    rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, sq_abs, pow_mul]
  unfold ccmActualHeadMomentCancelledCurrentAt
  simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2*(|Real.pi*r| * |ξ|)*(|ξ|^3/6*ccmActualHeadMomentCancelledCubicBudgetAt a N r n) := h
    _ = (|Real.pi*r| / 3*ccmActualHeadMomentCancelledCubicBudgetAt a N r n)*|ξ|^4 := by ring
    _ = _ := by rw [hpow, abs_mul]

theorem re_inner_increment_momentCancelledFieldAt (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    (inner ℂ (logTranslationCLM r f.1-f.1) (ccmActualHeadMomentCancelledFieldAt a N f.1 r n)).re =
      (inner ℂ (logTranslationCLM r f.1-f.1)
        (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re := by
  rw [ccmActualHeadMomentCancelledFieldAt, inner_sub_right, ccmActualHeadMomentCorrectionAt,
    inner_smul_right, inner_increment_exteriorOddAt_zero, mul_zero, sub_zero,
    re_inner_increment_midpointOdd]

private theorem sine_pair_inner (a b : ℝ) (z : ℂ) :
    (inner ℂ ((2*Complex.I*(a : ℂ))*z) ((-Complex.I*(b : ℂ))*z)).re = -2*a*b*‖z‖^2 := by
  change (inner ℂ ((2*Complex.I*(a : ℂ)) • z) ((-Complex.I*(b : ℂ)) • z)).re = _
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]; ring

/-- Every member of the small-cost family represents the full signed arithmetic current. -/
theorem re_inner_increment_completed_eq_momentCancelledAt_spectral
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    (inner ℂ (logTranslationCLM r f.1-f.1)
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re =
      ∫ ξ : ℝ, ccmActualHeadMomentCancelledCurrentAt a N r n ξ*‖fourierUnitary f.1 ξ‖^2 := by
  rw [← re_inner_increment_momentCancelledFieldAt a N f r n,
    ← fourierUnitary.inner_map_map, MeasureTheory.L2.inner_def]
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (fourierUnitary (logTranslationCLM r f.1-f.1))
    (fourierUnitary (ccmActualHeadMomentCancelledFieldAt a N f.1 r n))
  calc
    _ = ∫ ξ : ℝ, RCLike.re (inner ℂ (fourierUnitary (logTranslationCLM r f.1-f.1) ξ)
        (fourierUnitary (ccmActualHeadMomentCancelledFieldAt a N f.1 r n) ξ)) := (integral_re hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [fourier_logTranslation_increment_ae r f.1,
        fourier_ccmActualHeadMomentCancelledFieldAt_ae a N f.1 r n] with ξ hδ hO
      change (inner ℂ _ _).re = _
      rw [hδ, hO]
      have h₁ : (2*Complex.I*MellinL2.fourierPhase (r/2) ξ*(Real.sin (Real.pi*r*ξ) : ℂ))*fourierUnitary f.1 ξ =
          (2*Complex.I*(Real.sin (Real.pi*r*ξ) : ℂ))*(MellinL2.fourierPhase (r/2) ξ*fourierUnitary f.1 ξ) := by ring
      have h₂ : (-Complex.I*MellinL2.fourierPhase (r/2) ξ*(ccmActualHeadMomentCancelledSineAt a N r n ξ : ℂ))*fourierUnitary f.1 ξ =
          (-Complex.I*(ccmActualHeadMomentCancelledSineAt a N r n ξ : ℂ))*(MellinL2.fourierPhase (r/2) ξ*fourierUnitary f.1 ξ) := by ring
      rw [h₁, h₂, sine_pair_inner, norm_mul, MellinL2.norm_fourierPhase, one_mul]
      rfl

end RHTower
