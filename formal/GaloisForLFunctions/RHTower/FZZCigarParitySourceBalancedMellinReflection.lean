import GaloisForLFunctions.RHTower.FZZCigarParitySourceMetricReflectionTilt

/-!
# Source-balanced Mellin reflection for the FZZ parity carrier

The canonical FZZ source-metric reflection has a projective diagonal tilt on the raw Mellin
carrier.  This file absorbs its square root into the carrier itself: at scale `beta`, the second
coordinate is weighted by `sqrt(P(4 beta)/P(beta))⁻¹`.

In this source half-density coordinate, the same antiunitary sends each carrier to its
functional-equation reflection exactly up to a nonzero projective scalar.  The grade crossing,
normalized by the balanced second-coordinate norm, retains an exact transverse detector:
reflected crossings agree precisely on `Re rho = 1/2`.  Matching this balanced crossing on all
parity-Mellin divisor modes is therefore equivalent to RH; the remaining burden is a dynamical
proof of that matching, not construction of the antiunitary reflection.
-/

open Complex

namespace RHTower

noncomputable section

/-- Mellin carrier in the half-density coordinate selected by the source metric. -/
def fzzCigarParitySourceBalancedMellinCarrier (beta : ℝ) (rho : ℂ) : ℂ × ℂ :=
  (1, ((fzzCigarParitySourceMetricReflectionScale beta)⁻¹ : ℂ) *
    fzzCigarParityDyadicMellinCharacter rho)

/-- The balanced affine coordinate restores the centered Mellin character. -/
def fzzCigarParitySourceBalancedProjectiveCoordinate
    (beta : ℝ) (u : ℂ × ℂ) : ℂ :=
  (fzzCigarParitySourceMetricReflectionScale beta : ℂ) *
    fzzCigarParitySourceProjectiveRatio u

theorem fzzCigarParitySourceBalancedMellinCarrier_coordinate
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceBalancedProjectiveCoordinate beta
        (fzzCigarParitySourceBalancedMellinCarrier beta rho) =
      fzzCigarParityDyadicMellinCharacter rho := by
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  simp [fzzCigarParitySourceBalancedProjectiveCoordinate,
    fzzCigarParitySourceProjectiveRatio,
    fzzCigarParitySourceBalancedMellinCarrier, haC]

/-- The canonical source antiunitary sends each balanced carrier exactly to the reflected carrier
up to its nonzero projective scalar. -/
theorem fzzCigarParitySourceMetricReflection_balancedMellinCarrier
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceMetricReflection beta
        (fzzCigarParitySourceBalancedMellinCarrier beta rho) =
      star (fzzCigarParityDyadicMellinCharacter rho) •
        fzzCigarParitySourceBalancedMellinCarrier beta
          (criticalLineReflectionPoint rho) := by
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  have hz : star (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)
  have hz' :
      (starRingEnd ℂ) (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 := hz
  apply Prod.ext
  · simp [fzzCigarParitySourceMetricReflection,
      fzzCigarParitySourceBalancedMellinCarrier, Complex.conj_ofReal, haC]
  · simp only [fzzCigarParitySourceMetricReflection,
      fzzCigarParitySourceBalancedMellinCarrier,
      Prod.smul_snd, smul_eq_mul, star_one, mul_one]
    rw [fzzCigarParityDyadicMellinCharacter_reflection]
    field_simp [haC, hz']
    rfl

/-- In the balanced coordinate, the source antiunitary implements functional-equation reflection
without any residual scalar tilt. -/
theorem fzzCigarParitySourceMetricReflection_balancedCoordinate
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceBalancedProjectiveCoordinate beta
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParitySourceBalancedMellinCarrier beta rho)) =
      fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) := by
  rw [fzzCigarParitySourceMetricReflection_balancedMellinCarrier hbeta]
  have hz : star (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)
  have hz' :
      (starRingEnd ℂ) (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 := hz
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  simp [fzzCigarParitySourceBalancedProjectiveCoordinate,
    fzzCigarParitySourceProjectiveRatio,
    fzzCigarParitySourceBalancedMellinCarrier]
  field_simp [hz', haC]

/-- Grade crossing normalized by the norm of the balanced carrier's second coordinate. -/
def fzzCigarParitySourceBalancedMellinNormalizedCrossing
    (beta : ℝ) (rho : ℂ) : ℂ :=
  fzzCigarParityDilatedTwoScaleGradeCrossing beta
      (fzzCigarParitySourceBalancedMellinCarrier beta rho) /
    (‖(fzzCigarParitySourceBalancedMellinCarrier beta rho).2‖ : ℂ)

theorem fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceBalancedMellinNormalizedCrossing beta rho =
      (fzzKreinQAt beta : ℂ) *
          (fzzCigarParityDyadicMellinCharacter rho /
            (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ)) +
        (fzzKreinRAt beta : ℂ) *
          ((fzzCigarParitySourceMetricReflectionScale beta)⁻¹ : ℂ) *
          (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) := by
  rw [fzzCigarParitySourceBalancedMellinNormalizedCrossing,
    fzzCigarParitySourceBalancedMellinCarrier]
  push_cast
  let a : ℝ := fzzCigarParitySourceMetricReflectionScale beta
  let z : ℂ := fzzCigarParityDyadicMellinCharacter rho
  let n : ℝ := ‖z‖
  have hapos : 0 < a := fzzCigarParitySourceMetricReflectionScale_pos hbeta
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast hapos.ne'
  have hnpos : 0 < n := by
    dsimp only [n, z]
    exact norm_fzzCigarParityDyadicMellinCharacter_pos rho
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnorm : ‖(a : ℂ)⁻¹ * z‖ = a⁻¹ * n := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hapos]
  have hstar : star z * z = ((n ^ 2 : ℝ) : ℂ) := by
    simpa [n] using Complex.conj_mul' z
  have hstarA : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  have hstarScaled :
      star ((a : ℂ)⁻¹ * z) * ((a : ℂ)⁻¹ * z) =
        (a : ℂ)⁻¹ ^ 2 * ((n ^ 2 : ℝ) : ℂ) := by
    rw [star_mul, star_inv₀, hstarA]
    calc
      star z * (a : ℂ)⁻¹ * ((a : ℂ)⁻¹ * z) =
          (a : ℂ)⁻¹ ^ 2 * (star z * z) := by ring
      _ = (a : ℂ)⁻¹ ^ 2 * ((n ^ 2 : ℝ) : ℂ) := by rw [hstar]
  change
    fzzCigarParityDilatedTwoScaleGradeCrossing beta
        (1, (a : ℂ)⁻¹ * z) /
      (‖(a : ℂ)⁻¹ * z‖ : ℂ) =
      (fzzKreinQAt beta : ℂ) * (z / (n : ℂ)) +
        (fzzKreinRAt beta : ℂ) * (a : ℂ)⁻¹ * (n : ℂ)
  rw [fzzCigarParityDilatedTwoScaleGradeCrossing,
    fzzCigarParityDilatedTwoScaleGrade,
    fzzCigarParityDilatedTwoScaleKreinPairing, hnorm]
  simp only [star_one, mul_zero, add_zero, mul_one, zero_add]
  rw [show (fzzKreinRAt beta : ℂ) * star ((a : ℂ)⁻¹ * z) *
      ((a : ℂ)⁻¹ * z) =
      (fzzKreinRAt beta : ℂ) *
        ((a : ℂ)⁻¹ ^ 2 * ((n ^ 2 : ℝ) : ℂ)) by
          rw [mul_assoc, hstarScaled]]
  push_cast
  field_simp [haC, hnC]

/-- Balancing rescales but does not erase the transverse reflected-crossing defect. -/
theorem fzzCigarParitySourceBalancedMellinNormalizedCrossing_sub_reflection
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceBalancedMellinNormalizedCrossing beta rho -
        fzzCigarParitySourceBalancedMellinNormalizedCrossing beta
          (criticalLineReflectionPoint rho) =
      ((fzzCigarParitySourceMetricReflectionScale beta)⁻¹ : ℂ) *
        (fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
          fzzCigarParityMellinCharacterNormalizedCrossing beta
            (criticalLineReflectionPoint rho)) := by
  rw [fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq hbeta,
    fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq hbeta,
    fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection,
    fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection]
  ring

/-- Balanced reflected crossing equality is still exactly critical-line placement. -/
theorem fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq_reflection_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceBalancedMellinNormalizedCrossing beta rho =
        fzzCigarParitySourceBalancedMellinNormalizedCrossing beta
          (criticalLineReflectionPoint rho) ↔
      rho.re = 1 / 2 := by
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  rw [← sub_eq_zero,
    fzzCigarParitySourceBalancedMellinNormalizedCrossing_sub_reflection hbeta]
  constructor
  · intro hzero
    have hunbalanced :
        fzzCigarParityMellinCharacterNormalizedCrossing beta rho -
          fzzCigarParityMellinCharacterNormalizedCrossing beta
            (criticalLineReflectionPoint rho) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero haC)
    exact (fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff
      hbeta rho).mp (sub_eq_zero.mp hunbalanced)
  · intro hre
    have hunbalanced :=
      (fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff
        hbeta rho).mpr hre
    rw [hunbalanced, sub_self, mul_zero]

/-- Balanced reflected-crossing matching for all literal parity-Mellin divisor modes. -/
def FZZCigarParitySourceBalancedMellinReflectionCrossingMatchedAt (beta : ℝ) : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzCigarParitySourceBalancedMellinNormalizedCrossing beta rho =
      fzzCigarParitySourceBalancedMellinNormalizedCrossing beta
        (criticalLineReflectionPoint rho)

/-- One positive scale of balanced matching remains exactly RH-strength. -/
theorem fzzCigarParitySourceBalancedMellinReflectionCrossingMatchedAt_iff_riemannHypothesis
    {beta : ℝ} (hbeta : 0 < beta) :
    FZZCigarParitySourceBalancedMellinReflectionCrossingMatchedAt beta ↔
      RiemannHypothesis := by
  constructor
  · intro hmatch
    apply fzzCigarParityMellinComplete_iff_riemannHypothesis.mp
    intro rho h0 h1 hmode
    have hre :=
      (fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq_reflection_iff
        hbeta rho).mp (hmatch rho h0 h1 hmode)
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]
  · intro hRH rho h0 h1 hmode
    apply (fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq_reflection_iff
      hbeta rho).mpr
    have hxi : xi rho = 0 :=
      (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero h0 h1).mp hmode
    exact xi_zero_re_eq_half_of_RH hRH hxi

end

end RHTower
