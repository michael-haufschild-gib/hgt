import GaloisForLFunctions.RHTower.FZZCigarParitySourceBalancedMellinReflection

/-!
# Krein-antiunitary critical eigenline of the FZZ parity source

The canonical all-scale source-Krein operator anticommutes with the canonical source-metric
antiunitary.  Its positive-imaginary eigenvalue is fixed by the induced spectral action
`lambda ↦ -conj(lambda)`, so its eigenline is projectively antiunitary-fixed.

This file computes the eigenline in the F10 half-density coordinate and proves that its coordinate
has norm exactly one.  Taking its principal argument constructs an explicit centered Mellin
parameter on `Re rho=1/2`; the source eigenvector is exactly `P(2 beta)` times that balanced Mellin
carrier.  Thus literal FZZ parity coefficients generate an unconditional critical-line dynamical
mode with matched reflected crossing.  The remaining RH gate is divisor incidence for every
parity-Mellin zero, not existence of a source-native critical mode.
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical source antiunitary anticommutes with the canonical source-Krein operator. -/
theorem fzzCigarParityDilatedKreinOperator_sourceMetricReflection_anticommute
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinOperator beta
        (fzzCigarParitySourceMetricReflection beta u) =
      -fzzCigarParitySourceMetricReflection beta
        (fzzCigarParityDilatedTwoScaleKreinOperator beta u) := by
  rcases u with ⟨u₁, u₂⟩
  have ha2 := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hp := (fzzKreinPAt_pos hbeta).ne'
  have hr := (fzzKreinRAt_pos hbeta).ne'
  have ha := (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  have hpa2 :
      fzzKreinPAt beta * fzzCigarParitySourceMetricReflectionScale beta ^ (2 : ℕ) =
        fzzKreinRAt beta := by
    rw [ha2]
    field_simp
  have hpa2c :
      (fzzKreinPAt beta : ℂ) *
          (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ^ (2 : ℕ) =
        (fzzKreinRAt beta : ℂ) := by
    exact_mod_cast hpa2
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast ha
  have hrC : (fzzKreinRAt beta : ℂ) ≠ 0 := by exact_mod_cast hr
  apply Prod.ext <;>
    simp [fzzCigarParityDilatedTwoScaleKreinOperator,
      fzzCigarParitySourceMetricReflection, star_add, star_sub, star_mul,
      Complex.conj_ofReal]
  all_goals
    field_simp [haC, hrC]
    ring_nf at hpa2c ⊢
    rw [hpa2c]
    ring

/-- Balanced projective coordinate of the positive-imaginary source eigenline. -/
def fzzCigarParityDilatedKreinEigenlineBalancedCoordinate (beta : ℝ) : ℂ :=
  fzzCigarParitySourceBalancedProjectiveCoordinate beta
    (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)

theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_eq
    (beta : ℝ) :
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta =
      (fzzCigarParitySourceMetricReflectionScale beta : ℂ) *
        (fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
          (fzzKreinPAt beta : ℂ)) /
        (fzzKreinQAt beta : ℂ) := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate,
    fzzCigarParitySourceBalancedProjectiveCoordinate,
    fzzCigarParitySourceProjectiveRatio,
    fzzCigarParityDilatedTwoScaleKreinEigenvector]
  ring

theorem norm_sq_fzzCigarParityDilatedKreinEigenvalue_sub_p
    {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
        (fzzKreinPAt beta : ℂ)‖ ^ (2 : ℕ) =
      fzzKreinPAt beta * fzzKreinQAt beta ^ (2 : ℕ) / fzzKreinRAt beta := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    fzzCigarParityDilatedTwoScaleKreinEigenvalue]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
    Complex.sub_im, Complex.mul_im, mul_zero, zero_add]
  have hsqrt :
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) ^ (2 : ℕ) =
        fzzCigarParityDilatedTwoScaleKreinDiscriminant beta :=
    Real.sq_sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant_pos hbeta).le
  rw [show (0 - fzzKreinPAt beta) * (0 - fzzKreinPAt beta) =
      fzzKreinPAt beta ^ (2 : ℕ) by ring,
    show Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) *
        Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) =
      Real.sqrt (fzzCigarParityDilatedTwoScaleKreinDiscriminant beta) ^ (2 : ℕ) by ring,
    hsqrt, fzzCigarParityDilatedTwoScaleKreinDiscriminant]
  have hr := (fzzKreinRAt_pos hbeta).ne'
  field_simp
  ring

/-- The canonical source eigenline lands exactly on the unit circle in balanced coordinates. -/
theorem norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate
    {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta‖ = 1 := by
  rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_eq beta,
    norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (fzzCigarParitySourceMetricReflectionScale_pos hbeta),
    abs_of_pos (fzzKreinQAt_pos hbeta)]
  have ha2 := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hz2 := norm_sq_fzzCigarParityDilatedKreinEigenvalue_sub_p hbeta
  have hq := fzzKreinQAt_pos hbeta
  have hp := fzzKreinPAt_pos hbeta
  have hr := fzzKreinRAt_pos hbeta
  have hnonneg :
      0 ≤ fzzCigarParitySourceMetricReflectionScale beta *
          ‖fzzCigarParityDilatedTwoScaleKreinEigenvalue beta -
            (fzzKreinPAt beta : ℂ)‖ /
          fzzKreinQAt beta := by
    exact div_nonneg
      (mul_nonneg (fzzCigarParitySourceMetricReflectionScale_pos hbeta).le
        (norm_nonneg _))
      hq.le
  apply (sq_eq_sq₀ hnonneg (by norm_num)).mp
  rw [div_pow, mul_pow, ha2, hz2]
  field_simp

/-- Explicit critical Mellin parameter determined by the phase of the source eigenline. -/
def fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter (beta : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I *
    ((Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) /
      Real.log 2 : ℝ) : ℂ)

theorem fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_re
    (beta : ℝ) :
    (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta).re = 1 / 2 := by
  have hreal :
      (((Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) /
        Real.log 2 : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter,
    Complex.add_re, Complex.mul_re, hreal]
  norm_num

/-- The centered dyadic Mellin character of the explicit critical parameter is exactly the
balanced source-eigenline coordinate. -/
theorem fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDyadicMellinCharacter
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta) =
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta := by
  let y := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta
  have hy : ‖y‖ = 1 :=
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  rw [fzzCigarParityDyadicMellinCharacter, centeredComplexModularCharacter]
  have hexponent :
      (Real.log 2 : ℂ) *
          (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta - 1 / 2) =
        ((Complex.arg y : ℝ) : ℂ) * Complex.I := by
    rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter]
    dsimp only [y]
    push_cast
    field_simp [hlogC]
    ring
  rw [hexponent]
  have hpolar := Complex.norm_mul_exp_arg_mul_I y
  rw [hy] at hpolar
  simpa [y] using hpolar

/-- The canonical positive-imaginary eigenvector is exactly a nonzero scalar multiple of an
explicit critical-line balanced Mellin carrier. -/
theorem fzzCigarParityDilatedKreinEigenvector_eq_balancedCriticalMellinCarrier
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinEigenvector beta =
      (fzzKreinQAt beta : ℂ) •
        fzzCigarParitySourceBalancedMellinCarrier beta
          (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta) := by
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  have hqC : (fzzKreinQAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinQAt_pos hbeta).ne'
  rw [fzzCigarParitySourceBalancedMellinCarrier,
    fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter hbeta]
  apply Prod.ext
  · simp [fzzCigarParityDilatedTwoScaleKreinEigenvector]
  · rw [fzzCigarParityDilatedKreinEigenlineBalancedCoordinate,
      fzzCigarParitySourceBalancedProjectiveCoordinate,
      fzzCigarParitySourceProjectiveRatio,
      fzzCigarParityDilatedTwoScaleKreinEigenvector]
    simp only [Prod.smul_snd, smul_eq_mul]
    field_simp [haC, hqC]

theorem fzzCigarParitySourceMetricReflection_smul
    (beta : ℝ) (c : ℂ) (u : ℂ × ℂ) :
    fzzCigarParitySourceMetricReflection beta (c • u) =
      star c • fzzCigarParitySourceMetricReflection beta u := by
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext <;>
    simp [fzzCigarParitySourceMetricReflection, star_mul]
  all_goals ring

/-- Positive-imaginary source eigenline is projectively fixed by the canonical antiunitary. -/
theorem fzzCigarParitySourceMetricReflection_kreinEigenvector_projectivelyFixed
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParitySourceMetricReflection beta
        (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) =
      star (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) •
        fzzCigarParityDilatedTwoScaleKreinEigenvector beta := by
  have href :
      criticalLineReflectionPoint
          (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta) =
        fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta := by
    apply Complex.ext <;>
      simp [criticalLineReflectionPoint,
        fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_re]
    all_goals norm_num
  rw [fzzCigarParityDilatedKreinEigenvector_eq_balancedCriticalMellinCarrier hbeta,
    fzzCigarParitySourceMetricReflection_smul,
    fzzCigarParitySourceMetricReflection_balancedMellinCarrier hbeta,
    fzzCigarParityDyadicMellinCharacter_eigenlineCriticalParameter hbeta,
    href]
  have hstarq : star (fzzKreinQAt beta : ℂ) = (fzzKreinQAt beta : ℂ) :=
    Complex.conj_ofReal _
  rw [hstarq, smul_smul, smul_smul]
  congr 1
  ring

/-- Anticommutation and imaginary spectral orientation make the reflected source mode an
eigenvector for the same positive-imaginary eigenvalue. -/
theorem fzzCigarParityDilatedKreinOperator_reflectedEigenpair
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedTwoScaleKreinOperator beta
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityDilatedTwoScaleKreinEigenvector beta)) =
      fzzCigarParityDilatedTwoScaleKreinEigenvalue beta •
        fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityDilatedTwoScaleKreinEigenvector beta) := by
  rw [fzzCigarParityDilatedKreinOperator_sourceMetricReflection_anticommute hbeta,
    fzzCigarParityDilatedTwoScaleKreinEigenpair hbeta,
    fzzCigarParitySourceMetricReflection_smul,
    star_fzzCigarParityDilatedTwoScaleKreinEigenvalue_eq_neg]
  simp

/-- The source-derived critical eigenmode has matched balanced grade crossings unconditionally. -/
theorem fzzCigarParityDilatedKreinEigenline_balancedCrossing_eq_reflection
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParitySourceBalancedMellinNormalizedCrossing beta
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta) =
      fzzCigarParitySourceBalancedMellinNormalizedCrossing beta
        (criticalLineReflectionPoint
          (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter beta)) := by
  exact (fzzCigarParitySourceBalancedMellinNormalizedCrossing_eq_reflection_iff
    hbeta _).mpr
      (fzzCigarParityDilatedKreinEigenlineCriticalMellinParameter_re beta)

end

end RHTower
