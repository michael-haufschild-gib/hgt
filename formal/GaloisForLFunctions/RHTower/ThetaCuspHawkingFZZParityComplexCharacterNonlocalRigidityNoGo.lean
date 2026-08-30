import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParitySignedNonlocalMomentDeterminacyNoGo
import GaloisForLFunctions.HTGeometry.FlowCharFunUniqueness

/-!
# Full complex Mellin covariance collapses every finite-variation FZZ kernel

Integer Mellin rows leave a moment-indeterminate loophole in signed nonlocal reflection.  The
literal FZZ parity source, however, has a source-defined complex Mellin transform.  On logarithmic
delay, its imaginary Mellin orders are all Fourier characters.

This module represents a finite complex kernel by four finite positive measures: the Jordan parts
of its real and imaginary components.  If every imaginary Mellin order has the reflected FZZ
value, comparison of character covariance at `ξ` and `-ξ` first kills the imaginary component.
Fourier--Stieltjes uniqueness then forces the real component to be the reciprocal-delay atom.
No support, moment, or exponential-window assumption is used.

Reciprocal-Fermi undressing recovers the same essential ultraviolet weight as the local producer.
Thus no polynomially tempered finite-variation complex nonlocal completion can supply FZZ-P's
missing reflection arrow.  A survivor must leave finite variation, abandon universal complex-order
covariance, become divisor-dependent, or accept the forced essential singularity.

`[FZZ-P ROUTE KILL] [COMPLEX MELLIN] [FOURIER RIGIDITY] [CANDIDATE NEW KNOWLEDGE]`
-/

open Filter Topology Asymptotics MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Fermi reciprocal density in logarithmic delay coordinates. -/
def fzzCigarParityLogUndressingDensity (x : ℝ) : ℝ :=
  Real.exp (Real.exp x) + 1

/-- Fermi-weighted reflected target in logarithmic delay: mass `t⁻¹ F(t)` at
`log(t⁻¹)`. -/
def fzzCigarParityLogTargetMeasure (t : FZZCigarPositiveDelay) : Measure ℝ :=
  ENNReal.ofReal ((t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t) •
    Measure.dirac (Real.log (t : ℝ)⁻¹)

private theorem fzzCigarPositiveDelayDensity_pos_complex
    (t : FZZCigarPositiveDelay) : 0 < fzzCigarPositiveDelayDensity t := by
  rw [fzzCigarPositiveDelayDensity, fzzCigarParityDelay_eq_fermi t.property]
  positivity

private theorem integrable_charFunKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ξ : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) μ := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  · rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]

private theorem charFun_add_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    charFun (μ + ν) ξ = charFun μ ξ + charFun ν ξ := by
  rw [charFun_apply_real, charFun_apply_real, charFun_apply_real,
    integral_add_measure (integrable_charFunKernel μ ξ)
      (integrable_charFunKernel ν ξ)]

/-- Fourier rigidity for a finite complex measure presented by four positive parts.  Covariance at
both signs of every character forces the imaginary net measure to vanish and the real net measure
to equal the positive target. -/
private theorem complex_jordan_charFun_rigidity
    (realPositive realNegative imagPositive imagNegative target : Measure ℝ)
    [IsFiniteMeasure realPositive] [IsFiniteMeasure realNegative]
    [IsFiniteMeasure imagPositive] [IsFiniteMeasure imagNegative]
    [IsFiniteMeasure target]
    (hchar : ∀ ξ : ℝ,
      (charFun realPositive ξ - charFun realNegative ξ) +
          Complex.I * (charFun imagPositive ξ - charFun imagNegative ξ) =
        charFun target ξ) :
    imagPositive = imagNegative ∧
      realPositive = realNegative + target := by
  let A : ℝ → ℂ := fun ξ =>
    charFun realPositive ξ - charFun realNegative ξ
  let B : ℝ → ℂ := fun ξ =>
    charFun imagPositive ξ - charFun imagNegative ξ
  let T : ℝ → ℂ := fun ξ => charFun target ξ
  have hAB : ∀ ξ : ℝ, A ξ + Complex.I * B ξ = T ξ := by
    intro ξ
    exact hchar ξ
  have hAneg : ∀ ξ : ℝ,
      A (-ξ) = starRingEnd ℂ (A ξ) := by
    intro ξ
    simp [A, charFun_neg]
  have hBneg : ∀ ξ : ℝ,
      B (-ξ) = starRingEnd ℂ (B ξ) := by
    intro ξ
    simp [B, charFun_neg]
  have hTneg : ∀ ξ : ℝ,
      T (-ξ) = starRingEnd ℂ (T ξ) := by
    intro ξ
    simp [T, charFun_neg]
  have hBzero : ∀ ξ : ℝ, B ξ = 0 := by
    intro ξ
    have hminus := hAB (-ξ)
    rw [hAneg ξ, hBneg ξ, hTneg ξ] at hminus
    have hconj :
        starRingEnd ℂ (A ξ) - Complex.I * starRingEnd ℂ (B ξ) =
          starRingEnd ℂ (T ξ) := by
      have hc := congrArg (starRingEnd ℂ) (hAB ξ)
      simpa [sub_eq_add_neg] using hc
    have hz :
        (2 : ℂ) * Complex.I * starRingEnd ℂ (B ξ) = 0 := by
      calc
        (2 : ℂ) * Complex.I * starRingEnd ℂ (B ξ) =
            (starRingEnd ℂ (A ξ) +
                Complex.I * starRingEnd ℂ (B ξ)) -
              (starRingEnd ℂ (A ξ) -
                Complex.I * starRingEnd ℂ (B ξ)) := by ring
        _ = starRingEnd ℂ (T ξ) - starRingEnd ℂ (T ξ) := by
          rw [hminus, hconj]
        _ = 0 := sub_self _
    have hstar : starRingEnd ℂ (B ξ) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left
        (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    have hc := congrArg (starRingEnd ℂ) hstar
    simpa using hc
  have hAeq : ∀ ξ : ℝ, A ξ = T ξ := by
    intro ξ
    simpa [hBzero ξ] using hAB ξ
  constructor
  · apply Measure.ext_of_charFun
    funext ξ
    exact sub_eq_zero.mp (hBzero ξ)
  · apply Measure.ext_of_charFun
    funext ξ
    rw [charFun_add_finite]
    have hAT :
        charFun realPositive ξ - charFun realNegative ξ =
          charFun target ξ := by
      simpa [A, T] using hAeq ξ
    calc
      charFun realPositive ξ =
          (charFun realPositive ξ - charFun realNegative ξ) +
            charFun realNegative ξ := by ring
      _ = charFun target ξ + charFun realNegative ξ := by rw [hAT]
      _ = charFun realNegative ξ + charFun target ξ := by ring

/-- Four-Jordan-part data for a finite-variation complex nonlocal reflection of the literal FZZ
source.  The output coordinate is logarithmic delay, so `all_imaginary_grades` is exactly
covariance for every imaginary Mellin order. -/
structure FZZCigarParityComplexCharacterNonlocalFEReflectionData where
  realPositive : FZZCigarPositiveDelay → Measure ℝ
  realNegative : FZZCigarPositiveDelay → Measure ℝ
  imagPositive : FZZCigarPositiveDelay → Measure ℝ
  imagNegative : FZZCigarPositiveDelay → Measure ℝ
  realPositive_finite : ∀ t, IsFiniteMeasure (realPositive t)
  realNegative_finite : ∀ t, IsFiniteMeasure (realNegative t)
  imagPositive_finite : ∀ t, IsFiniteMeasure (imagPositive t)
  imagNegative_finite : ∀ t, IsFiniteMeasure (imagNegative t)
  undressing_realPositive_integrable : ∀ t,
    Integrable fzzCigarParityLogUndressingDensity (realPositive t)
  undressing_realNegative_integrable : ∀ t,
    Integrable fzzCigarParityLogUndressingDensity (realNegative t)
  undressing_imagPositive_integrable : ∀ t,
    Integrable fzzCigarParityLogUndressingDensity (imagPositive t)
  undressing_imagNegative_integrable : ∀ t,
    Integrable fzzCigarParityLogUndressingDensity (imagNegative t)
  all_imaginary_grades : ∀ t ξ,
    (charFun (realPositive t) ξ - charFun (realNegative t) ξ) +
          Complex.I *
            (charFun (imagPositive t) ξ - charFun (imagNegative t) ξ) =
      charFun (fzzCigarParityLogTargetMeasure t) ξ

private theorem finite_fzzCigarParityLogTargetMeasure
    (t : FZZCigarPositiveDelay) :
    IsFiniteMeasure (fzzCigarParityLogTargetMeasure t) := by
  refine IsFiniteMeasure.mk ?_
  simp [fzzCigarParityLogTargetMeasure]

/-- Exact finite-complex-kernel classification: the imaginary net kernel vanishes. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.imaginaryPart_eq
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.imagPositive t = D.imagNegative t := by
  letI : IsFiniteMeasure (D.realPositive t) := D.realPositive_finite t
  letI : IsFiniteMeasure (D.realNegative t) := D.realNegative_finite t
  letI : IsFiniteMeasure (D.imagPositive t) := D.imagPositive_finite t
  letI : IsFiniteMeasure (D.imagNegative t) := D.imagNegative_finite t
  letI : IsFiniteMeasure (fzzCigarParityLogTargetMeasure t) :=
    finite_fzzCigarParityLogTargetMeasure t
  exact (complex_jordan_charFun_rigidity
    (D.realPositive t) (D.realNegative t)
    (D.imagPositive t) (D.imagNegative t)
    (fzzCigarParityLogTargetMeasure t) (D.all_imaginary_grades t)).1

/-- Exact finite-complex-kernel classification: the real net kernel is precisely the reciprocal
delay atom. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.realPart_eq
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.realPositive t =
      D.realNegative t + fzzCigarParityLogTargetMeasure t := by
  letI : IsFiniteMeasure (D.realPositive t) := D.realPositive_finite t
  letI : IsFiniteMeasure (D.realNegative t) := D.realNegative_finite t
  letI : IsFiniteMeasure (D.imagPositive t) := D.imagPositive_finite t
  letI : IsFiniteMeasure (D.imagNegative t) := D.imagNegative_finite t
  letI : IsFiniteMeasure (fzzCigarParityLogTargetMeasure t) :=
    finite_fzzCigarParityLogTargetMeasure t
  exact (complex_jordan_charFun_rigidity
    (D.realPositive t) (D.realNegative t)
    (D.imagPositive t) (D.imagNegative t)
    (fzzCigarParityLogTargetMeasure t) (D.all_imaginary_grades t)).2

private theorem integrable_fzzCigarParityLogUndressingDensity_target
    (t : FZZCigarPositiveDelay) :
    Integrable fzzCigarParityLogUndressingDensity
      (fzzCigarParityLogTargetMeasure t) := by
  have hcpos : 0 < (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t :=
    mul_pos (inv_pos.mpr t.property) (fzzCigarPositiveDelayDensity_pos_complex t)
  rw [fzzCigarParityLogTargetMeasure]
  apply (integrable_smul_measure (ENNReal.ofReal_pos.mpr hcpos).ne' (by simp)).mpr
  apply integrable_dirac
  simp [fzzCigarParityLogUndressingDensity]

/-- Reciprocal-Fermi undressing of the exact real classification recovers the forced local
reflection weight. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedRealNet_eq
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.realPositive t) -
        (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.realNegative t) =
      (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
        (Real.exp (t : ℝ) + 1) := by
  have heq := congrArg
    (fun μ : Measure ℝ =>
      ∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂μ)
    (D.realPart_eq t)
  rw [integral_add_measure (D.undressing_realNegative_integrable t)
    (integrable_fzzCigarParityLogUndressingDensity_target t)] at heq
  rw [fzzCigarParityLogTargetMeasure, integral_smul_measure,
    integral_dirac] at heq
  have hcpos : 0 < (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t :=
    mul_pos (inv_pos.mpr t.property) (fzzCigarPositiveDelayDensity_pos_complex t)
  rw [ENNReal.toReal_ofReal hcpos.le] at heq
  simp only [smul_eq_mul] at heq
  rw [fzzCigarParityLogUndressingDensity,
    Real.exp_log (inv_pos.mpr t.property)] at heq
  rw [fzzCigarPositiveDelayDensity,
    fzzCigarParityDelay_eq_fermi t.property] at heq
  have hden : Real.exp (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden] at heq ⊢
  linarith

/-- Undressing also sees exact cancellation of the imaginary net kernel. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedImagNet_eq_zero
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagPositive t) -
        (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagNegative t) = 0 := by
  rw [D.imaginaryPart_eq t, sub_self]

/-- Reciprocal-Fermi-weighted four-part variation of the complex kernel. -/
def FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedVariation
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) : ℝ :=
  (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.realPositive t) +
    (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.realNegative t) +
    (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagPositive t) +
    (∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagNegative t)

/-- Every finite complex implementation pays at least the forced singular local weight. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.forcedWeight_le_undressedVariation
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
          (Real.exp (t : ℝ) + 1) ≤
      D.undressedVariation t := by
  have hnet := D.undressedRealNet_eq t
  have hrneg : 0 ≤
      ∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.realNegative t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityLogUndressingDensity]
    positivity
  have hipos : 0 ≤
      ∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagPositive t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityLogUndressingDensity]
    positivity
  have hineg : 0 ≤
      ∫ x : ℝ, fzzCigarParityLogUndressingDensity x ∂D.imagNegative t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityLogUndressingDensity]
    positivity
  rw [FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedVariation]
  linarith

theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedVariation_nonneg
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    0 ≤ D.undressedVariation t := by
  have hforced := D.forcedWeight_le_undressedVariation t
  have hweight : 0 <
      (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
        (Real.exp (t : ℝ) + 1) := by
    exact div_pos
      (mul_pos (inv_pos.mpr t.property) (by positivity)) (by positivity)
  exact hweight.le.trans hforced

/-- Complex-kernel variation on the reciprocal-depth ultraviolet ray. -/
def FZZCigarParityComplexCharacterNonlocalFEReflectionData.uvUndressedVariation
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData) (n : ℕ) : ℝ :=
  D.undressedVariation (fzzCigarParityPositiveNonlocalUVDelay n)

theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.forcedLocal_uvWeight_le
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData) (n : ℕ) :
    fzzCigarParityForcedLocalFEReflectionData.uvWeight n ≤
      D.uvUndressedVariation n := by
  rw [fzzCigarParityForcedLocalFEReflectionData.uvWeight_eq]
  simpa only [FZZCigarParityComplexCharacterNonlocalFEReflectionData.uvUndressedVariation,
    fzzCigarParityPositiveNonlocalUVDelay, Subtype.coe_mk, inv_inv] using
      D.forcedWeight_le_undressedVariation
        (fzzCigarParityPositiveNonlocalUVDelay n)

/-- Polynomial tempering of finite complex transport means polynomial reciprocal-Fermi-weighted
four-part variation on the ultraviolet ray. -/
def FZZCigarParityComplexCharacterNonlocalFEReflectionData.PolynomiallyTempered
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData) : Prop :=
  ∃ K : ℕ, D.uvUndressedVariation =O[atTop]
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K)

/-- Full complex Mellin covariance forces the same beyond-polynomial singularity as local
reflection. -/
theorem FZZCigarParityComplexCharacterNonlocalFEReflectionData.not_polynomiallyTempered
    (D : FZZCigarParityComplexCharacterNonlocalFEReflectionData) :
    ¬ D.PolynomiallyTempered := by
  rintro ⟨K, hK⟩
  have hdom : fzzCigarParityForcedLocalFEReflectionData.uvWeight =O[atTop]
      D.uvUndressedVariation := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Eventually.of_forall fun n => ?_⟩
    have huvnonneg : 0 ≤ D.uvUndressedVariation n := by
      exact D.undressedVariation_nonneg
        (fzzCigarParityPositiveNonlocalUVDelay n)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (fzzCigarParityForcedLocalFEReflectionData.uvWeight_pos n),
      abs_of_nonneg huvnonneg]
    simpa only [one_mul] using D.forcedLocal_uvWeight_le n
  have hforced : fzzCigarParityForcedLocalFEReflectionData.PolynomiallyTempered :=
    ⟨K, hdom.trans hK⟩
  exact fzzCigarParityForcedLocalFEReflectionData.not_polynomiallyTempered hforced

/-- **[FZZ-P FINITE-COMPLEX ROUTE KILL].**  No polynomially tempered finite-variation complex
nonlocal kernel can implement every imaginary-order Mellin reflection character of the literal
FZZ parity source. -/
theorem no_polynomiallyTempered_FZZCigarParityComplexCharacterNonlocalFEReflectionData :
    ¬ ∃ D : FZZCigarParityComplexCharacterNonlocalFEReflectionData,
      D.PolynomiallyTempered := by
  rintro ⟨D, hD⟩
  exact D.not_polynomiallyTempered hD

end

end RHTower
