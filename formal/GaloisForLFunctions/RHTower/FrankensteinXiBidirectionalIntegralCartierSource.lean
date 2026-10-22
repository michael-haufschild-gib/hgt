import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature
import GaloisForLFunctions.HTGeometry.ConstitutiveStrictInversionCartier
import GaloisForLFunctions.RHTower.Deninger.DeningerPrincipalConormal

/-!
# Bidirectional integral Cartier source for retained Xi divisors

This is an integral source class distinct from the rational, `1/6`-normalized Gamma-six Big-Witt
cross-effect.  Its coefficient ring is the literal Laurent ring `ℤ[q,q⁻¹]`, its source ideal is
`I = (q-1)`, and its carrier is the first Cartier conormal `I/I²`.

The forward and inverse orientations are the classes of `q-1` and `q⁻¹-1`.  Strict inversion gives

`(q-1) + (q⁻¹-1) = -(q-1)(q⁻¹-1)`,

so the two orientations annihilate in `I/I²`.  The class is not zero: Cartier evaluation at `q=1`
proves that every positive multiplicity copy of the forward generator survives.  Hence every
retained Xi divisor has an unconditional nonzero, multiplicity-faithful, bidirectional integral
source class.

An exact Gamma character reads the two representatives as `m(exp(a)-1)` and `m(exp(-a)-1)`.
Therefore a coefficient-faithful additive reporter on this integral conormal can exist only when
the nonlinear paired curvature `2(cosh(a)-1)` vanishes.  At a prime clock
`a = log(p) (2 Re rho - 1)`, this is exactly critical-line placement.  Thus one prime is enough:
integral Cartier descent replaces the previous two-prime shared-ghost comparison.

No reporter existence is assumed.  The source class itself is constructed unconditionally; final
classification identifies coefficient-faithful Gamma descent for every Xi divisor with RH.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry
open LaurentPolynomial

noncomputable section

/-- Literal integral Laurent source ring. -/
abbrev DeningerIntegralCartierSourceRing := LaurentPolynomial ℤ

/-- Forward source generator `q - 1`. -/
def deningerIntegralCartierSourceGenerator : DeningerIntegralCartierSourceRing :=
  T 1 - 1

/-- Cartier augmentation ideal `I = (q - 1)`. -/
abbrev DeningerIntegralCartierSourceIdeal : Ideal DeningerIntegralCartierSourceRing :=
  cartierIdeal (k := ℤ)

/-- Integral first conormal `I / I²`. -/
abbrev DeningerIntegralCartierConormal :=
  DeningerIntegralCartierSourceIdeal.Cotangent

/-- Forward orientation in the integral Cartier conormal. -/
def deningerIntegralCartierForwardClass : DeningerIntegralCartierConormal :=
  DeningerIntegralCartierSourceIdeal.toCotangent
    ⟨deningerIntegralCartierSourceGenerator, generator_mem⟩

/-- Inverse orientation in the integral Cartier conormal. -/
def deningerIntegralCartierInverseClass : DeningerIntegralCartierConormal :=
  DeningerIntegralCartierSourceIdeal.toCotangent
    ⟨inversion ℤ deningerIntegralCartierSourceGenerator, inversion_mem_span⟩

theorem deningerIntegralCartierSourceGenerator_ne_zero :
    deningerIntegralCartierSourceGenerator ≠ 0 := by
  intro h
  have hT : (T 1 : DeningerIntegralCartierSourceRing) = 1 :=
    sub_eq_zero.mp h
  have hd := congrArg LaurentPolynomial.degree hT
  have hone : LaurentPolynomial.degree
      (1 : DeningerIntegralCartierSourceRing) = 0 := by
    simpa using (LaurentPolynomial.degree_C (R := ℤ) one_ne_zero)
  have hcontra : (1 : WithBot ℤ) = 0 := by
    calc
      1 = LaurentPolynomial.degree
          (T 1 : DeningerIntegralCartierSourceRing) :=
        (LaurentPolynomial.degree_T (R := ℤ) 1).symm
      _ = LaurentPolynomial.degree (1 : DeningerIntegralCartierSourceRing) := hd
      _ = 0 := hone
  norm_num at hcontra

theorem deningerIntegralCartierSourceGenerator_isRegular :
    IsRegular deningerIntegralCartierSourceGenerator :=
  IsRegular.of_ne_zero deningerIntegralCartierSourceGenerator_ne_zero

/-- The forward integral conormal orientation is genuinely nonzero. -/
theorem deningerIntegralCartierForwardClass_ne_zero :
    deningerIntegralCartierForwardClass ≠ 0 := by
  intro hzero
  rw [deningerIntegralCartierForwardClass, Ideal.toCotangent_eq_zero] at hzero
  have hsq :
      (1 : DeningerIntegralCartierSourceRing) *
          deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal ^ (2 : ℕ) := by
    simpa only [deningerIntegralCartierSourceGenerator, one_mul] using hzero
  have hmem : (1 : DeningerIntegralCartierSourceRing) ∈
      DeningerIntegralCartierSourceIdeal :=
    (deningerConormal_mul_mem_sq_iff deningerIntegralCartierSourceGenerator
      deningerIntegralCartierSourceGenerator_isRegular 1).1 hsq
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc := congrArg (cartier ℤ) ha
  simp at hc

/-- Every positive multiplicity copy of the integral forward class remains nonzero. -/
theorem deningerIntegralCartierMultiplicityForwardClass_ne_zero
    {m : ℕ} (hm : 0 < m) :
    m • deningerIntegralCartierForwardClass ≠ 0 := by
  intro hzero
  rw [deningerIntegralCartierForwardClass, ← map_nsmul,
    Ideal.toCotangent_eq_zero] at hzero
  have hsq :
      (m : DeningerIntegralCartierSourceRing) *
          deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal ^ (2 : ℕ) := by
    simpa [nsmul_eq_mul] using hzero
  have hmem : (m : DeningerIntegralCartierSourceRing) ∈
      DeningerIntegralCartierSourceIdeal :=
    (deningerConormal_mul_mem_sq_iff deningerIntegralCartierSourceGenerator
      deningerIntegralCartierSourceGenerator_isRegular m).1 hsq
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc := congrArg (cartier ℤ) ha
  simp at hc
  have hm0 : m = 0 := by exact_mod_cast hc.symm
  omega

/-- Strict inversion makes the two source orientations annihilate in `I/I²`. -/
theorem deningerIntegralCartierForward_add_inverse :
    deningerIntegralCartierForwardClass + deningerIntegralCartierInverseClass = 0 := by
  rw [deningerIntegralCartierForwardClass, deningerIntegralCartierInverseClass,
    ← map_add, Ideal.toCotangent_eq_zero]
  simpa [deningerIntegralCartierSourceGenerator, add_comm] using
    (inversion_conormal_odd (k := ℤ))

/-- Multiplicity-labelled forward source class. -/
def deningerIntegralCartierMultiplicityForwardClass (m : ℕ) :
    DeningerIntegralCartierConormal :=
  m • deningerIntegralCartierForwardClass

/-- Multiplicity-labelled inverse source class. -/
def deningerIntegralCartierMultiplicityInverseClass (m : ℕ) :
    DeningerIntegralCartierConormal :=
  m • deningerIntegralCartierInverseClass

/-- Multiplicity preserves exact bidirectional annihilation. -/
theorem deningerIntegralCartierMultiplicity_annihilate (m : ℕ) :
    deningerIntegralCartierMultiplicityForwardClass m +
        deningerIntegralCartierMultiplicityInverseClass m = 0 := by
  rw [deningerIntegralCartierMultiplicityForwardClass,
    deningerIntegralCartierMultiplicityInverseClass, ← smul_add,
    deningerIntegralCartierForward_add_inverse, smul_zero]

/-- Nonzero bidirectional integral source class attached to an actual retained Xi divisor. -/
structure DeningerXiBidirectionalIntegralSourceClass
    (rho : XiDivisorSupport) where
  forward : DeningerIntegralCartierConormal
  inverse : DeningerIntegralCartierConormal
  forward_eq :
    forward = deningerIntegralCartierMultiplicityForwardClass
      (xiSupportMultiplicity rho)
  inverse_eq :
    inverse = deningerIntegralCartierMultiplicityInverseClass
      (xiSupportMultiplicity rho)
  forward_ne_zero : forward ≠ 0
  annihilate : forward + inverse = 0

/-- Every retained Xi divisor unconditionally carries the new integral source class. -/
def deningerXiBidirectionalIntegralSourceClass
    (rho : XiDivisorSupport) :
    DeningerXiBidirectionalIntegralSourceClass rho where
  forward := deningerIntegralCartierMultiplicityForwardClass
    (xiSupportMultiplicity rho)
  inverse := deningerIntegralCartierMultiplicityInverseClass
    (xiSupportMultiplicity rho)
  forward_eq := rfl
  inverse_eq := rfl
  forward_ne_zero :=
    deningerIntegralCartierMultiplicityForwardClass_ne_zero
      (xiSupportMultiplicity_pos rho)
  annihilate := deningerIntegralCartierMultiplicity_annihilate _

/-- Coefficient-faithful Gamma descent of both prime-labelled orientations through the same
integral source conormal.  No shared fitted scalar or prime-local countercharacter is stored. -/
structure DeningerXiBidirectionalIntegralGammaReporter
    (rho : XiDivisorSupport) (p : Nat.Primes) where
  source : DeningerXiBidirectionalIntegralSourceClass rho
  reporter : DeningerIntegralCartierConormal →+ ℝ
  forward_coefficient :
    reporter source.forward =
      (xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitForwardBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)
  inverse_coefficient :
    reporter source.inverse =
      (xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)

/-- Integral source annihilation forces exact cancellation of the two nonlinear Gamma defects. -/
theorem deningerXiBidirectionalIntegralGammaReporter_defects_annihilate
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiBidirectionalIntegralGammaReporter rho p) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) +
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) = 0 := by
  have hzero := congrArg h.reporter h.source.annihilate
  rw [map_add, map_zero, h.forward_coefficient, h.inverse_coefficient] at hzero
  have hm : (xiSupportMultiplicity rho : ℝ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  apply (mul_eq_zero.mp ?_).resolve_left hm
  linear_combination hzero

/-- Equivalently, integral descent kills the exact paired Gamma curvature. -/
theorem deningerXiBidirectionalIntegralGammaReporter_curvature_eq_zero
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiBidirectionalIntegralGammaReporter rho p) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
      (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) = 0 := by
  rw [← sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_curvature]
  exact deningerXiBidirectionalIntegralGammaReporter_defects_annihilate h

/-- A coefficient-faithful reporter at one retained prime forces the critical line. -/
theorem deningerXiBidirectionalIntegralGammaReporter_line
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiBidirectionalIntegralGammaReporter rho p) :
    (rho : ℂ).re = 1 / 2 := by
  exact (sourceHorizontalGammaSixPrimePhysicalBoundaryDefects_add_eq_zero_iff
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ p).1
      (deningerXiBidirectionalIntegralGammaReporter_defects_annihilate h)

/-- On the critical line, zero readout is the coefficient-faithful integral reporter. -/
def deningerXiBidirectionalIntegralGammaReporterOfLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hline : (rho : ℂ).re = 1 / 2) :
    DeningerXiBidirectionalIntegralGammaReporter rho p where
  source := deningerXiBidirectionalIntegralSourceClass rho
  reporter := 0
  forward_coefficient := by
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hline, mul_zero]
    simp [sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq]
  inverse_coefficient := by
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hline, mul_zero]
    simp [sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- Exact pointwise classification: one-prime integral conormal descent is critical-line
placement. -/
theorem deningerXiBidirectionalIntegralGammaReporter_nonempty_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨h⟩
    exact deningerXiBidirectionalIntegralGammaReporter_line h
  · intro h
    exact ⟨deningerXiBidirectionalIntegralGammaReporterOfLine rho p h⟩

/-- Global producer target over every retained Xi divisor and every retained prime label. -/
def EveryXiBidirectionalIntegralGammaReporterDescends : Prop :=
  ∀ (rho : XiDivisorSupport) (p : Nat.Primes),
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p)

/-- Full endpoint: constructing coefficient-faithful integral reporters on the unconditional source
classes is exactly RH. -/
theorem everyXiBidirectionalIntegralGammaReporterDescends_iff_riemannHypothesis :
    EveryXiBidirectionalIntegralGammaReporterDescends ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (deningerXiBidirectionalIntegralGammaReporter_nonempty_iff
      rho (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
        (h rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro h rho p
    exact (deningerXiBidirectionalIntegralGammaReporter_nonempty_iff rho p).2
      (xi_divisor_support_re_eq_half_of_rh h rho)

end

end RHTower
