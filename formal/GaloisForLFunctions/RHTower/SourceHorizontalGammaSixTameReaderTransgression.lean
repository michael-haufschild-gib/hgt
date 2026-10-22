import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding
import GaloisForLFunctions.RHTower.SourceHorizontalShellGreenPrimeClockProfile
import GaloisForLFunctions.RHTower.Deninger.DeningerExponentExceptionalTameGreenBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerCyclicHomology

/-!
# Gamma-six tame-reader transgression of the source-horizontal shell profile

This file identifies the finite Gamma-six shell/Wold response with a harmonic transgression of
the already constructed marked exceptional tame readers.  The identity is pre-divisor and keeps
every shell grade and both marked Gamma orientations.  Its horizon is twice the universal Wold
prime-clock profile.

The second part audits specialization to the first nonzero Xi jet.  A raw leading coefficient
introduces an exact multiplicity-parity wall: reflected equality is automatic at every odd-order
zero.  Pairing the two nonzero orientation coefficients removes that blindness and gives a
coefficient-faithful RH receiver.  No theorem here asserts that the orbit-paired response descends
to the reflection quotient; that source descent remains the producer.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## Leading-jet parity wall -/

/-- Raw multiplicity-leading Xi coefficient multiplying the complete source-horizontal response. -/
def sourceHorizontalLeadingXiJetPrimeClockResponse
    (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho *
    (sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate rho) : ℂ)

/-- Functional-equation reflection acts on the weighted response by jet parity shifted once by
the odd horizontal profile. -/
theorem sourceHorizontalLeadingXiJetPrimeClockResponse_reflection
    (rho : XiDivisorSupport) :
    sourceHorizontalLeadingXiJetPrimeClockResponse (xiZeroReflectEquiv rho) =
      -((-1 : ℂ) ^ xiSupportMultiplicity rho) *
        sourceHorizontalLeadingXiJetPrimeClockResponse rho := by
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroReflectEquiv rho) =
        -primeDepthBVWoldXiCenteredRate rho := by
    rw [primeDepthBVWoldXiCenteredRate,
      primeDepthBVWoldXiCenteredRate, xiZeroReflectEquiv_apply]
    simp
    ring
  rw [sourceHorizontalLeadingXiJetPrimeClockResponse,
    sourceHorizontalLeadingXiJetPrimeClockResponse,
    ccmRationalAdelicPrimeXiCartierCoefficient_reflection,
    hrate, sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  push_cast
  ring

theorem sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_of_even
    (rho : XiDivisorSupport) (h : Even (xiSupportMultiplicity rho)) :
    sourceHorizontalLeadingXiJetPrimeClockResponse (xiZeroReflectEquiv rho) =
      -sourceHorizontalLeadingXiJetPrimeClockResponse rho := by
  rw [sourceHorizontalLeadingXiJetPrimeClockResponse_reflection, h.neg_one_pow]
  ring

theorem sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_of_odd
    (rho : XiDivisorSupport) (h : Odd (xiSupportMultiplicity rho)) :
    sourceHorizontalLeadingXiJetPrimeClockResponse (xiZeroReflectEquiv rho) =
      sourceHorizontalLeadingXiJetPrimeClockResponse rho := by
  rw [sourceHorizontalLeadingXiJetPrimeClockResponse_reflection, h.neg_one_pow]
  ring

theorem sourceHorizontalLeadingXiJetPrimeClockResponse_eq_zero_iff
    (rho : XiDivisorSupport) :
    sourceHorizontalLeadingXiJetPrimeClockResponse rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalLeadingXiJetPrimeClockResponse, mul_eq_zero]
  simp only [ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero, false_or]
  rw [Complex.ofReal_eq_zero,
    sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

theorem sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_eq_iff_of_even
    (rho : XiDivisorSupport) (h : Even (xiSupportMultiplicity rho)) :
    sourceHorizontalLeadingXiJetPrimeClockResponse (xiZeroReflectEquiv rho) =
        sourceHorizontalLeadingXiJetPrimeClockResponse rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_of_even rho h]
  constructor
  · intro heq
    apply (sourceHorizontalLeadingXiJetPrimeClockResponse_eq_zero_iff rho).1
    have htwice :
        sourceHorizontalLeadingXiJetPrimeClockResponse rho +
            sourceHorizontalLeadingXiJetPrimeClockResponse rho = 0 := by
      have hadd := congrArg
        (fun z : ℂ => z + sourceHorizontalLeadingXiJetPrimeClockResponse rho) heq
      simpa using hadd.symm
    calc
      sourceHorizontalLeadingXiJetPrimeClockResponse rho =
          (1 / 2 : ℂ) *
            (sourceHorizontalLeadingXiJetPrimeClockResponse rho +
              sourceHorizontalLeadingXiJetPrimeClockResponse rho) := by ring
      _ = 0 := by rw [htwice]; simp
  · intro hline
    have hz :=
      (sourceHorizontalLeadingXiJetPrimeClockResponse_eq_zero_iff rho).2 hline
    rw [hz]
    simp

/-- Exact no-go classification.  Raw coefficient-weighted reflected equality detects the line at
even multiplicity but is automatic at odd multiplicity. -/
theorem sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_eq_iff
    (rho : XiDivisorSupport) :
    sourceHorizontalLeadingXiJetPrimeClockResponse (xiZeroReflectEquiv rho) =
        sourceHorizontalLeadingXiJetPrimeClockResponse rho ↔
      Odd (xiSupportMultiplicity rho) ∨ (rho : ℂ).re = 1 / 2 := by
  rcases Nat.even_or_odd (xiSupportMultiplicity rho) with h | h
  · rw [sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_eq_iff_of_even rho h]
    constructor
    · exact Or.inr
    · intro hor
      exact hor.resolve_left (Nat.not_odd_iff_even.mpr h)
  · constructor
    · intro _
      exact Or.inl h
    · intro _
      exact sourceHorizontalLeadingXiJetPrimeClockResponse_reflection_of_odd rho h

/-! ## Two-orientation coefficient pairing -/

/-- Product of both functional-equation orientation coefficients.  Neither nonzero leading jet is
divided out. -/
def sourceHorizontalGammaSixXiReflectionOrbitCoefficient
    (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho *
    ccmRationalAdelicPrimeXiCartierCoefficient (xiZeroReflectEquiv rho)

theorem sourceHorizontalGammaSixXiReflectionOrbitCoefficient_ne_zero
    (rho : XiDivisorSupport) :
    sourceHorizontalGammaSixXiReflectionOrbitCoefficient rho ≠ 0 :=
  mul_ne_zero
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero
      (xiZeroReflectEquiv rho))

/-- The two-orientation coefficient product is independent of the ordering of its orbit. -/
theorem sourceHorizontalGammaSixXiReflectionOrbitCoefficient_reflection
    (rho : XiDivisorSupport) :
    sourceHorizontalGammaSixXiReflectionOrbitCoefficient (xiZeroReflectEquiv rho) =
      sourceHorizontalGammaSixXiReflectionOrbitCoefficient rho := by
  have hinv : xiZeroReflectEquiv (xiZeroReflectEquiv rho) = rho := by
    apply Subtype.ext
    simp
  rw [sourceHorizontalGammaSixXiReflectionOrbitCoefficient,
    sourceHorizontalGammaSixXiReflectionOrbitCoefficient, hinv]
  ring

/-- Both nonzero leading Xi coefficients paired with the odd shell horizon. -/
def sourceHorizontalGammaSixXiReflectionOrbitResponse
    (rho : XiDivisorSupport) : ℂ :=
  sourceHorizontalGammaSixXiReflectionOrbitCoefficient rho *
    (sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate rho) : ℂ)

/-- Pairing both coefficients removes multiplicity parity: reflection always reverses the orbit
response. -/
theorem sourceHorizontalGammaSixXiReflectionOrbitResponse_reflection
    (rho : XiDivisorSupport) :
    sourceHorizontalGammaSixXiReflectionOrbitResponse (xiZeroReflectEquiv rho) =
      -sourceHorizontalGammaSixXiReflectionOrbitResponse rho := by
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroReflectEquiv rho) =
        -primeDepthBVWoldXiCenteredRate rho := by
    rw [primeDepthBVWoldXiCenteredRate,
      primeDepthBVWoldXiCenteredRate, xiZeroReflectEquiv_apply]
    simp
    ring
  rw [sourceHorizontalGammaSixXiReflectionOrbitResponse,
    sourceHorizontalGammaSixXiReflectionOrbitResponse,
    sourceHorizontalGammaSixXiReflectionOrbitCoefficient_reflection,
    hrate, sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  push_cast
  ring

theorem sourceHorizontalGammaSixXiReflectionOrbitResponse_eq_zero_iff
    (rho : XiDivisorSupport) :
    sourceHorizontalGammaSixXiReflectionOrbitResponse rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixXiReflectionOrbitResponse, mul_eq_zero]
  simp only [sourceHorizontalGammaSixXiReflectionOrbitCoefficient_ne_zero, false_or]
  rw [Complex.ofReal_eq_zero,
    sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Coefficient-faithful two-orientation receiver.  Identifying its two reflection transports is
pointwise equivalent to critical-line placement, independently of zero multiplicity parity. -/
theorem sourceHorizontalGammaSixXiReflectionOrbitResponse_reflection_eq_iff
    (rho : XiDivisorSupport) :
    sourceHorizontalGammaSixXiReflectionOrbitResponse (xiZeroReflectEquiv rho) =
        sourceHorizontalGammaSixXiReflectionOrbitResponse rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixXiReflectionOrbitResponse_reflection]
  constructor
  · intro heq
    apply (sourceHorizontalGammaSixXiReflectionOrbitResponse_eq_zero_iff rho).1
    have htwice :
        sourceHorizontalGammaSixXiReflectionOrbitResponse rho +
            sourceHorizontalGammaSixXiReflectionOrbitResponse rho = 0 := by
      have hadd := congrArg
        (fun z : ℂ => z + sourceHorizontalGammaSixXiReflectionOrbitResponse rho) heq
      simpa using hadd.symm
    calc
      sourceHorizontalGammaSixXiReflectionOrbitResponse rho =
          (1 / 2 : ℂ) *
            (sourceHorizontalGammaSixXiReflectionOrbitResponse rho +
              sourceHorizontalGammaSixXiReflectionOrbitResponse rho) := by ring
      _ = 0 := by rw [htwice]; simp
  · intro hline
    have hz :=
      (sourceHorizontalGammaSixXiReflectionOrbitResponse_eq_zero_iff rho).2 hline
    rw [hz]
    simp

/-! ## Exact marked-tame transgression -/

/-- Cofinal real spectral fibre whose grade-`m` Gamma-six character has normalized argument
`u*m/N`. -/
def sourceHorizontalGammaSixCofinalSpectralPoint (N : ℕ) (u : ℝ) : ℂ :=
  (((1 + u / ((N : ℝ) * Real.log 6)) / 2 : ℝ) : ℂ)

@[simp] theorem sourceHorizontalGammaSixCofinalSpectralPoint_re
    (N : ℕ) (u : ℝ) :
    (sourceHorizontalGammaSixCofinalSpectralPoint N u).re =
      (1 + u / ((N : ℝ) * Real.log 6)) / 2 := by
  rfl

/-- The existing exceptional tame reader on the cofinal fibre is exactly the hyperbolic shell
character at normalized grade `m/N`. -/
theorem sourceHorizontalGammaSixExceptionalTameReader_cofinal_eq_sinh
    {N : ℕ} (hN : 0 < N) (m : ℕ) (u : ℝ) :
    deningerGammaSixExceptionalTameReader m
        (sourceHorizontalGammaSixCofinalSpectralPoint N u) =
      2 * Real.sinh (u * (m : ℝ) / N) := by
  rw [deningerGammaSixExceptionalTameReader_eq_mateCurvature,
    deningerTensorSquareRadialMateCurvature_eq_sinh]
  · congr 2
    rw [sourceHorizontalGammaSixCofinalSpectralPoint_re]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hlog6 : Real.log (6 : ℝ) ≠ 0 :=
      (Real.log_pos (by norm_num)).ne'
    rw [show Real.log ((6 ^ m : ℕ) : ℝ) =
        (m : ℝ) * Real.log 6 by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num]
    field_simp [hN0, hlog6]
    ring
  · positivity

/-- Harmonic Gamma-six shell transgression of all marked exceptional tame grades up to `N`. -/
def sourceHorizontalGammaSixExceptionalTameReaderTransgression
    (N : ℕ) (u : ℝ) : ℝ :=
  (1 / (N : ℝ)) *
      ∑ j ∈ Finset.range N,
        (sourceHorizontalGammaSixShellClock N j)⁻¹ *
          deningerGammaSixExceptionalTameReader (N - j)
            (sourceHorizontalGammaSixCofinalSpectralPoint N u) -
    deningerGammaSixExceptionalTameReader N
      (sourceHorizontalGammaSixCofinalSpectralPoint N u)

/-- Exact finite Frankenstein junction.  The complete Gamma-six Green shell response is half the
harmonic transgression of the actual marked tame/Gamma/Calderon readers. -/
theorem sourceHorizontalGammaSixShellProfile_eq_tameReaderTransgression
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u =
      sourceHorizontalGammaSixExceptionalTameReaderTransgression N u := by
  rw [sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_finiteTrace hN]
  rw [sourceHorizontalGammaSixExceptionalTameReaderTransgression,
    sourceHorizontalGammaSixExceptionalTameReader_cofinal_eq_sinh hN N u]
  have hNN : u * (N : ℝ) / N = u := by
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
  rw [hNN]
  simp_rw [sourceHorizontalGammaSixExceptionalTameReader_cofinal_eq_sinh hN]
  have hclock : ∀ j ∈ Finset.range N,
      u * ((N - j : ℕ) : ℝ) / N =
        u * sourceHorizontalGammaSixShellClock N j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [sourceHorizontalGammaSixShellClock, Nat.cast_sub (Nat.le_of_lt hj)]
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
  have hsum :
      (∑ j ∈ Finset.range N,
          (sourceHorizontalGammaSixShellClock N j)⁻¹ *
            (2 * Real.sinh (u * ((N - j : ℕ) : ℝ) / N))) =
        2 * ∑ j ∈ Finset.range N,
          (sourceHorizontalGammaSixShellClock N j)⁻¹ *
            Real.sinh (u * sourceHorizontalGammaSixShellClock N j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hclock j hj]
    ring
  rw [hsum]
  ring

/-- The marked tame transgression has the complete Wold prime-clock horizon. -/
theorem tendsto_sourceHorizontalGammaSixExceptionalTameReaderTransgression
    (u : ℝ) :
    Tendsto
      (fun N : ℕ =>
        sourceHorizontalGammaSixExceptionalTameReaderTransgression N u)
      atTop (nhds (2 * sourceHorizontalWoldPrimeClockUniversalProfile u)) := by
  have hEq :
      (fun N : ℕ =>
          sourceHorizontalGammaSixExceptionalTameReaderTransgression N u) =ᶠ[atTop]
        (fun N : ℕ =>
          2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (sourceHorizontalGammaSixShellProfile_eq_tameReaderTransgression hN u).symm
  exact (tendsto_const_nhds.mul
    (tendsto_sourceHorizontalGammaSixShellPrimeClockProfileSeries u)).congr' hEq.symm

/-! ## Pre-divisor regulator-kernel class -/

/-- Finite real group algebra of the marked Gamma-six exponent lattice. -/
abbrev SourceHorizontalGammaSixExponentCarrier := ℤ →₀ ℝ

/-- Ordered pair of the two retained exponent orientations at shell grade `m`. -/
def sourceHorizontalGammaSixOrientedExponentAtom
    (m : ℕ) : SourceHorizontalGammaSixExponentCarrier :=
  Finsupp.single (m : ℤ) 1 - Finsupp.single (-(m : ℤ)) 1

/-- Linear Kummer exponent moment.  Multiplication by `log 6` gives the Gamma-six Kummer
regulator. -/
def sourceHorizontalGammaSixKummerExponentMoment :
    SourceHorizontalGammaSixExponentCarrier →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun k => (k : ℝ) • LinearMap.id

@[simp] theorem sourceHorizontalGammaSixKummerExponentMoment_atom
    (m : ℕ) :
    sourceHorizontalGammaSixKummerExponentMoment
        (sourceHorizontalGammaSixOrientedExponentAtom m) =
      2 * m := by
  rw [sourceHorizontalGammaSixOrientedExponentAtom, map_sub,
    sourceHorizontalGammaSixKummerExponentMoment,
    Finsupp.lsum_single, Finsupp.lsum_single]
  simp
  ring

/-- Nonlinear horizontal-character readout of the exponent carrier. -/
def sourceHorizontalGammaSixExponentCharacterReadout (a : ℝ) :
    SourceHorizontalGammaSixExponentCarrier →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun k => Real.exp (a * (k : ℝ)) • LinearMap.id

@[simp] theorem sourceHorizontalGammaSixExponentCharacterReadout_atom
    (a : ℝ) (m : ℕ) :
    sourceHorizontalGammaSixExponentCharacterReadout a
        (sourceHorizontalGammaSixOrientedExponentAtom m) =
      2 * Real.sinh (a * m) := by
  rw [sourceHorizontalGammaSixOrientedExponentAtom, map_sub,
    sourceHorizontalGammaSixExponentCharacterReadout,
    Finsupp.lsum_single, Finsupp.lsum_single]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    Real.sinh_eq, Int.cast_neg, Int.cast_natCast]
  ring

/-- Concrete finite source relation: harmonic average of all retained marked shell orientations
minus the terminal orientation pair. -/
def sourceHorizontalGammaSixHarmonicBoundaryClass
    (N : ℕ) : SourceHorizontalGammaSixExponentCarrier :=
  (1 / (N : ℝ)) •
      ∑ j ∈ Finset.range N,
        (sourceHorizontalGammaSixShellClock N j)⁻¹ •
          sourceHorizontalGammaSixOrientedExponentAtom (N - j) -
    sourceHorizontalGammaSixOrientedExponentAtom N

/-- The harmonic shell class is unconditionally Kummer-regulator null before any horizontal
character or Xi divisor is chosen. -/
theorem sourceHorizontalGammaSixKummerExponentMoment_harmonicBoundaryClass
    {N : ℕ} (hN : 0 < N) :
    sourceHorizontalGammaSixKummerExponentMoment
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) = 0 := by
  rw [sourceHorizontalGammaSixHarmonicBoundaryClass, map_sub, map_smul, map_sum]
  simp_rw [map_smul, sourceHorizontalGammaSixKummerExponentMoment_atom]
  have hterm : ∀ j ∈ Finset.range N,
      (1 / (N : ℝ)) *
          ((sourceHorizontalGammaSixShellClock N j)⁻¹ *
            (2 * (N - j : ℕ))) = 2 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [sourceHorizontalGammaSixShellClock, Nat.cast_sub (Nat.le_of_lt hj)]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hdiff : (N : ℝ) - j ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hj)
    field_simp [hN0, hdiff]
  calc
    (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N,
            (sourceHorizontalGammaSixShellClock N j)⁻¹ * (2 * ↑(N - j)) -
        2 * ↑N =
      ∑ j ∈ Finset.range N,
        (1 / (N : ℝ)) *
          ((sourceHorizontalGammaSixShellClock N j)⁻¹ * (2 * ↑(N - j))) -
        2 * ↑N := by rw [Finset.mul_sum]
    _ = ∑ _j ∈ Finset.range N, (2 : ℝ) - 2 * N := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j hj
    _ = 0 := by simp; ring

/-- Nonlinear horizontal evaluation of the regulator-kernel source class is the explicit
hyperbolic shell transgression. -/
theorem sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass
    {N : ℕ} (_hN : 0 < N) (u : ℝ) :
    sourceHorizontalGammaSixExponentCharacterReadout (u / N)
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) =
      (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N,
            (sourceHorizontalGammaSixShellClock N j)⁻¹ *
              (2 * Real.sinh (u * ((N - j : ℕ) : ℝ) / N)) -
        2 * Real.sinh (u * (N : ℝ) / N) := by
  rw [sourceHorizontalGammaSixHarmonicBoundaryClass, map_sub, map_smul, map_sum]
  simp_rw [map_smul, sourceHorizontalGammaSixExponentCharacterReadout_atom]
  simp only [smul_eq_mul]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · ring

/-- Exact source interpretation of the Frankenstein seam: a class already killed by the linear
Kummer regulator is sent by nonlinear character evaluation to the full marked-tame shell anomaly. -/
theorem sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_eq_tame
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    sourceHorizontalGammaSixExponentCharacterReadout (u / N)
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) =
      sourceHorizontalGammaSixExceptionalTameReaderTransgression N u := by
  rw [sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass hN u,
    sourceHorizontalGammaSixExceptionalTameReaderTransgression]
  simp_rw [sourceHorizontalGammaSixExceptionalTameReader_cofinal_eq_sinh hN]

/-- Consequently nonlinear evaluation of the regulator-null source class is exactly twice the
finite Gamma-six Green/Wold shell profile. -/
theorem sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_eq_profile
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    sourceHorizontalGammaSixExponentCharacterReadout (u / N)
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) =
      2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u := by
  rw [sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_eq_tame hN u,
    ← sourceHorizontalGammaSixShellProfile_eq_tameReaderTransgression hN u]

/-- The regulator kernel is strictly larger than the kernel of nonlinear character evaluation:
already the two-shell class has a negative readout at every positive horizontal character. -/
theorem sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_two_neg
    {u : ℝ} (hu : 0 < u) :
    sourceHorizontalGammaSixExponentCharacterReadout (u / (2 : ℕ))
        (sourceHorizontalGammaSixHarmonicBoundaryClass 2) < 0 := by
  rw [sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass
    (N := 2) (by norm_num) u]
  norm_num [sourceHorizontalGammaSixShellClock, Finset.sum_range_succ]
  have hsinh : 0 < Real.sinh (u / 2) :=
    Real.sinh_pos_iff.mpr (by linarith)
  have hcosh0 : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have hcosh1 : 1 < Real.cosh (u / 2) := by
    nlinarith [Real.cosh_sq (u / 2)]
  have hdouble :
      Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    convert Real.sinh_two_mul (u / 2) using 1 <;> ring
  rw [hdouble]
  nlinarith

/-- Thus a concrete nonzero source class survives inside the linear Kummer-regulator kernel. -/
theorem sourceHorizontalGammaSixHarmonicBoundaryClass_two_ne_zero :
    sourceHorizontalGammaSixHarmonicBoundaryClass 2 ≠ 0 := by
  intro hzero
  have hneg :=
    sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_two_neg
      (u := 1) zero_lt_one
  rw [hzero, map_zero] at hneg
  exact (lt_irrefl 0) hneg

/-! ## Existing Deninger cyclic resolution realizes the source class -/

/-- Multiplicative presentation of the Gamma-six exponent lattice. -/
abbrev SourceHorizontalGammaSixCyclicGroup := Multiplicative ℤ

/-- Canonical identification with the infinite cyclic group used by Deninger's resolution. -/
def sourceHorizontalGammaSixCyclicGroupEquiv :
    SourceHorizontalGammaSixCyclicGroup ≃* Multiplicative ℤ :=
  MulEquiv.refl SourceHorizontalGammaSixCyclicGroup

/-- Group-algebra presentation of the two marked exponent orientations. -/
def sourceHorizontalGammaSixCyclicGroupAtom
    (m : ℕ) : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  MonoidAlgebra.single (Multiplicative.ofAdd (m : ℤ)) 1 -
    MonoidAlgebra.single (Multiplicative.ofAdd (-(m : ℤ))) 1

/-- Its coefficient column is exactly the previously defined oriented exponent atom. -/
theorem sourceHorizontalGammaSixCyclicGroupAtom_coeff
    (m : ℕ) :
    MonoidAlgebra.coeffLinearEquiv ℝ
        (sourceHorizontalGammaSixCyclicGroupAtom m) =
      Finsupp.domLCongr (M := ℝ) (R := ℝ)
        (Multiplicative.ofAdd : ℤ ≃ SourceHorizontalGammaSixCyclicGroup)
        (sourceHorizontalGammaSixOrientedExponentAtom m) := by
  rw [sourceHorizontalGammaSixCyclicGroupAtom,
    sourceHorizontalGammaSixOrientedExponentAtom, map_sub, map_sub,
    Finsupp.domLCongr_single, Finsupp.domLCongr_single]
  rfl

/-- The oriented atom is already a genuine `t - 1` boundary in Deninger's infinite-cyclic
resolution. -/
theorem sourceHorizontalGammaSixCyclicGroupAtom_mem_boundaryRange
    (m : ℕ) :
    sourceHorizontalGammaSixCyclicGroupAtom m ∈
      LinearMap.range
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap := by
  have hp := deningerZ_pow_sub_one
    sourceHorizontalGammaSixCyclicGroupEquiv ℝ (m : ℤ)
  have hn := deningerZ_pow_sub_one
    sourceHorizontalGammaSixCyclicGroupEquiv ℝ (-(m : ℤ))
  have h := Submodule.sub_mem _ hp hn
  convert h using 1
  simp [sourceHorizontalGammaSixCyclicGroupAtom,
    sourceHorizontalGammaSixCyclicGroupEquiv, deningerZPow]

/-- Group-algebra lift of the harmonic shell relation. -/
def sourceHorizontalGammaSixCyclicHarmonicBoundaryClass
    (N : ℕ) : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  (1 / (N : ℝ)) •
      ∑ j ∈ Finset.range N,
        (sourceHorizontalGammaSixShellClock N j)⁻¹ •
          sourceHorizontalGammaSixCyclicGroupAtom (N - j) -
    sourceHorizontalGammaSixCyclicGroupAtom N

/-- The cyclic group-algebra lift has exactly the coefficient column whose nonlinear evaluation
was proved to be the finite shell profile. -/
theorem sourceHorizontalGammaSixCyclicHarmonicBoundaryClass_coeff
    (N : ℕ) :
    MonoidAlgebra.coeffLinearEquiv ℝ
        (sourceHorizontalGammaSixCyclicHarmonicBoundaryClass N) =
      Finsupp.domLCongr (M := ℝ) (R := ℝ)
        (Multiplicative.ofAdd : ℤ ≃ SourceHorizontalGammaSixCyclicGroup)
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) := by
  rw [sourceHorizontalGammaSixCyclicHarmonicBoundaryClass,
    sourceHorizontalGammaSixHarmonicBoundaryClass]
  simp only [map_sub, map_smul, map_sum]
  simp_rw [sourceHorizontalGammaSixCyclicGroupAtom_coeff]

/-- **Source boundary theorem.** The complete finite harmonic marked-shell class is not merely
regulator-null: it lies in the image of the literal `t - 1` differential of the existing Deninger
infinite-cyclic resolution. -/
theorem sourceHorizontalGammaSixCyclicHarmonicBoundaryClass_mem_boundaryRange
    (N : ℕ) :
    sourceHorizontalGammaSixCyclicHarmonicBoundaryClass N ∈
      LinearMap.range
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap := by
  rw [sourceHorizontalGammaSixCyclicHarmonicBoundaryClass]
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (sourceHorizontalGammaSixCyclicGroupAtom_mem_boundaryRange (N - j))
  · exact sourceHorizontalGammaSixCyclicGroupAtom_mem_boundaryRange N

/-- Equivalent primitive form of the source boundary theorem. -/
theorem exists_sourceHorizontalGammaSixCyclicHarmonicBoundaryPrimitive
    (N : ℕ) :
    ∃ primitive : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup,
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom primitive =
        sourceHorizontalGammaSixCyclicHarmonicBoundaryClass N := by
  exact LinearMap.mem_range.mp
    (sourceHorizontalGammaSixCyclicHarmonicBoundaryClass_mem_boundaryRange N)

/-! ## Physical-character descent anomaly -/

/-- Physical horizontal character on the actual Deninger cyclic group algebra. -/
def sourceHorizontalGammaSixCyclicCharacterReadout (a : ℝ) :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup →ₗ[ℝ] ℝ :=
  (Finsupp.lsum ℝ fun k =>
    Real.exp (a * ((Multiplicative.toAdd k : ℤ) : ℝ)) • LinearMap.id).comp
      (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem sourceHorizontalGammaSixCyclicCharacterReadout_single
    (a : ℝ) (k : SourceHorizontalGammaSixCyclicGroup) (c : ℝ) :
    sourceHorizontalGammaSixCyclicCharacterReadout a (MonoidAlgebra.single k c) =
      Real.exp (a * ((Multiplicative.toAdd k : ℤ) : ℝ)) * c := by
  rw [sourceHorizontalGammaSixCyclicCharacterReadout, LinearMap.comp_apply]
  change (Finsupp.lsum ℝ fun k : SourceHorizontalGammaSixCyclicGroup =>
    Real.exp (a * ((Multiplicative.toAdd k : ℤ) : ℝ)) • LinearMap.id)
      (Finsupp.single k c) = _
  rw [Finsupp.lsum_single]
  simp [smul_eq_mul]

/-- Exact Beck--Chevalley defect: applying a physical character after the source differential
multiplies its input readout by `exp a - 1`.  Thus character specialization does not descend
through the source boundary away from the neutral horizontal grade. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_boundary
    (a : ℝ) (f : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
        ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom f) =
      (Real.exp a - 1) * sourceHorizontalGammaSixCyclicCharacterReadout a f := by
  refine MonoidAlgebra.induction_on (p := fun f =>
    sourceHorizontalGammaSixCyclicCharacterReadout a
        ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom f) =
      (Real.exp a - 1) * sourceHorizontalGammaSixCyclicCharacterReadout a f) f ?_ ?_ ?_
  · intro k
    rw [show (MonoidAlgebra.of ℝ SourceHorizontalGammaSixCyclicGroup) k =
          MonoidAlgebra.single k 1 from rfl,
      deningerZBoundary_single, one_smul, map_sub,
      sourceHorizontalGammaSixCyclicCharacterReadout_single,
      sourceHorizontalGammaSixCyclicCharacterReadout_single]
    have hval :
        Multiplicative.toAdd
            (k * deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) =
          Multiplicative.toAdd k + 1 := by
      exact deningerZVal_mul_gen sourceHorizontalGammaSixCyclicGroupEquiv k
    rw [hval]
    push_cast
    rw [mul_add, Real.exp_add]
    ring
  · intro x y hx hy
    simp only [map_add, hx, hy]
    ring
  · intro c x hx
    simp only [map_smul, hx, smul_eq_mul]
    ring

/-- **Exact descent classification.** Physical-character evaluation kills every source
`t - 1` boundary exactly at horizontal grade zero. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_comp_boundary_eq_zero_iff
    (a : ℝ) :
    (sourceHorizontalGammaSixCyclicCharacterReadout a).comp
          (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap = 0 ↔
      a = 0 := by
  constructor
  · intro hzero
    have h := LinearMap.congr_fun hzero
      (MonoidAlgebra.single (1 : SourceHorizontalGammaSixCyclicGroup) (1 : ℝ))
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
    change sourceHorizontalGammaSixCyclicCharacterReadout a
      ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom
        (MonoidAlgebra.single (1 : SourceHorizontalGammaSixCyclicGroup) (1 : ℝ))) = 0 at h
    rw [sourceHorizontalGammaSixCyclicCharacterReadout_boundary,
      sourceHorizontalGammaSixCyclicCharacterReadout_single] at h
    have hone :
        (Multiplicative.toAdd (1 : SourceHorizontalGammaSixCyclicGroup) : ℤ) = 0 := rfl
    rw [hone] at h
    norm_num at h
    have hexp : Real.exp a = 1 := sub_eq_zero.mp h
    exact Real.exp_injective (by simpa using hexp)
  · rintro rfl
    apply LinearMap.ext
    intro f
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    change sourceHorizontalGammaSixCyclicCharacterReadout 0
      ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom f) = 0
    rw [sourceHorizontalGammaSixCyclicCharacterReadout_boundary]
    simp

/-- On each retained orientation pair, group-algebra evaluation agrees exactly with the original
exponent-carrier character. -/
@[simp] theorem sourceHorizontalGammaSixCyclicCharacterReadout_atom
    (a : ℝ) (m : ℕ) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
        (sourceHorizontalGammaSixCyclicGroupAtom m) =
      2 * Real.sinh (a * m) := by
  rw [sourceHorizontalGammaSixCyclicGroupAtom, map_sub,
    sourceHorizontalGammaSixCyclicCharacterReadout_single,
    sourceHorizontalGammaSixCyclicCharacterReadout_single]
  simp only [mul_one]
  have hp : Multiplicative.toAdd (Multiplicative.ofAdd (m : ℤ)) = (m : ℤ) := rfl
  have hn : Multiplicative.toAdd (Multiplicative.ofAdd (-(m : ℤ))) = -(m : ℤ) := rfl
  rw [hp, hn]
  simp only [Int.cast_neg, Int.cast_natCast, Real.sinh_eq]
  ring

/-- The literal cyclic boundary—not a coefficient surrogate—has physical value exactly equal to
twice the finite Gamma-six Green/Wold shell profile. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_harmonicBoundaryClass_eq_profile
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    sourceHorizontalGammaSixCyclicCharacterReadout (u / N)
        (sourceHorizontalGammaSixCyclicHarmonicBoundaryClass N) =
      2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u := by
  calc
    sourceHorizontalGammaSixCyclicCharacterReadout (u / N)
        (sourceHorizontalGammaSixCyclicHarmonicBoundaryClass N) =
        sourceHorizontalGammaSixExponentCharacterReadout (u / N)
          (sourceHorizontalGammaSixHarmonicBoundaryClass N) := by
      rw [sourceHorizontalGammaSixCyclicHarmonicBoundaryClass,
        sourceHorizontalGammaSixHarmonicBoundaryClass, map_sub, map_sub,
        map_smul, map_smul, map_sum, map_sum]
      simp_rw [map_smul, sourceHorizontalGammaSixCyclicCharacterReadout_atom,
        sourceHorizontalGammaSixExponentCharacterReadout_atom]
    _ = 2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u :=
      sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_eq_profile hN u

/-! ## Actual Xi-specialized physical descent -/

/-- Additive exponent of the literal degree-six half-density character. -/
def sourceHorizontalGammaSixPhysicalCharacterParameter (s : ℂ) : ℝ :=
  (2 * s.re - 1) * Real.log 6

/-- The cyclic group-algebra character is exactly the existing marked exceptional
Gamma-six/Burnol/BV reader at every spectral parameter and every retained grade. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_atom_eq_exceptionalTameReader
    (s : ℂ) (m : ℕ) :
    sourceHorizontalGammaSixCyclicCharacterReadout
        (sourceHorizontalGammaSixPhysicalCharacterParameter s)
        (sourceHorizontalGammaSixCyclicGroupAtom m) =
      deningerGammaSixExceptionalTameReader m s := by
  rw [sourceHorizontalGammaSixCyclicCharacterReadout_atom,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature,
    deningerTensorSquareRadialMateCurvature_eq_sinh]
  · congr 2
    rw [sourceHorizontalGammaSixPhysicalCharacterParameter,
      Nat.cast_pow, Real.log_pow]
    norm_num
    ring
  · positivity

/-- Pointwise source producer isolated after all connectors: the actual physical character of an
Xi divisor copy descends through the literal Deninger `t - 1` source boundary. -/
def SourceZeroGammaSixCyclicPhysicalCharacterDescends (q : XiZeroCopy) : Prop :=
  (sourceHorizontalGammaSixCyclicCharacterReadout
      (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).comp
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap = 0

/-- Exact pointwise classification: physical homological descent is neither weaker nor stronger
than critical-line placement. -/
theorem sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff
    (q : XiZeroCopy) :
    SourceZeroGammaSixCyclicPhysicalCharacterDescends q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [SourceZeroGammaSixCyclicPhysicalCharacterDescends,
    sourceHorizontalGammaSixCyclicCharacterReadout_comp_boundary_eq_zero_iff,
    sourceHorizontalGammaSixPhysicalCharacterParameter]
  have hlog : Real.log (6 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · intro h
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp h).resolve_right hlog)
  · intro hline
    change primeDepthBVWoldXiCenteredRate q.1 * Real.log 6 = 0
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline, zero_mul]

/-- Global physical cyclic descent statement.  This names the remaining producer without hiding
its quantifiers or replacing the fixed reader. -/
def SourceZeroGammaSixCyclicPhysicalCharactersDescend : Prop :=
  ∀ q : XiZeroCopy, SourceZeroGammaSixCyclicPhysicalCharacterDescends q

/-- Frankenstein endpoint: fixed-reader cyclicity on the constructed Gamma-six source boundary
for every multiplicity copy is exactly RH.  The theorem is a receiver and does not assert that
cyclicity producer. -/
theorem sourceZeroGammaSixCyclicPhysicalCharactersDescend_iff_riemannHypothesis :
    SourceZeroGammaSixCyclicPhysicalCharactersDescend ↔ RiemannHypothesis := by
  constructor
  · intro hdescends
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      exact (sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff q).1
        (hdescends q)
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH q
    apply (sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
