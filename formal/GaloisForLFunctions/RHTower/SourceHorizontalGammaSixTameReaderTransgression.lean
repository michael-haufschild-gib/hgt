import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding
import GaloisForLFunctions.RHTower.SourceHorizontalShellGreenPrimeClockProfile
import GaloisForLFunctions.RHTower.DeningerExponentExceptionalTameGreenBridge

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

end

end RHTower
