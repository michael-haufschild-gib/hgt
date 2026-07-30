import GaloisForLFunctions.RHTower.XiBVResidueHurwitzPhaseEnergyUniversalityLaw
import GaloisForLFunctions.RHTower.XiRealTransverseQuartetSurgeryMatroidInvariance

/-!
# The complex modular character of the Riemann divisor

Every spectral point `rho` carries the centered one-dimensional complex
character

```text
chi_rho(z) = exp(z * (rho - 1/2)).
```

Its real ray is the Mellin character governing compact-BV source dilation.
Its imaginary period is the negative Hurwitz monodromy character.  Critical
line reflection negates its real weight, and the supremum of the positive Xi
weights is the projective reflection aperture.

The final theorem separates this height-uniform character weight from five
weaker reporters at once.  A fixed off-critical quartet can escape to
infinite height while every compact holomorphic jet and bounded Ward window
loses it, its reciprocal-square energy tends to zero, and its full
real-aperture differential matroid remains unchanged.  Its Ward mass remains
exactly `8*pi`, and its modular weight and principal Hurwitz phase remain the
same prescribed positive number.
-/

open Complex Filter MeasureTheory Real Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential ENNReal UpperEndDifferentialInstances

namespace RHTower

noncomputable section

/-- Centered one-dimensional complex dilation character of a spectral
point. -/
def centeredComplexModularCharacter (rho z : ℂ) : ℂ :=
  Complex.exp (z * (rho - 1 / 2))

/-- The modular character is a representation of the additive complex
dilation plane. -/
theorem centeredComplexModularCharacter_add
    (rho z w : ℂ) :
    centeredComplexModularCharacter rho (z + w) =
      centeredComplexModularCharacter rho z *
        centeredComplexModularCharacter rho w := by
  rw [centeredComplexModularCharacter, centeredComplexModularCharacter,
    centeredComplexModularCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- The norm on the real parameter ray is the exponential of the centered
horizontal weight. -/
theorem norm_centeredComplexModularCharacter_ofReal
    (rho : ℂ) (t : ℝ) :
    ‖centeredComplexModularCharacter rho (t : ℂ)‖ =
      Real.exp (t * (rho.re - 1 / 2)) := by
  rw [centeredComplexModularCharacter, Complex.norm_exp]
  congr 1
  norm_num [Complex.sub_re, mul_re]

/-- Positive real Mellin dilation is the real-ray restriction of the complex
modular character. -/
theorem centeredComplexModularCharacter_real_cpow
    (rho : ℂ) {r : ℝ} (hr : 0 < r) :
    centeredComplexModularCharacter rho (Real.log r : ℂ) =
      (r : ℂ) ^ (rho - 1 / 2) := by
  rw [centeredComplexModularCharacter,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]
  rw [← Complex.ofReal_log hr.le]

/-- Every nonzero real character parameter recovers the centered horizontal
weight exactly from a logarithmic norm ratio. -/
theorem centeredComplexModularCharacter_weight_recovery
    (rho : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Real.log ‖centeredComplexModularCharacter rho (t : ℂ)‖ / t =
      rho.re - 1 / 2 := by
  rw [norm_centeredComplexModularCharacter_ofReal, Real.log_exp]
  field_simp

/-- Critical-line reflection of an arbitrary complex spectral point. -/
def criticalLineReflectionPoint (rho : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) rho

/-- Critical-line reflection negates the real modular weight. -/
theorem criticalLineReflectionPoint_weight (rho : ℂ) :
    (criticalLineReflectionPoint rho).re - 1 / 2 =
      -(rho.re - 1 / 2) := by
  simp [criticalLineReflectionPoint]
  ring

/-- Reflected real-ray character norms are exact multiplicative duals. -/
theorem norm_centeredComplexModularCharacter_reflection_mul
    (rho : ℂ) (t : ℝ) :
    ‖centeredComplexModularCharacter
        (criticalLineReflectionPoint rho) (t : ℂ)‖ *
      ‖centeredComplexModularCharacter rho (t : ℂ)‖ = 1 := by
  rw [norm_centeredComplexModularCharacter_ofReal,
    norm_centeredComplexModularCharacter_ofReal,
    criticalLineReflectionPoint_weight, ← Real.exp_add]
  have hzero :
      t * (-(rho.re - 1 / 2)) +
        t * (rho.re - 1 / 2) = 0 := by ring
  rw [hzero, Real.exp_zero]

/-- The negative Hurwitz monodromy character is the imaginary-period value
of the centered complex modular character. -/
theorem centeredComplexModularCharacter_hurwitzPeriod
    (rho : ℂ) :
    centeredComplexModularCharacter rho
        (-2 * (Real.pi : ℂ) * Complex.I) =
      -HurwitzOrbit.monoScalar rho := by
  rw [centeredComplexModularCharacter, HurwitzOrbit.monoScalar]
  calc
    Complex.exp
        ((-2 * (Real.pi : ℂ) * Complex.I) * (rho - 1 / 2)) =
      Complex.exp
        ((Real.pi : ℂ) * Complex.I +
          -(2 * (Real.pi : ℂ) * Complex.I * rho)) := by
            congr 1
            ring
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * rho)) := by
          rw [Complex.exp_add]
    _ = -Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * rho)) := by
          rw [Complex.exp_pi_mul_I]
          ring

/-- On the open critical strip the principal imaginary-period phase recovers
the absolute centered modular weight without aliasing. -/
theorem centeredComplexModularCharacter_principalPhase
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    |(centeredComplexModularCharacter rho
        (-2 * (Real.pi : ℂ) * Complex.I)).arg| /
        (2 * Real.pi) =
      |rho.re - 1 / 2| := by
  rw [centeredComplexModularCharacter_hurwitzPeriod,
    monoScalar_neg_arg_openCriticalStrip hstrip]
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hneg : -2 * Real.pi < 0 := by nlinarith [Real.pi_pos]
  rw [abs_mul, abs_of_neg hneg]
  field_simp [hpi.ne']

/-- Positive modular weight carried by one right-half Xi zero copy. -/
def xiRightComplexModularWeight (q : XiRightZeroCopy) : ℝ :=
  (q.1.1 : ℂ).re - 1 / 2

/-- The Xi modular weight is exactly the principal Hurwitz phase. -/
theorem xiRightComplexModularWeight_eq_hurwitzPrincipalPhase
    (q : XiRightZeroCopy) :
    xiRightComplexModularWeight q =
      xiHurwitzRightPrincipalPhase q := by
  rw [xiRightComplexModularWeight,
    xiHurwitzRightPrincipalPhase_eq_transverse,
    xiRightCenteredZero_eq_support_sub_half, Complex.sub_re]
  norm_num

/-- Supremal positive modular weight of the Xi divisor. -/
def xiRightComplexModularWeightSup : ℝ :=
  sSup (Set.range xiRightComplexModularWeight)

/-- The supremal modular weight is exactly the intrinsic projective
reflection aperture. -/
theorem xiRightComplexModularWeightSup_eq_projectiveReflectionRadius :
    xiRightComplexModularWeightSup =
      xiProjectiveReflectionRadius := by
  have hfun :
      xiRightComplexModularWeight =
        xiHurwitzRightPrincipalPhase := by
    funext q
    exact xiRightComplexModularWeight_eq_hurwitzPrincipalPhase q
  rw [xiRightComplexModularWeightSup, hfun,
    ← xiHurwitzRightPrincipalPhaseSet]
  rw [← xiHurwitzRightPrincipalPhaseSup,
    xiHurwitzRightPrincipalPhaseSup_eq_transverseSup,
    ← xiProjectiveReflectionRadius_eq_transverseSup]

/-- Forward/inverse compact-BV source residues reconstruct the same modular
weight carried by the Hurwitz character and aperture. -/
theorem xiBVResiduePhaseCoordinate_eq_complexModularWeight
    (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r)
    (q : XiRightZeroCopy)
    (hres : W.continuedSourceResidueValue (q.1.1 : ℂ) ≠ 0) :
    xiBVResiduePhaseCoordinate W r hr q =
      xiRightComplexModularWeight q := by
  have hcert := xiBVResidue_hurwitzPhaseEnergyUniversality W hr q hres
  rw [hcert.phaseReconstruction,
    xiRightComplexModularWeight_eq_hurwitzPrincipalPhase]

/-- Canonical upper-right point of the escaping quartet. -/
def escapingModularPoint (a : ℝ) (n : ℕ) : ℂ :=
  (1 / 2 : ℂ) + (a : ℂ) +
    Complex.I * (escapingQuartetHeight n : ℂ)

/-- Its modular weight is independent of height. -/
theorem escapingModularPoint_weight (a : ℝ) (n : ℕ) :
    (escapingModularPoint a n).re - 1 / 2 = a := by
  simp [escapingModularPoint]

/-- Its principal Hurwitz phase is the same fixed positive weight at every
height. -/
theorem escapingModularPoint_principalPhase
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (n : ℕ) :
    |(centeredComplexModularCharacter (escapingModularPoint a n)
        (-2 * (Real.pi : ℂ) * Complex.I)).arg| /
        (2 * Real.pi) = a := by
  rw [centeredComplexModularCharacter_principalPhase]
  · rw [escapingModularPoint_weight, abs_of_pos ha0]
  · rw [escapingModularPoint]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_zero]
    norm_num
    constructor <;> linarith

/-- Reciprocal-square trace-class orientation shadow of one escaping
upper-right quartet point. -/
def escapingModularTraceEnergy (a : ℝ) (n : ℕ) : ℝ :=
  Real.sin (2 * Real.pi * a) ^ 2 *
    escapingQuartetScale n ^ 2 /
      (1 + a ^ 2 * escapingQuartetScale n ^ 2)

/-- Exact centered-distance form of the escaping trace-class energy. -/
theorem escapingModularTraceEnergy_eq
    (a : ℝ) (n : ℕ) :
    escapingModularTraceEnergy a n =
      Real.sin (2 * Real.pi * a) ^ 2 /
        (a ^ 2 + escapingQuartetHeight n ^ 2) := by
  rw [escapingModularTraceEnergy, escapingQuartetScale]
  have hh : escapingQuartetHeight n ≠ 0 :=
    ne_of_gt (escapingQuartetHeight_pos n)
  field_simp [hh]
  ring

/-- Reciprocal-square energy loses a fixed nonzero modular weight at the
height boundary. -/
theorem escapingModularTraceEnergy_tendsto_zero (a : ℝ) :
    Tendsto (escapingModularTraceEnergy a) atTop (nhds 0) := by
  have hs :
      Tendsto (fun n : ℕ => escapingQuartetScale n ^ 2)
        atTop (nhds 0) :=
    by simpa using escapingQuartetScale_tendsto_zero.pow 2
  have hnum :
      Tendsto
        (fun n : ℕ =>
          Real.sin (2 * Real.pi * a) ^ 2 *
            escapingQuartetScale n ^ 2)
        atTop (nhds 0) := by
    simpa using hs.const_mul (Real.sin (2 * Real.pi * a) ^ 2)
  have hden :
      Tendsto
        (fun n : ℕ => 1 + a ^ 2 * escapingQuartetScale n ^ 2)
        atTop (nhds 1) := by
    simpa using Tendsto.const_add 1 (hs.const_mul (a ^ 2))
  change Tendsto
    (fun n : ℕ =>
      Real.sin (2 * Real.pi * a) ^ 2 *
        escapingQuartetScale n ^ 2 /
          (1 + a ^ 2 * escapingQuartetScale n ^ 2))
    atTop (nhds 0)
  have hquot := hnum.div hden (by norm_num)
  convert hquot using 1
  · ext n
    rfl
  · norm_num

/-- Simultaneous compact, differential, Ward, energy, and character behavior
of one escaping functional-equation quartet. -/
structure EscapingModularCharacterSeparationCertificate (a : ℝ) : Prop where
  hypertranscendental :
    ∀ n, Hypertranscendental (escapingQuartetGaugedXi a n)
  completedSymmetry :
    (∀ n s, escapingQuartetGaugedXi a n (1 - s) =
      escapingQuartetGaugedXi a n s) ∧
    (∀ n s, escapingQuartetGaugedXi a n ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (escapingQuartetGaugedXi a n s))
  offCriticalZero :
    ∀ n, (quartetPoint a (escapingQuartetHeight n)).re ≠ 1 / 2 ∧
      escapingQuartetGaugedXi a n
        (quartetPoint a (escapingQuartetHeight n)) = 0
  allJetsEscape :
    ∀ j, TendstoLocallyUniformly
      (fun n => iteratedDeriv j (escapingQuartetGaugedXi a n))
      (iteratedDeriv j xi) atTop
  wardEscapesEveryBoundedWindow :
    ∀ R, 0 ≤ R → TendstoUniformlyOn
      (fun n t => quartetWardInfinitesimalDensity a
        (escapingQuartetHeight n) t)
      (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}
  wardMassQuantized :
    ∀ n, ∫⁻ t : ℝ, ENNReal.ofReal
      (quartetWardInfinitesimalDensity a
        (escapingQuartetHeight n) t) =
      ENNReal.ofReal (8 * Real.pi)
  continuumDifferentialMatroidBlind :
    ∀ (A : Type) (shift : A → ℝ) (n : ℕ),
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (fun i =>
            escapingQuartetRealShiftUpperEndCarrier a n (shift i)) =
        differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (fun i => xiRealTransverseShiftUpperEndCarrier (shift i))
  fixedModularWeight :
    ∀ n, (escapingModularPoint a n).re - 1 / 2 = a
  fixedHurwitzPrincipalPhase :
    ∀ n, |(centeredComplexModularCharacter (escapingModularPoint a n)
        (-2 * (Real.pi : ℂ) * Complex.I)).arg| /
        (2 * Real.pi) = a
  traceClassEnergyEscapes :
    Tendsto (escapingModularTraceEnergy a) atTop (nhds 0)

/-- **Complex modular-character separation law.**  A fixed nonzero horizontal
character weight survives while every holomorphic jet, bounded Ward window,
and reciprocal-square energy shadow loses the same escaping quartet.  The
total Ward charge stays quantized and the full continuum differential matroid
remains unchanged. -/
theorem escapingModularCharacterSeparation_law
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    EscapingModularCharacterSeparationCertificate a := by
  have hescape := compactOpenKolchinWardChargeEscape_law ha0 ha1
  exact {
    hypertranscendental := hescape.1
    completedSymmetry := ⟨hescape.2.2.1, hescape.2.2.2.1⟩
    offCriticalZero := hescape.2.2.2.2.1
    allJetsEscape := hescape.2.2.2.2.2.1
    wardEscapesEveryBoundedWindow := hescape.2.2.2.2.2.2.1
    wardMassQuantized := hescape.2.2.2.2.2.2.2
    continuumDifferentialMatroidBlind :=
      fun _A shift n =>
        escapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw
          a n shift
    fixedModularWeight := escapingModularPoint_weight a
    fixedHurwitzPrincipalPhase :=
      escapingModularPoint_principalPhase ha0 ha1
    traceClassEnergyEscapes :=
      escapingModularTraceEnergy_tendsto_zero a }

end

end RHTower
