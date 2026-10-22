import GaloisForLFunctions.RHTower.Suzuki.SuzukiAdmissibleTwoShiftAffineSewing

/-!
# Suzuki projected continuous deficiency channels

Suzuki's continuous-kernel operator is

`S_a = P_a G P_a - eta (-Delta_N)⁻¹`

on the zero-mean space.  Its ordinary interval output is therefore defined only after the output
projection has removed a constant.  The displayed Section 8.3 representatives `exp(x)+i` and
`exp(-x)-i` cannot themselves be the zero-mean operator values.  Canonical centering instead gives
two reflected interior representatives of the form

`hPlus(x)=exp(x)+c`, `hMinus(x)=exp(-x)+c`.

This file formalizes the exact positive survivor without assuming existence of an ordinary
`L²` inverse for the compact first-kind operator.  Any differentiable reflected pair satisfying

`hPlus' - hPlus = -c`, `hMinus' + hMinus = c`

has complete cancellation of its first-order bulk at phase `q=1`.  Its finite-interval Suzuki
bracket is exactly one sine clock

`2 A sin(a z)`,

where `A` is the common sum of the two endpoint values.  Thus the projection ambiguity is not an
unknown entire function: it is a one-dimensional, all-real-zero clock, nonvanishing at every
nonreal point.  In arbitrary two-shift affine sewing, both interval channels retain this common
sine factor.

The theorem corrects the printed `q=-1` plateau cancellation and closes the projected interval
part of source identification.  It does not prove holomorphy of the exterior continuation; that
remaining exterior Schur-complement statement is RH-bearing.

No estimate, aperture limit, numerical computation, RH assumption, or unproved analytic inverse
is used.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Fourier transform of one finite-interval continuous-kernel representative. -/
def suzukiProjectedIntervalFourier (f : ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x in -a..a, f x * suzukiOscillatoryKernel z x

/-- **Projected bulk cancellation.**  If the two reflected continuous-kernel representatives have
opposite constant first-order defects, their `q=1` Suzuki bracket consists only of endpoint flux.
The statement allows arbitrary differentiable representatives and does not assume a first-kind
inverse exists in `L²`. -/
theorem suzukiProjectedInteriorBracket_eq_boundary
    (fPlus fMinus fPlus' fMinus' : ℝ → ℂ) (a : ℝ) (z c : ℂ)
    (hfPlus : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt fPlus (fPlus' x) x)
    (hfMinus : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt fMinus (fMinus' x) x)
    (hfPlus'i : IntervalIntegrable fPlus' MeasureTheory.volume (-a) a)
    (hfMinus'i : IntervalIntegrable fMinus' MeasureTheory.volume (-a) a)
    (hPlusODE : ∀ x ∈ Set.uIcc (-a) a, fPlus' x - fPlus x = -c)
    (hMinusODE : ∀ x ∈ Set.uIcc (-a) a, fMinus' x + fMinus x = c) :
    suzukiTwoChannelBracket
        (suzukiProjectedIntervalFourier fPlus a)
        (suzukiProjectedIntervalFourier fMinus a) 1 z =
      -I * ((fPlus a + fMinus a) * suzukiOscillatoryKernel z a -
        (fPlus (-a) + fMinus (-a)) * suzukiOscillatoryKernel z (-a)) := by
  let K : ℝ → ℂ := suzukiOscillatoryKernel z
  let K' : ℝ → ℂ := fun x => (I * z) * K x
  have hK : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt K (K' x) x := by
    intro x hx
    exact hasDerivAt_suzukiOscillatoryKernel z x
  have hKc : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_suzukiOscillatoryKernel z x).continuousAt
  have hK'i : IntervalIntegrable K' MeasureTheory.volume (-a) a :=
    (by fun_prop : Continuous K').intervalIntegrable _ _
  have hPlusIBP := intervalIntegral.integral_deriv_mul_eq_sub
    hfPlus hK hfPlus'i hK'i
  have hMinusIBP := intervalIntegral.integral_deriv_mul_eq_sub
    hfMinus hK hfMinus'i hK'i
  have hPlusI : IntervalIntegrable fPlus MeasureTheory.volume (-a) a :=
    (show ContinuousOn fPlus (Set.uIcc (-a) a) from
      fun x hx => (hfPlus x hx).continuousAt.continuousWithinAt).intervalIntegrable
  have hMinusI : IntervalIntegrable fMinus MeasureTheory.volume (-a) a :=
    (show ContinuousOn fMinus (Set.uIcc (-a) a) from
      fun x hx => (hfMinus x hx).continuousAt.continuousWithinAt).intervalIntegrable
  have hPlusK : IntervalIntegrable (fun x => fPlus x * K x)
      MeasureTheory.volume (-a) a := hPlusI.mul_continuousOn hKc.continuousOn
  have hMinusK : IntervalIntegrable (fun x => fMinus x * K x)
      MeasureTheory.volume (-a) a := hMinusI.mul_continuousOn hKc.continuousOn
  have hPlus'K : IntervalIntegrable (fun x => fPlus' x * K x)
      MeasureTheory.volume (-a) a := hfPlus'i.mul_continuousOn hKc.continuousOn
  have hMinus'K : IntervalIntegrable (fun x => fMinus' x * K x)
      MeasureTheory.volume (-a) a := hfMinus'i.mul_continuousOn hKc.continuousOn
  have hPlusK' : IntervalIntegrable (fun x => fPlus x * K' x)
      MeasureTheory.volume (-a) a :=
    hK'i.continuousOn_mul (fun x hx => (hfPlus x hx).continuousAt.continuousWithinAt)
  have hMinusK' : IntervalIntegrable (fun x => fMinus x * K' x)
      MeasureTheory.volume (-a) a :=
    hK'i.continuousOn_mul (fun x hx => (hfMinus x hx).continuousAt.continuousWithinAt)
  rw [intervalIntegral.integral_add hPlus'K hPlusK'] at hPlusIBP
  rw [intervalIntegral.integral_add hMinus'K hMinusK'] at hMinusIBP
  have hPlusK'_const :
      (∫ x in -a..a, fPlus x * K' x) =
        (I * z) * (∫ x in -a..a, fPlus x * K x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [K']
    ring
  have hMinusK'_const :
      (∫ x in -a..a, fMinus x * K' x) =
        (I * z) * (∫ x in -a..a, fMinus x * K x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [K']
    ring
  rw [hPlusK'_const] at hPlusIBP
  rw [hMinusK'_const] at hMinusIBP
  have hbulk :
      (∫ x in -a..a, (fPlus' x - fPlus x) * K x) =
        -(∫ x in -a..a, (fMinus' x + fMinus x) * K x) := by
    calc
      _ = ∫ x in -a..a, -((fMinus' x + fMinus x) * K x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp only
            rw [hPlusODE x hx, hMinusODE x hx]
            ring
      _ = -(∫ x in -a..a, (fMinus' x + fMinus x) * K x) := by
            rw [intervalIntegral.integral_neg]
  have hPlusDiff :
      (∫ x in -a..a, (fPlus' x - fPlus x) * K x) =
        (∫ x in -a..a, fPlus' x * K x) -
          (∫ x in -a..a, fPlus x * K x) := by
    rw [show (fun x => (fPlus' x - fPlus x) * K x) =
        fun x => fPlus' x * K x - fPlus x * K x by funext x; ring,
      intervalIntegral.integral_sub hPlus'K hPlusK]
  have hMinusAdd :
      (∫ x in -a..a, (fMinus' x + fMinus x) * K x) =
        (∫ x in -a..a, fMinus' x * K x) +
          (∫ x in -a..a, fMinus x * K x) := by
    rw [show (fun x => (fMinus' x + fMinus x) * K x) =
        fun x => fMinus' x * K x + fMinus x * K x by funext x; ring,
      intervalIntegral.integral_add hMinus'K hMinusK]
  rw [hPlusDiff, hMinusAdd] at hbulk
  have hbulk0 :
      (∫ x in -a..a, fPlus' x * K x) -
          (∫ x in -a..a, fPlus x * K x) +
        ((∫ x in -a..a, fMinus' x * K x) +
          (∫ x in -a..a, fMinus x * K x)) = 0 := by
    linear_combination hbulk
  simp only [suzukiTwoChannelBracket, suzukiProjectedIntervalFourier, one_mul]
  change (z - I) * (∫ x in -a..a, fPlus x * K x) +
      (z + I) * (∫ x in -a..a, fMinus x * K x) = _
  have hboundary0 :
      (fPlus a * K a - fPlus (-a) * K (-a)) +
          (fMinus a * K a - fMinus (-a) * K (-a)) =
        (∫ x in -a..a, fPlus' x * K x) +
          (∫ x in -a..a, fMinus' x * K x) +
          I * z * ((∫ x in -a..a, fPlus x * K x) +
            (∫ x in -a..a, fMinus x * K x)) := by
    calc
      _ = ((∫ x in -a..a, fPlus' x * K x) +
            I * z * (∫ x in -a..a, fPlus x * K x)) +
          ((∫ x in -a..a, fMinus' x * K x) +
            I * z * (∫ x in -a..a, fMinus x * K x)) := by
              rw [hPlusIBP, hMinusIBP]
      _ = _ := by ring
  have hboundary :
      (fPlus a * K a - fPlus (-a) * K (-a)) +
          (fMinus a * K a - fMinus (-a) * K (-a)) =
        ((∫ x in -a..a, fPlus x * K x) -
            (∫ x in -a..a, fMinus x * K x)) +
          I * z * ((∫ x in -a..a, fPlus x * K x) +
            (∫ x in -a..a, fMinus x * K x)) := by
    rw [hboundary0]
    linear_combination hbulk0
  have hboundaryR :
      (fPlus a + fMinus a) * suzukiOscillatoryKernel z a -
          (fPlus (-a) + fMinus (-a)) * suzukiOscillatoryKernel z (-a) =
        (fPlus a * K a - fPlus (-a) * K (-a)) +
          (fMinus a * K a - fMinus (-a) * K (-a)) := by
    simp only [K]
    ring
  rw [hboundaryR, hboundary]
  rw [mul_add]
  have hclock :
      -I * (I * z * ((∫ x in -a..a, fPlus x * K x) +
        (∫ x in -a..a, fMinus x * K x))) =
      z * ((∫ x in -a..a, fPlus x * K x) +
        (∫ x in -a..a, fMinus x * K x)) := by
    calc
      _ = -(I * I) * z * ((∫ x in -a..a, fPlus x * K x) +
          (∫ x in -a..a, fMinus x * K x)) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [hclock]
  ring

/-- The one-dimensional clock left by the correctly projected reflected interior pair. -/
def suzukiProjectedSineClock (a : ℝ) (A z : ℂ) : ℂ :=
  2 * A * Complex.sin ((a : ℂ) * z)

/-- **Exact projected interval law.**  Reflection makes the endpoint sums equal.  The complete
`q=1` interval bracket is then one sine clock, rather than an uncontrolled entire correction. -/
theorem suzukiProjectedInteriorBracket_eq_sineClock
    (fPlus fMinus fPlus' fMinus' : ℝ → ℂ) (a : ℝ) (z c A : ℂ)
    (hfPlus : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt fPlus (fPlus' x) x)
    (hfMinus : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt fMinus (fMinus' x) x)
    (hfPlus'i : IntervalIntegrable fPlus' MeasureTheory.volume (-a) a)
    (hfMinus'i : IntervalIntegrable fMinus' MeasureTheory.volume (-a) a)
    (hPlusODE : ∀ x ∈ Set.uIcc (-a) a, fPlus' x - fPlus x = -c)
    (hMinusODE : ∀ x ∈ Set.uIcc (-a) a, fMinus' x + fMinus x = c)
    (hRight : fPlus a + fMinus a = A)
    (hLeft : fPlus (-a) + fMinus (-a) = A) :
    suzukiTwoChannelBracket
        (suzukiProjectedIntervalFourier fPlus a)
        (suzukiProjectedIntervalFourier fMinus a) 1 z =
      suzukiProjectedSineClock a A z := by
  rw [suzukiProjectedInteriorBracket_eq_boundary fPlus fMinus fPlus' fMinus'
    a z c hfPlus hfMinus hfPlus'i hfMinus'i hPlusODE hMinusODE,
    hRight, hLeft]
  simp only [suzukiProjectedSineClock, suzukiOscillatoryKernel, Complex.sin]
  rw [show (a : ℂ) * (I * z) = I * ((a : ℂ) * z) by ring,
    show ((-a : ℝ) : ℂ) * (I * z) = -(I * ((a : ℂ) * z)) by
      norm_num
      ring]
  ring_nf

/-- The projected interval clock has no nonreal zero.  Thus it cannot cancel an off-real Xi pole. -/
theorem suzukiProjectedSineClock_ne_zero_of_im_ne_zero
    {a : ℝ} (ha : a ≠ 0) {A z : ℂ} (hA : A ≠ 0) (hz : z.im ≠ 0) :
    suzukiProjectedSineClock a A z ≠ 0 := by
  intro hzero
  have hsin : Complex.sin ((a : ℂ) * z) = 0 := by
    simp only [suzukiProjectedSineClock] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hA)
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have him := congrArg Complex.im hk
  norm_num [mul_im] at him
  exact him.elim ha hz

/-- Affine sewing of two projected interval channels retains one common sine-clock factor.  All
source-dependent projection constants are confined to the remaining explicit scalar bracket. -/
theorem suzukiAffineSewnIntervalPart_projectedSineClock
    (a : ℝ) (alpha beta gamma AAlpha ABeta : ℂ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (suzukiProjectedSineClock a AAlpha)
        (suzukiProjectedSineClock a ABeta) z =
      suzukiProjectedSineClock a 1 z *
        ((beta - gamma) * WBeta z * AAlpha -
          (alpha - gamma) * WAlpha z * ABeta) := by
  simp only [suzukiAffineSewnIntervalPart, suzukiProjectedSineClock]
  ring

end

end RHTower
