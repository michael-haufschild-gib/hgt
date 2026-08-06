import GaloisForLFunctions.HTGeometry.ShiftDivisorReflection
import GaloisForLFunctions.RHTower.XiPairwiseShiftValueReflection

/-!
# Completed-Xi value reflection for arbitrary finite shift divisors

Reciprocity `xi (1 - s) = xi s` gives the signed reflection `logDeriv xi (1 - s) = -logDeriv xi s`.
Applied to a finitely supported complex divisor `w` of shifts, the divisor reflection law says that
reflecting the observation coordinate about `σ / 2` is exactly reflecting the divisor about
`(1 - σ) / 2`:

  `∑ a w a * logDeriv xi (σ - s + a) = -∑ a w a * logDeriv xi (s + (1 - σ - a))`.

Hence a weighted family of completed-Xi translates has an exact reflection law precisely when its
divisor is a reflection eigenvector, and the eigenvalue decides invariance versus anti-invariance.
The one-shift defect and the two-endpoint pairwise difference are the point and two-point divisors;
their midpoints `(1 - a) / 2` and `(1 - a - b) / 2` are the divisor reflection centres, and the
endpoint-order bookkeeping disappears because the divisor law needs no order on the shifts.

Two consequences hold for every divisor with no eigenvector hypothesis at all: the canonical
splitting of a divisor into reflection-invariant and anti-invariant parts splits every weighted
completed-Xi value into a part fixed by the coordinate reflection and a part that is negated by it
and therefore vanishes at the centre.  For the entire function `xi` itself the negated part vanishes
to all orders in the prescribed jet parity at the centre.
-/

namespace RHTower

open Complex

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Finite differences are divisor values -/

/-- A forward difference of a divisor value is the divisor value of the difference divisor. -/
theorem forwardDifference_shiftDivisorValue (τ : ℂ) (w : ℂ →₀ ℂ) (f : ℂ → ℂ) (s : ℂ) :
    forwardDifference τ (shiftDivisorValue w f) s =
      shiftDivisorValue (translateShiftDivisor τ w - w) f s := by
  rw [forwardDifference, shiftDivisorValue_sub, shiftDivisorValue_translateShiftDivisor]

/-- **Finite differences are divisor values.** Every iterated forward difference is the weighted
translate family of its iterated difference divisor. -/
theorem iteratedForwardDifference_eq_shiftDivisorValue (τs : List ℂ) (f : ℂ → ℂ) :
    iteratedForwardDifference τs f = shiftDivisorValue (iteratedDifferenceDivisor τs) f := by
  induction τs with
  | nil =>
      funext s
      simp [iteratedForwardDifference, iteratedDifferenceDivisor]
  | cons τ τs ih =>
      funext s
      rw [iteratedForwardDifference, ih, iteratedDifferenceDivisor,
        forwardDifference_shiftDivisorValue]

/-! ## The completed-Xi reflection data -/

/-- Completed-Xi reciprocity as a signed reflection about `1 / 2`. -/
theorem xi_signed_reflection (z : ℂ) : xi (2 * (1 / 2 : ℂ) - z) = (1 : ℂ) * xi z := by
  rw [show 2 * (1 / 2 : ℂ) - z = 1 - z by ring, xi_one_sub, one_mul]

/-- Completed-Xi logarithmic-derivative reciprocity as a signed reflection about `1 / 2`. -/
theorem logDeriv_xi_signed_reflection (z : ℂ) :
    logDeriv xi (2 * (1 / 2 : ℂ) - z) = (-1 : ℂ) * logDeriv xi z := by
  rw [show 2 * (1 / 2 : ℂ) - z = 1 - z by ring, logDeriv_xi_reciprocity]
  ring

/-- Completed-Xi value of a finite shift divisor. -/
def xiShiftDivisorValue (w : ℂ →₀ ℂ) (s : ℂ) : ℂ :=
  shiftDivisorValue w xi s

/-- Completed-Xi logarithmic-derivative value of a finite shift divisor. -/
def xiShiftDivisorLogDeriv (w : ℂ →₀ ℂ) (s : ℂ) : ℂ :=
  shiftDivisorValue w (logDeriv xi) s

/-- **Completed-Xi divisor reflection law.** Reflecting the coordinate about `σ / 2` is reflecting
the shift divisor about `(1 - σ) / 2`. -/
theorem xiShiftDivisorValue_reflection (w : ℂ →₀ ℂ) (σ s : ℂ) :
    xiShiftDivisorValue w (σ - s) =
      xiShiftDivisorValue (reflectShiftDivisor (1 - σ) w) s := by
  have h := shiftDivisorValue_signed_reflection xi_signed_reflection w σ s
  rw [show 2 * (1 / 2 : ℂ) - σ = 1 - σ by ring, one_mul] at h
  exact h

/-- **Completed-Xi logarithmic-derivative divisor reflection law.** The functional-equation sign
`-1` is carried through unchanged. -/
theorem xiShiftDivisorLogDeriv_reflection (w : ℂ →₀ ℂ) (σ s : ℂ) :
    xiShiftDivisorLogDeriv w (σ - s) =
      -xiShiftDivisorLogDeriv (reflectShiftDivisor (1 - σ) w) s := by
  have h := shiftDivisorValue_signed_reflection logDeriv_xi_signed_reflection w σ s
  rw [show 2 * (1 / 2 : ℂ) - σ = 1 - σ by ring] at h
  rw [xiShiftDivisorLogDeriv, xiShiftDivisorLogDeriv, h]
  ring

/-! ## Eigen divisors -/

/-- An anti-invariant divisor makes the weighted completed-Xi logarithmic derivative exactly fixed
by reflection about `σ / 2`. -/
theorem xiShiftDivisorLogDeriv_reflection_fixed {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = -w) (s : ℂ) :
    xiShiftDivisorLogDeriv w (σ - s) = xiShiftDivisorLogDeriv w s := by
  rw [xiShiftDivisorLogDeriv_reflection, hw]
  show -shiftDivisorValue (-w) (logDeriv xi) s = shiftDivisorValue w (logDeriv xi) s
  rw [shiftDivisorValue_neg]
  ring

/-- An invariant divisor makes the weighted completed-Xi logarithmic derivative exactly negated by
reflection about `σ / 2`. -/
theorem xiShiftDivisorLogDeriv_reflection_neg {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = w) (s : ℂ) :
    xiShiftDivisorLogDeriv w (σ - s) = -xiShiftDivisorLogDeriv w s := by
  rw [xiShiftDivisorLogDeriv_reflection, hw]

/-- An invariant divisor forces the weighted completed-Xi logarithmic derivative to vanish at the
reflection centre. -/
theorem xiShiftDivisorLogDeriv_center_eq_zero {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = w) :
    xiShiftDivisorLogDeriv w (σ / 2) = 0 := by
  have h := xiShiftDivisorLogDeriv_reflection_neg hw (σ / 2)
  rw [show σ - σ / 2 = σ / 2 by ring] at h
  linear_combination (1 / 2 : ℂ) * h

/-- An invariant divisor makes the weighted completed-Xi value exactly fixed by reflection. -/
theorem xiShiftDivisorValue_reflection_fixed {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = w) (s : ℂ) :
    xiShiftDivisorValue w (σ - s) = xiShiftDivisorValue w s := by
  rw [xiShiftDivisorValue_reflection, hw]

/-- An anti-invariant divisor makes the weighted completed-Xi value exactly negated by
reflection. -/
theorem xiShiftDivisorValue_reflection_neg {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = -w) (s : ℂ) :
    xiShiftDivisorValue w (σ - s) = -xiShiftDivisorValue w s := by
  rw [xiShiftDivisorValue_reflection, hw]
  show shiftDivisorValue (-w) xi s = -shiftDivisorValue w xi s
  rw [shiftDivisorValue_neg]

/-- An anti-invariant divisor forces the weighted completed-Xi value to vanish at the reflection
centre. -/
theorem xiShiftDivisorValue_center_eq_zero {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = -w) :
    xiShiftDivisorValue w (σ / 2) = 0 := by
  have h := xiShiftDivisorValue_reflection_neg hw (σ / 2)
  rw [show σ - σ / 2 = σ / 2 by ring] at h
  linear_combination (1 / 2 : ℂ) * h

/-! ## Universal splitting: no eigen hypothesis -/

/-- **Universal centering law.** Twice any weighted completed-Xi logarithmic-derivative value is
the sum of the value of the reflection-invariant part of its divisor and the value of the
anti-invariant part. -/
theorem xiShiftDivisorLogDeriv_symm_add_antisymm (w : ℂ →₀ ℂ) (σ s : ℂ) :
    xiShiftDivisorLogDeriv (symmShiftDivisorPart (1 - σ) w) s +
        xiShiftDivisorLogDeriv (antisymmShiftDivisorPart (1 - σ) w) s =
      2 * xiShiftDivisorLogDeriv w s := by
  rw [xiShiftDivisorLogDeriv, xiShiftDivisorLogDeriv, xiShiftDivisorLogDeriv,
    symmShiftDivisorPart, antisymmShiftDivisorPart, shiftDivisorValue_add,
    shiftDivisorValue_sub]
  ring

/-- The anti-invariant half of any divisor carries a completed-Xi logarithmic-derivative value
exactly fixed by reflection about `σ / 2`. -/
theorem xiShiftDivisorLogDeriv_antisymmPart_reflection (w : ℂ →₀ ℂ) (σ s : ℂ) :
    xiShiftDivisorLogDeriv (antisymmShiftDivisorPart (1 - σ) w) (σ - s) =
      xiShiftDivisorLogDeriv (antisymmShiftDivisorPart (1 - σ) w) s :=
  xiShiftDivisorLogDeriv_reflection_fixed
    (reflectShiftDivisor_antisymmShiftDivisorPart (1 - σ) w) s

/-- The invariant half of any divisor carries a completed-Xi logarithmic-derivative value that
vanishes at the reflection centre. -/
theorem xiShiftDivisorLogDeriv_symmPart_center_eq_zero (w : ℂ →₀ ℂ) (σ : ℂ) :
    xiShiftDivisorLogDeriv (symmShiftDivisorPart (1 - σ) w) (σ / 2) = 0 :=
  xiShiftDivisorLogDeriv_center_eq_zero
    (reflectShiftDivisor_symmShiftDivisorPart (1 - σ) w)

/-- The invariant half of any divisor carries a completed-Xi value exactly fixed by reflection. -/
theorem xiShiftDivisorValue_symmPart_reflection (w : ℂ →₀ ℂ) (σ s : ℂ) :
    xiShiftDivisorValue (symmShiftDivisorPart (1 - σ) w) (σ - s) =
      xiShiftDivisorValue (symmShiftDivisorPart (1 - σ) w) s :=
  xiShiftDivisorValue_reflection_fixed
    (reflectShiftDivisor_symmShiftDivisorPart (1 - σ) w) s

/-- The anti-invariant half of any divisor carries a completed-Xi value vanishing at the
reflection centre. -/
theorem xiShiftDivisorValue_antisymmPart_center_eq_zero (w : ℂ →₀ ℂ) (σ : ℂ) :
    xiShiftDivisorValue (antisymmShiftDivisorPart (1 - σ) w) (σ / 2) = 0 :=
  xiShiftDivisorValue_center_eq_zero
    (reflectShiftDivisor_antisymmShiftDivisorPart (1 - σ) w)

/-! ## Central jet parity -/

/-- Every weighted completed-Xi translate family is entire. -/
theorem xiShiftDivisorValue_analyticOnNhd_univ (w : ℂ →₀ ℂ) :
    AnalyticOnNhd ℂ (xiShiftDivisorValue w) Set.univ :=
  shiftDivisorValue_analyticOnNhd_univ xi_analyticOnNhd_univ w

/-- **All-order central jet parity.** For a reflection-eigen divisor with eigenvalue `η`, the
`m`-th derivative of the weighted completed-Xi value vanishes at the centre `σ / 2` whenever
`(-1)^m * η = -1`. -/
theorem iteratedDeriv_xiShiftDivisorValue_center_eq_zero {w : ℂ →₀ ℂ} {σ η : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = η • w) {m : ℕ}
    (hpar : (-1 : ℂ) ^ m * η = -1) :
    (deriv^[m] (xiShiftDivisorValue w)) (σ / 2) = 0 := by
  have hw' : reflectShiftDivisor (2 * (1 / 2 : ℂ) - σ) w = η • w := by
    rw [show 2 * (1 / 2 : ℂ) - σ = 1 - σ by ring]
    exact hw
  have hsym : ∀ s, xiShiftDivisorValue w (2 * (σ / 2) - s) = η * xiShiftDivisorValue w s := by
    intro s
    have h := shiftDivisorValue_center_reflection xi_signed_reflection hw' s
    rw [one_mul] at h
    exact h
  have h := iteratedDeriv_signed_reflection
    (xiShiftDivisorValue_analyticOnNhd_univ w) hsym m (σ / 2)
  rw [show 2 * (σ / 2) - σ / 2 = σ / 2 by ring, hpar] at h
  linear_combination (1 / 2 : ℂ) * h

/-! ## The corrected value and its reflection cocycle -/

/-- Archimedean correction attached to a finite shift divisor. -/
def xiShiftDivisorArchimedeanCorrection (w : ℂ →₀ ℂ) (s : ℂ) : ℂ :=
  shiftDivisorValue w (logDeriv archFactor) s

/-- Corrected completed-Xi prime value of a finite shift divisor. -/
def xiShiftDivisorPrimeValue (w : ℂ →₀ ℂ) (s : ℂ) : ℂ :=
  xiShiftDivisorLogDeriv w s - xiShiftDivisorArchimedeanCorrection w s

/-- Reflection defect of the archimedean correction about `σ / 2`. -/
def xiShiftDivisorReflectionCocycle (w : ℂ →₀ ℂ) (σ s : ℂ) : ℂ :=
  xiShiftDivisorArchimedeanCorrection w s -
    xiShiftDivisorArchimedeanCorrection w (σ - s)

/-- The divisor reflection cocycle is anti-invariant under the coordinate reflection. -/
theorem xiShiftDivisorReflectionCocycle_isAdditiveReflectionCocycle (w : ℂ →₀ ℂ) (σ : ℂ) :
    IsAdditiveReflectionCocycle (fun s : ℂ => σ - s)
      (xiShiftDivisorReflectionCocycle w σ) := by
  intro s
  show xiShiftDivisorArchimedeanCorrection w (σ - s) -
      xiShiftDivisorArchimedeanCorrection w (σ - (σ - s)) =
    -(xiShiftDivisorArchimedeanCorrection w s -
      xiShiftDivisorArchimedeanCorrection w (σ - s))
  rw [show σ - (σ - s) = s by ring]
  ring

/-- The divisor reflection cocycle vanishes at the reflection centre. -/
theorem xiShiftDivisorReflectionCocycle_center (w : ℂ →₀ ℂ) (σ : ℂ) :
    xiShiftDivisorReflectionCocycle w σ (σ / 2) = 0 :=
  IsAdditiveReflectionCocycle.eq_zero_of_fixed
    (xiShiftDivisorReflectionCocycle_isAdditiveReflectionCocycle w σ)
    (show σ - σ / 2 = σ / 2 by ring)

/-- **Universal corrected divisor reflection law.** For an anti-invariant shift divisor the
corrected completed-Xi prime value changes under reflection exactly by the archimedean cocycle.
No order or integrality condition on the shifts enters. -/
theorem xiShiftDivisorPrimeValue_reflection_cocycle {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = -w) (s : ℂ) :
    xiShiftDivisorPrimeValue w (σ - s) =
      xiShiftDivisorPrimeValue w s + xiShiftDivisorReflectionCocycle w σ s := by
  rw [xiShiftDivisorPrimeValue, xiShiftDivisorPrimeValue,
    xiShiftDivisorLogDeriv_reflection_fixed hw s, xiShiftDivisorReflectionCocycle]
  ring

/-- Half-cocycle centering of the corrected divisor value. -/
def xiShiftDivisorCenteredPrimeValue (w : ℂ →₀ ℂ) (σ s : ℂ) : ℂ :=
  xiShiftDivisorPrimeValue w s + (1 / 2 : ℂ) * xiShiftDivisorReflectionCocycle w σ s

/-- **Universal centered divisor reflection law.** Half-cocycle centering makes the corrected
completed-Xi value of every anti-invariant shift divisor exactly fixed by reflection about
`σ / 2`. -/
theorem xiShiftDivisorCenteredPrimeValue_reflection {w : ℂ →₀ ℂ} {σ : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = -w) (s : ℂ) :
    xiShiftDivisorCenteredPrimeValue w σ (σ - s) =
      xiShiftDivisorCenteredPrimeValue w σ s :=
  (add_half_reflection_fixed_iff
    (r := fun s : ℂ => σ - s)
    (f := xiShiftDivisorPrimeValue w)
    (c := xiShiftDivisorReflectionCocycle w σ)
    (xiShiftDivisorReflectionCocycle_isAdditiveReflectionCocycle w σ) s).2
      (xiShiftDivisorPrimeValue_reflection_cocycle hw s)

/-- At the reflection centre the centered corrected value is the corrected value itself. -/
theorem xiShiftDivisorCenteredPrimeValue_center (w : ℂ →₀ ℂ) (σ : ℂ) :
    xiShiftDivisorCenteredPrimeValue w σ (σ / 2) = xiShiftDivisorPrimeValue w (σ / 2) := by
  rw [xiShiftDivisorCenteredPrimeValue, xiShiftDivisorReflectionCocycle_center]
  ring

/-! ## Point and two-point divisors -/

/-- The two-point divisor of an ordered pair of shifts. -/
def pairShiftDivisor (a b : ℂ) : ℂ →₀ ℂ :=
  Finsupp.single a 1 - Finsupp.single b 1

/-- The raw pairwise completed-Xi difference is the value of the two-point divisor. -/
theorem xiPairwiseShiftRawLogDerivDifference_eq_xiShiftDivisorLogDeriv (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b s =
      xiShiftDivisorLogDeriv (pairShiftDivisor a b) s := by
  rw [xiShiftDivisorLogDeriv, pairShiftDivisor, shiftDivisorValue_sub,
    shiftDivisorValue_single, shiftDivisorValue_single,
    xiPairwiseShiftRawLogDerivDifference]
  ring

/-- The two-point divisor is anti-invariant under reflection about the midpoint of its shifts. -/
theorem reflectShiftDivisor_pairShiftDivisor (a b : ℂ) :
    reflectShiftDivisor (a + b) (pairShiftDivisor a b) = -pairShiftDivisor a b := by
  rw [pairShiftDivisor, reflectShiftDivisor_sub, reflectShiftDivisor_single,
    reflectShiftDivisor_single, show a + b - a = b by ring, show a + b - b = a by ring]
  abel

/-- **The two-endpoint reflection law is the two-point divisor instance.** The pairwise coordinate
reflection is the coordinate reflection at `σ = 1 - a - b`, and anti-invariance of the two-point
divisor about `(a + b) / 2` is what makes the value reflection-fixed. -/
theorem xiPairwiseShiftRawLogDerivDifference_reflection_eq_xiShiftDivisorLogDeriv (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b (xiPairwiseShiftReflection a b s) =
      xiShiftDivisorLogDeriv (pairShiftDivisor a b) s := by
  rw [xiPairwiseShiftRawLogDerivDifference_eq_xiShiftDivisorLogDeriv,
    xiPairwiseShiftReflection, show (1 : ℂ) - a - b - s = 1 - a - b - s by ring]
  have hw : reflectShiftDivisor (1 - (1 - a - b)) (pairShiftDivisor a b) =
      -pairShiftDivisor a b := by
    rw [show (1 : ℂ) - (1 - a - b) = a + b by ring]
    exact reflectShiftDivisor_pairShiftDivisor a b
  have h := xiShiftDivisorLogDeriv_reflection_fixed hw s
  rw [show (1 : ℂ) - a - b - s = 1 - a - b - s by ring] at h
  exact h

/-- The one-shift raw completed-Xi defect is the value of a two-point divisor based at `0`. -/
theorem xiTransverseShiftRawLogDerivDefect_eq_xiShiftDivisorLogDeriv (a : ℕ) (s : ℂ) :
    xiTransverseShiftRawLogDerivDefect a s =
      xiShiftDivisorLogDeriv (pairShiftDivisor (a : ℂ) 0) s := by
  rw [xiShiftDivisorLogDeriv, pairShiftDivisor, shiftDivisorValue_sub,
    shiftDivisorValue_single, shiftDivisorValue_single,
    xiTransverseShiftRawLogDerivDefect]
  simp

/-- The pairwise archimedean correction difference is the two-point divisor correction. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_xiShiftDivisorArchimedeanCorrection
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiShiftDivisorArchimedeanCorrection (pairShiftDivisor (a : ℂ) (b : ℂ)) s := by
  rw [xiShiftDivisorArchimedeanCorrection, pairShiftDivisor, shiftDivisorValue_sub,
    shiftDivisorValue_single, shiftDivisorValue_single,
    xiPairwiseShiftArchimedeanCorrectionDifference, xiTransverseShiftArchimedeanCorrection,
    xiTransverseShiftArchimedeanCorrection]
  ring

/-- The corrected pairwise prime difference is the corrected value of the two-point divisor. -/
theorem xiPairwiseShiftPrimeDifference_eq_xiShiftDivisorPrimeValue (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a b s =
      xiShiftDivisorPrimeValue (pairShiftDivisor (a : ℂ) (b : ℂ)) s := by
  rw [xiShiftDivisorPrimeValue,
    ← xiPairwiseShiftArchimedeanCorrectionDifference_eq_xiShiftDivisorArchimedeanCorrection,
    ← xiPairwiseShiftRawLogDerivDifference_eq_xiShiftDivisorLogDeriv,
    xiPairwiseShiftPrimeDifference_eq_raw_sub_correction]

/-- The pairwise reflection cocycle is the two-point divisor cocycle at `σ = 1 - a - b`. -/
theorem xiPairwiseShiftReflectionCocycle_eq_xiShiftDivisorReflectionCocycle (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftReflectionCocycle a b s =
      xiShiftDivisorReflectionCocycle (pairShiftDivisor (a : ℂ) (b : ℂ))
        (1 - (a : ℂ) - (b : ℂ)) s := by
  rw [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_xiShiftDivisorArchimedeanCorrection,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_xiShiftDivisorArchimedeanCorrection,
    xiShiftDivisorReflectionCocycle, xiPairwiseShiftReflection]

/-- The centered pairwise prime difference is the centered corrected value of the two-point
divisor. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_xiShiftDivisorCenteredPrimeValue
    (a b : ℕ) (s : ℂ) :
    xiPairwiseCenteredShiftPrimeDifference a b s =
      xiShiftDivisorCenteredPrimeValue (pairShiftDivisor (a : ℂ) (b : ℂ))
        (1 - (a : ℂ) - (b : ℂ)) s := by
  rw [xiPairwiseCenteredShiftPrimeDifference, xiShiftDivisorCenteredPrimeValue,
    xiPairwiseShiftPrimeDifference_eq_xiShiftDivisorPrimeValue,
    xiPairwiseShiftReflectionCocycle_eq_xiShiftDivisorReflectionCocycle]

end

end RHTower
