import GaloisForLFunctions.RHTower.XiTransverseShiftPrimeDefectValueReflection

/-!
# Pairwise completed-Xi shift cocycle and reflection

For arbitrary complex shifts `a` and `b`, the difference

`logDeriv xi (s+a) - logDeriv xi (s+b)`

is an additive pair-groupoid cocycle. Completed-Xi reciprocity fixes this pairwise difference under
reflection about `(1-a-b)/2`. The previous raw one-shift reflection is the specialization `b=0`.

This is the value-level law behind the rooted incidence matroids of finite even-shift families:
edge reversal is negation and every telescoping cycle is an exact value relation.
-/

namespace RHTower

open Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reflection about the midpoint `(1-a-b)/2` associated to a pair of shifts. -/
def xiPairwiseShiftReflection (a b s : ℂ) : ℂ :=
  1 - a - b - s

@[simp]
theorem xiPairwiseShiftReflection_involutive (a b s : ℂ) :
    xiPairwiseShiftReflection a b (xiPairwiseShiftReflection a b s) = s := by
  simp [xiPairwiseShiftReflection]

/-- Raw logarithmic-derivative difference between two arbitrary complex translates of completed
Xi. -/
def xiPairwiseShiftRawLogDerivDifference (a b s : ℂ) : ℂ :=
  logDeriv xi (s + a) - logDeriv xi (s + b)

@[simp]
theorem xiPairwiseShiftRawLogDerivDifference_self (a s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a a s = 0 := by
  simp [xiPairwiseShiftRawLogDerivDifference]

/-- Reversing an oriented pair negates its completed-Xi value difference. -/
theorem xiPairwiseShiftRawLogDerivDifference_swap (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference b a s =
      -xiPairwiseShiftRawLogDerivDifference a b s := by
  simp [xiPairwiseShiftRawLogDerivDifference]

/-- **Pairwise shift cocycle.** Every two-step translate difference telescopes exactly. -/
theorem xiPairwiseShiftRawLogDerivDifference_cocycle (a b c s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a c s =
      xiPairwiseShiftRawLogDerivDifference a b s +
        xiPairwiseShiftRawLogDerivDifference b c s := by
  simp [xiPairwiseShiftRawLogDerivDifference]

/-- Simultaneously translating both endpoints and translating the observation coordinate back
does not change a raw pairwise completed-Xi value. -/
theorem xiPairwiseShiftRawLogDerivDifference_translationGauge
    (a b c s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference (a + c) (b + c) (s - c) =
      xiPairwiseShiftRawLogDerivDifference a b s := by
  rw [xiPairwiseShiftRawLogDerivDifference,
    xiPairwiseShiftRawLogDerivDifference,
    show s - c + (a + c) = s + a by ring,
    show s - c + (b + c) = s + b by ring]

/-- **Raw relative-shift normal form.** Every complex pairwise completed-Xi value is a zero-tail
value with relative shift `a - b`, observed from the translated coordinate `s + b`. -/
theorem xiPairwiseShiftRawLogDerivDifference_eq_relativeShift
    (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b s =
      xiPairwiseShiftRawLogDerivDifference (a - b) 0 (s + b) := by
  rw [xiPairwiseShiftRawLogDerivDifference,
    xiPairwiseShiftRawLogDerivDifference,
    show s + b + (a - b) = s + a by ring,
    show s + b + 0 = s + b by ring]

/-- The pairwise midpoint reflection is carried to the zero-tail relative-shift reflection by the
same translation gauge. -/
theorem xiPairwiseShiftReflection_relativeShift (a b s : ℂ) :
    xiPairwiseShiftReflection (a - b) 0 (s + b) =
      xiPairwiseShiftReflection a b s + b := by
  unfold xiPairwiseShiftReflection
  ring

/-- **Pairwise completed-Xi reflection law.** The difference between shifts `a` and `b` is fixed
by reflection about `(1-a-b)/2`. -/
theorem xiPairwiseShiftRawLogDerivDifference_reflection (a b s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference a b
        (xiPairwiseShiftReflection a b s) =
      xiPairwiseShiftRawLogDerivDifference a b s := by
  rw [xiPairwiseShiftRawLogDerivDifference, xiPairwiseShiftReflection,
    show 1 - a - b - s + a = 1 - (s + b) by ring,
    show 1 - a - b - s + b = 1 - (s + a) by ring,
    logDeriv_xi_reciprocity, logDeriv_xi_reciprocity]
  simp [xiPairwiseShiftRawLogDerivDifference]
  ring

/-- The existing natural one-shift raw defect is exactly the zero-tail specialization of the
pairwise complex-shift difference. -/
theorem xiPairwiseShiftRawLogDerivDifference_nat_zero
    (a : ℕ) (s : ℂ) :
    xiPairwiseShiftRawLogDerivDifference (a : ℂ) 0 s =
      xiTransverseShiftRawLogDerivDefect a s := by
  simp [xiPairwiseShiftRawLogDerivDifference,
    xiTransverseShiftRawLogDerivDefect]

/-! ## Corrected integral pairwise reflection cocycle -/

/-- Difference of two corrected integral completed-Xi prime defects. This is the pointwise value
carried by the all-integral pairwise source theory. -/
def xiPairwiseShiftPrimeDifference (a b : ℕ) (s : ℂ) : ℂ :=
  xiTransverseShiftPrimeDefect a s - xiTransverseShiftPrimeDefect b s

/-- Difference of the two archimedean corrections attached to an integral shift pair. -/
def xiPairwiseShiftArchimedeanCorrectionDifference (a b : ℕ) (s : ℂ) : ℂ :=
  xiTransverseShiftArchimedeanCorrection a s -
    xiTransverseShiftArchimedeanCorrection b s

/-- Reversing an integral pair negates its archimedean correction difference. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_swap (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftArchimedeanCorrectionDifference b a s =
      -xiPairwiseShiftArchimedeanCorrectionDifference a b s := by
  simp [xiPairwiseShiftArchimedeanCorrectionDifference]

/-- For ordered integral endpoints, the pairwise midpoint reflection is exactly the one-shift
reflection of their relative shift in the translated coordinate. -/
theorem xiPairwiseShiftReflection_eq_transverse_relativeShift_of_le
    (a b : ℕ) (s : ℂ) (hba : b ≤ a) :
    xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s + b =
      xiTransverseShiftReflection (a - b) (s + b) := by
  simp [xiPairwiseShiftReflection, xiTransverseShiftReflection]
  rw [Nat.cast_sub hba]
  ring

/-- The pairwise archimedean correction has the same ordered relative-shift normal form. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le
    (a b : ℕ) (s : ℂ) (hba : b ≤ a) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiTransverseShiftArchimedeanCorrection (a - b) (s + b) := by
  rw [xiPairwiseShiftArchimedeanCorrectionDifference,
    xiTransverseShiftArchimedeanCorrection_eq_forwardDifference,
    xiTransverseShiftArchimedeanCorrection_eq_forwardDifference,
    xiTransverseShiftArchimedeanCorrection_eq_forwardDifference]
  simpa [Nat.cast_sub hba] using
    forwardDifference_sub_forwardDifference
      (logDeriv archFactor) (a : ℂ) (b : ℂ) s

/-- **Unconditional correction normal form.** Every pairwise archimedean correction is one
translated nonnegative relative-shift correction, with orientation recorded only by its sign.
This removes endpoint order from the public correction interface. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      if b ≤ a then xiTransverseShiftArchimedeanCorrection (a - b) (s + b)
      else -xiTransverseShiftArchimedeanCorrection (b - a) (s + a) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le a b s hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba, xiPairwiseShiftArchimedeanCorrectionDifference_swap b a,
      xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le b a s hab]

/-- Corrected pairwise values are raw pairwise completed-Xi differences minus the exact
archimedean correction difference. -/
theorem xiPairwiseShiftPrimeDifference_eq_raw_sub_correction
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a b s =
      xiPairwiseShiftRawLogDerivDifference (a : ℂ) (b : ℂ) s -
        xiPairwiseShiftArchimedeanCorrectionDifference a b s := by
  simp only [xiPairwiseShiftPrimeDifference, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiPairwiseShiftRawLogDerivDifference,
    xiPairwiseShiftArchimedeanCorrectionDifference]
  ring

@[simp]
theorem xiPairwiseShiftPrimeDifference_self (a : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a a s = 0 := by
  simp [xiPairwiseShiftPrimeDifference]

/-- Reversing a corrected integral pair negates its value. -/
theorem xiPairwiseShiftPrimeDifference_swap (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference b a s =
      -xiPairwiseShiftPrimeDifference a b s := by
  simp [xiPairwiseShiftPrimeDifference]

/-- Corrected integral pairwise values retain the exact additive pair-groupoid cocycle. -/
theorem xiPairwiseShiftPrimeDifference_cocycle (a b c : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a c s =
      xiPairwiseShiftPrimeDifference a b s +
        xiPairwiseShiftPrimeDifference b c s := by
  simp [xiPairwiseShiftPrimeDifference]

/-- **Corrected relative-shift normal form.** If `b ≤ a`, the corrected pair value at endpoints
`a,b` is exactly the one-shift prime defect of `a-b` observed at `s+b`. -/
theorem xiPairwiseShiftPrimeDifference_eq_relativeShift_of_le
    (a b : ℕ) (s : ℂ) (hba : b ≤ a) :
    xiPairwiseShiftPrimeDifference a b s =
      xiTransverseShiftPrimeDefect (a - b) (s + b) := by
  rw [xiPairwiseShiftPrimeDifference,
    xiTransverseShiftPrimeDefect_eq_forwardDifference,
    xiTransverseShiftPrimeDefect_eq_forwardDifference,
    xiTransverseShiftPrimeDefect_eq_forwardDifference]
  simpa [Nat.cast_sub hba] using
    forwardDifference_sub_forwardDifference
      (fun z ↦ logDeriv xi z - logDeriv archFactor z)
      (a : ℂ) (b : ℂ) s

/-- **Unconditional oriented relative-shift classifier.** Every corrected integral pair value is
one translated nonnegative relative-shift defect, with the sign determined solely by orientation.
This discharges the endpoint-order hypothesis from the public value interface. -/
theorem xiPairwiseShiftPrimeDifference_eq_relativeShift
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a b s =
      if b ≤ a then xiTransverseShiftPrimeDefect (a - b) (s + b)
      else -xiTransverseShiftPrimeDefect (b - a) (s + a) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiPairwiseShiftPrimeDifference_eq_relativeShift_of_le a b s hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba, xiPairwiseShiftPrimeDifference_swap,
      xiPairwiseShiftPrimeDifference_eq_relativeShift_of_le b a s hab]

/-- Reflection cocycle induced by the pairwise archimedean correction. -/
def xiPairwiseShiftReflectionCocycle (a b : ℕ) (s : ℂ) : ℂ :=
  xiPairwiseShiftArchimedeanCorrectionDifference a b s -
    xiPairwiseShiftArchimedeanCorrectionDifference a b
      (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s)

/-- Reversing the endpoint orientation negates the induced reflection cocycle. -/
theorem xiPairwiseShiftReflectionCocycle_swap (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftReflectionCocycle b a s =
      -xiPairwiseShiftReflectionCocycle a b s := by
  simp only [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference,
    xiPairwiseShiftReflection]
  ring_nf

/-- The pairwise correction cocycle is anti-invariant under its midpoint reflection. -/
theorem xiPairwiseShiftReflectionCocycle_reflection (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftReflectionCocycle a b
        (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) =
      -xiPairwiseShiftReflectionCocycle a b s := by
  rw [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftReflection_involutive]
  ring

/-- The pairwise archimedean cocycle vanishes at its reflection midpoint. -/
theorem xiPairwiseShiftReflectionCocycle_center (a b : ℕ) :
    xiPairwiseShiftReflectionCocycle a b
      ((1 - (a : ℂ) - (b : ℂ)) / 2) = 0 := by
  apply IsAdditiveReflectionCocycle.eq_zero_of_fixed
    (xiPairwiseShiftReflectionCocycle_reflection a b)
  change 1 - (a : ℂ) - (b : ℂ) -
      ((1 - (a : ℂ) - (b : ℂ)) / 2) =
    (1 - (a : ℂ) - (b : ℂ)) / 2
  ring

/-- The pairwise correction cocycle is the translated one-shift cocycle of the relative shift. -/
theorem xiPairwiseShiftReflectionCocycle_eq_relativeShift_of_le
    (a b : ℕ) (s : ℂ) (hba : b ≤ a) :
    xiPairwiseShiftReflectionCocycle a b s =
      xiTransverseShiftReflectionCocycle (a - b) (s + b) := by
  rw [xiPairwiseShiftReflectionCocycle,
    xiTransverseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le
      a b s hba,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le
      a b (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) hba,
    xiPairwiseShiftReflection_eq_transverse_relativeShift_of_le a b s hba]

/-- **Unconditional reflection-cocycle normal form.** Every pairwise correction cocycle is one
translated one-shift cocycle, with the endpoint orientation contributing exactly a sign. -/
theorem xiPairwiseShiftReflectionCocycle_eq_relativeShift
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftReflectionCocycle a b s =
      if b ≤ a then xiTransverseShiftReflectionCocycle (a - b) (s + b)
      else -xiTransverseShiftReflectionCocycle (b - a) (s + a) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiPairwiseShiftReflectionCocycle_eq_relativeShift_of_le a b s hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba, xiPairwiseShiftReflectionCocycle_swap b a,
      xiPairwiseShiftReflectionCocycle_eq_relativeShift_of_le b a s hab]

/-- **Corrected pairwise completed-Xi reflection law.** Reflection changes an integral pairwise
prime defect exactly by its archimedean correction cocycle. -/
theorem xiPairwiseShiftPrimeDifference_reflection_cocycle
    (a b : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a b
        (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) =
      xiPairwiseShiftPrimeDifference a b s +
        xiPairwiseShiftReflectionCocycle a b s := by
  rw [xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftRawLogDerivDifference_reflection,
    xiPairwiseShiftReflectionCocycle]
  ring

/-- Half-cocycle centering of a corrected integral pairwise prime difference. -/
def xiPairwiseCenteredShiftPrimeDifference (a b : ℕ) (s : ℂ) : ℂ :=
  xiPairwiseShiftPrimeDifference a b s +
    (1 / 2 : ℂ) * xiPairwiseShiftReflectionCocycle a b s

/-- Reversing the endpoints negates the half-cocycle-centered pairwise value. -/
theorem xiPairwiseCenteredShiftPrimeDifference_swap (a b : ℕ) (s : ℂ) :
    xiPairwiseCenteredShiftPrimeDifference b a s =
      -xiPairwiseCenteredShiftPrimeDifference a b s := by
  rw [xiPairwiseCenteredShiftPrimeDifference,
    xiPairwiseCenteredShiftPrimeDifference,
    xiPairwiseShiftPrimeDifference_swap,
    xiPairwiseShiftReflectionCocycle_swap]
  ring

/-- **Centered pairwise reflection law.** Half-cocycle centering restores exact reflection
invariance about `(1-a-b)/2` for every integral shift pair. -/
theorem xiPairwiseCenteredShiftPrimeDifference_reflection
    (a b : ℕ) (s : ℂ) :
    xiPairwiseCenteredShiftPrimeDifference a b
        (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) =
      xiPairwiseCenteredShiftPrimeDifference a b s := by
  change xiPairwiseShiftPrimeDifference a b
        (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) +
      (1 / 2 : ℂ) * xiPairwiseShiftReflectionCocycle a b
        (xiPairwiseShiftReflection (a : ℂ) (b : ℂ) s) =
    xiPairwiseShiftPrimeDifference a b s +
      (1 / 2 : ℂ) * xiPairwiseShiftReflectionCocycle a b s
  exact (add_half_reflection_fixed_iff
    (r := xiPairwiseShiftReflection (a : ℂ) (b : ℂ))
    (f := xiPairwiseShiftPrimeDifference a b)
    (c := xiPairwiseShiftReflectionCocycle a b)
    (xiPairwiseShiftReflectionCocycle_reflection a b) s).2
      (xiPairwiseShiftPrimeDifference_reflection_cocycle a b s)

/-- Half-cocycle centering commutes with the ordered relative-shift reduction. Thus the centered
pairwise reflection law contains no analytic degree of freedom beyond the one-shift law. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_relativeShift_of_le
    (a b : ℕ) (s : ℂ) (hba : b ≤ a) :
    xiPairwiseCenteredShiftPrimeDifference a b s =
      xiTransverseCenteredShiftPrimeDefect (a - b) (s + b) := by
  rw [xiPairwiseCenteredShiftPrimeDifference,
    xiTransverseCenteredShiftPrimeDefect,
    xiPairwiseShiftPrimeDifference_eq_relativeShift_of_le a b s hba,
    xiPairwiseShiftReflectionCocycle_eq_relativeShift_of_le a b s hba]

/-- **Unconditional centered-value normal form.** Every centered pairwise Xi prime value is one
translated centered nonnegative relative-shift defect, with orientation recorded exactly by sign.
Thus the full centered two-endpoint reflection theory contains no endpoint-order hypothesis and no
extra analytic degree of freedom beyond the one-shift theory. -/
theorem xiPairwiseCenteredShiftPrimeDifference_eq_relativeShift
    (a b : ℕ) (s : ℂ) :
    xiPairwiseCenteredShiftPrimeDifference a b s =
      if b ≤ a then xiTransverseCenteredShiftPrimeDefect (a - b) (s + b)
      else -xiTransverseCenteredShiftPrimeDefect (b - a) (s + a) := by
  by_cases hba : b ≤ a
  · rw [if_pos hba,
      xiPairwiseCenteredShiftPrimeDifference_eq_relativeShift_of_le a b s hba]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    rw [if_neg hba, xiPairwiseCenteredShiftPrimeDifference_swap b a,
      xiPairwiseCenteredShiftPrimeDifference_eq_relativeShift_of_le b a s hab]

/-- The pairwise corrected value law recovers the existing one-shift prime defect at tail zero. -/
@[simp]
theorem xiPairwiseShiftPrimeDifference_nat_zero (a : ℕ) (s : ℂ) :
    xiPairwiseShiftPrimeDifference a 0 s =
      xiTransverseShiftPrimeDefect a s := by
  simp [xiPairwiseShiftPrimeDifference, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection]

/-- At tail zero the pairwise reflection cocycle is the existing one-shift cocycle. -/
theorem xiPairwiseShiftReflectionCocycle_nat_zero (a : ℕ) (s : ℂ) :
    xiPairwiseShiftReflectionCocycle a 0 s =
      xiTransverseShiftReflectionCocycle a s := by
  simp [xiPairwiseShiftReflectionCocycle,
    xiPairwiseShiftArchimedeanCorrectionDifference,
    xiPairwiseShiftReflection, xiTransverseShiftReflection,
    xiTransverseShiftReflectionCocycle,
    xiTransverseShiftArchimedeanCorrection]

end

end RHTower
