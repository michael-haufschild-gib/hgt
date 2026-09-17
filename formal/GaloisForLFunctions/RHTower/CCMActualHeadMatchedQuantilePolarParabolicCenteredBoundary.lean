import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceBoundary

/-!
# Barycentrically centered source boundary for the literal parabolic codiagonal

The literal matched--quantile parabolic codiagonal is mass-neutral.  Its unshifted source
boundary has strictly positive mass, but also a first moment, so its source pairing contains both
the completed error--debt coordinate and a visible first-moment term.  That extra term is a
coordinate effect, not an independent arithmetic channel.

This module applies one common parabolic null translation to the actual codiagonal and the actual
matched-plus-quantile source boundary.  The shift is fixed by the boundary's own barycenter; no
external marker, fitted coefficient, or cellwise modification is introduced.  It preserves the
complete strict cross-cell transport exactly, centers the boundary, and makes the preserved
cross-current equal to the positive boundary mass times one centered codiagonal charge.

The result is an exact pre-scalar producer.  It proves neither a sign nor a cofinal bound: the
remaining RH-bearing task is control of this displayed globally coupled charge with its complete
prime--polar displacement debt still present.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The finite physical head always has positive literal critical-Mellin mass: its first cell is
the prime `2`. -/
theorem ccmActualHeadParabolicMass_pos (K : ℕ) :
    0 < ccmActualHeadParabolicMass K := by
  unfold ccmActualHeadParabolicMass
  have hmem : 0 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have htwo : 0 < criticalMellinAtomWeight (0 + 2) := by
    norm_num
    exact criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  apply lt_of_lt_of_le htwo
  exact Finset.single_le_sum (s := Finset.range (K + 1))
    (f := fun n => criticalMellinAtomWeight (n + 2))
    (fun n _ => criticalMellinAtomWeight_nonneg (n + 2)) hmem

/-- The unique common null translation which puts the literal source boundary at zero first
moment. -/
def ccmActualHeadMatchedQuantileParabolicCenteredShift (K : ℕ) : ℝ :=
  -ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 /
    ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0

/-- Source boundary in its canonical finite-head barycentric parabolic gauge. -/
def ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary
    (K : ℕ) : Fin 3 → ℝ :=
  ccmParabolicShift (ccmActualHeadMatchedQuantileParabolicCenteredShift K)
    (ccmActualHeadMatchedQuantileParabolicSourceBoundary K)

/-- Literal matched--quantile codiagonal in the same canonical source gauge. -/
def ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal
    (K : ℕ) : Fin 3 → ℝ :=
  ccmParabolicShift (ccmActualHeadMatchedQuantileParabolicCenteredShift K)
    (ccmActualHeadMatchedQuantileParabolicCodiagonal K)

/-- The centered codiagonal's second coordinate: the canonical source-relative global charge. -/
def ccmActualHeadMatchedQuantileParabolicCenteredCharge (K : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K 2

theorem ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero_pos (K : ℕ) :
    0 < ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0 := by
  rw [ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero]
  nlinarith [ccmActualHeadParabolicMass_pos K]

/-- Centering leaves the source boundary's physical mass unchanged. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary_zero (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K 0 =
      2 * ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary]
  simp [ccmParabolicShift,
    ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero]

/-- This is the exact barycentric centering law; division is legal because the physical prime
head contains the positive atom at `2`. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary_one (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K 1 = 0 := by
  change (-ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 /
      ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0) *
        ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0 +
      ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 = 0
  have hne : ccmActualHeadMatchedQuantileParabolicSourceBoundary K 0 ≠ 0 :=
    (ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero_pos K).ne'
  field_simp
  ring

/-- Common parabolic null translation preserves the full Lorentz pairing, not only a diagonal
or scalarized part of it. -/
theorem ccmParabolicPairing_shift_same (d : ℝ) (v w : Fin 3 → ℝ) :
    ccmParabolicPairing (ccmParabolicShift d v) (ccmParabolicShift d w) =
      ccmParabolicPairing v w := by
  rw [ccmParabolicPairing_shift]
  ring

/-- The common gauge preserves the literal source-boundary parabolic form. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary_form (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K) =
      ccmParabolicForm (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) := by
  rw [ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary,
    ccmParabolicForm_shift]

/-- The codiagonal remains mass-neutral after the common source centering. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal_zero (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K 0 = 0 := by
  change ccmActualHeadMatchedQuantileParabolicCodiagonal K 0 = 0
  exact ccmActualHeadMatchedQuantileParabolicCodiagonal_zero K

/-- The centered charge retains the raw literal error--debt coordinate and adds exactly the
forced barycentric first-moment correction. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredCharge_eq (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredCharge K =
      ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 +
        ccmActualHeadMatchedQuantileParabolicCenteredShift K *
          ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 := by
  change ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K 2 = _
  change ccmActualHeadMatchedQuantileParabolicCenteredShift K ^ 2 / 2 *
      ccmActualHeadMatchedQuantileParabolicCodiagonal K 0 +
      ccmActualHeadMatchedQuantileParabolicCenteredShift K *
        ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 +
      ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 = _
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_zero]
  ring

/-- In the centered source gauge, the boundary pairing is exactly mass times the one global
centered charge. -/
theorem ccmActualHeadMatchedQuantileParabolicCentered_pairing (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K) =
      2 * ccmActualHeadParabolicMass K *
        ccmActualHeadMatchedQuantileParabolicCenteredCharge K := by
  change ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K) =
    2 * ccmActualHeadParabolicMass K *
      ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K 2
  rw [ccmParabolicPairing_massNeutral
      (ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal_zero K),
    ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary_zero,
    ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary_one]
  ring

/-- **Centered strict-cross producer.** The complete ordered strict cross-cell transport,
including every signed displacement--moment term and every quadratic displacement debt, is
exactly the finite source mass times the one centered charge. -/
theorem two_mul_ccmActualHeadParabolicMass_mul_centeredCharge_eq_crossKernel
    (K : ℕ) :
    2 * ccmActualHeadParabolicMass K *
        ccmActualHeadMatchedQuantileParabolicCenteredCharge K =
      ∑ m ∈ Finset.range (K + 1), ∑ n ∈ (Finset.range (K + 1)).erase m,
        (-(ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) *
          (ccmActualHeadMatchedParabolicMoment (m + 2) 0 *
              ccmActualHeadMatchedParabolicMoment (n + 2) 1 -
            ccmActualHeadMatchedParabolicMoment (m + 2) 1 *
              ccmActualHeadMatchedParabolicMoment (n + 2) 0) -
        (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)) ^ 2 / 2 *
          (criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2))) := by
  rw [← ccmActualHeadMatchedQuantileParabolicCentered_pairing]
  rw [ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal,
    ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary,
    ccmParabolicPairing_shift_same,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_crossKernel]

end RHTower
