import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectedContinuousDeficiency
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOppositeShiftParityHarmonicRecovery
import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectiveDefectBoundary

/-!
# Suzuki's one-sided Carleman exterior seam

Suzuki's 2023 identity for the screw kernel is explicitly a one-sided transform on the positive
half-line.  Section 8.3 of the 2026 source treats the same odd meromorphic function as though it
were the bilateral Fourier transform of the real even screw kernel.  That reading is impossible:
the zero-shift Xi multiplier is odd, while a genuine bilateral transform of an even kernel would
be even.

Cutting a convolution by a compact source produces two triangular corrections.  After
meromorphic continuation the right and left Carleman sheets have opposite Xi multipliers:

`right = M W - TRight`,  `left = -M W - TLeft`.

Their sum is therefore the negative compact interval part `-(TRight+TLeft)` and loses every Xi
pole identically.  Their difference retains `2 M W`.  Thus a bilateral exterior sum is not an RH
carrier.  The correct source object is one Carleman sheet.  Its continuation from the initial
upper convergence half-plane through all of the upper half-plane is equivalent to RH once the
Suzuki characteristic and triangular correction are identified.

This file proves the dependency-closed algebraic seam, the exact shifted reflection law, a parity
no-go for the false bilateral reading, and the upper-sheet RH criterion.  The physical Fubini
identity identifying `TRight` and `TLeft` with the two convolution triangles is proved on paper;
half-line Fourier--Carleman integration is not represented in the current Lean tree.

Coordinate warning: abstract `M` can be Suzuki's physical multiplier.  The source-semantic
specialization `suzukiShiftedXiMultiplier eta` instead uses the Xi-real normalized multiplier.
`SuzukiCarlemanCoordinatePhase` proves that its interval argument is `-I` times the physical
triangle and that exact real form shift maps to `eta=-I*lambda/2`.

No estimate, numerical computation, RH assumption, or unproved positivity premise is used.
-/

open Complex GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Abstract two-sheet algebra -/

/-- Meromorphic continuation of the positive-half-line exterior sheet. -/
def suzukiCarlemanRightSheet
    (M W rightTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  M z * W z - rightTriangle z

/-- Meromorphic continuation of the negative-half-line exterior sheet when the arithmetic
one-sided multiplier is odd. -/
def suzukiCarlemanLeftSheet
    (M W leftTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  -M z * W z - leftTriangle z

/-- The compact interval contribution is the sum of the two convolution triangles. -/
def suzukiCarlemanInteriorPart
    (rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  rightTriangle z + leftTriangle z

/-- The two opposite Carleman multipliers cancel in the bilateral sheet sum. -/
theorem suzukiCarlemanSheet_sum
    (M W rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiCarlemanRightSheet M W rightTriangle z +
        suzukiCarlemanLeftSheet M W leftTriangle z =
      -suzukiCarlemanInteriorPart rightTriangle leftTriangle z := by
  simp only [suzukiCarlemanRightSheet, suzukiCarlemanLeftSheet,
    suzukiCarlemanInteriorPart]
  ring

/-- The sheet difference, not the sheet sum, retains the meromorphic arithmetic multiplier. -/
theorem suzukiCarlemanSheet_difference
    (M W rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiCarlemanRightSheet M W rightTriangle z -
        suzukiCarlemanLeftSheet M W leftTriangle z =
      2 * M z * W z - (rightTriangle z - leftTriangle z) := by
  simp only [suzukiCarlemanRightSheet, suzukiCarlemanLeftSheet]
  ring

/-! ## Exact Xi-sheet reflection -/

/-- The zero-shift meromorphic Carleman multiplier is odd. -/
theorem suzukiZeroShiftMultiplier_odd :
    Function.Odd (suzukiShiftedXiMultiplier 0) := by
  intro z
  simp only [suzukiShiftedXiMultiplier]
  rw [suzukiShiftedXiTarget_neg]
  simp

/-- Reflection of one shifted sheet exchanges the opposite shift and contributes a minus sign. -/
theorem suzukiShiftedXiMultiplier_neg (eta z : ℂ) :
    suzukiShiftedXiMultiplier eta (-z) =
      -suzukiShiftedXiMultiplier (-eta) z := by
  simp only [suzukiShiftedXiMultiplier]
  rw [suzukiShiftedXiTarget_neg]
  simp

/-- The left sheet written directly as the reflected one-sided multiplier. -/
def suzukiReflectedCarlemanLeftSheet
    (eta : ℂ) (W leftTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiShiftedXiMultiplier eta (-z) * W z - leftTriangle z

theorem suzukiReflectedCarlemanLeftSheet_eq_opposite
    (eta : ℂ) (W leftTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiReflectedCarlemanLeftSheet eta W leftTriangle z =
      -suzukiShiftedXiMultiplier (-eta) z * W z - leftTriangle z := by
  rw [suzukiReflectedCarlemanLeftSheet, suzukiShiftedXiMultiplier_neg]

/-- At zero shift, reflected left and right sheets sum to the negative compact interval part. -/
theorem suzukiZeroShiftCarlemanSheet_sum
    (W rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiCarlemanRightSheet (suzukiShiftedXiMultiplier 0) W rightTriangle z +
        suzukiReflectedCarlemanLeftSheet 0 W leftTriangle z =
      -suzukiCarlemanInteriorPart rightTriangle leftTriangle z := by
  rw [suzukiCarlemanRightSheet, suzukiReflectedCarlemanLeftSheet,
    suzukiZeroShiftMultiplier_odd z]
  simp only [suzukiCarlemanInteriorPart]
  ring

/-! ## Parity falsification of the bilateral-multiplier reading -/

/-- Product of the odd zero-shift multiplier and odd phase-one Suzuki characteristic is even. -/
def suzukiZeroShiftBilateralMultiplierChannel
    (A E : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiShiftedXiMultiplier 0 z * suzukiCharacteristicPencil A E 1 z

theorem suzukiZeroShiftBilateralMultiplierChannel_even
    {A E : ℂ → ℂ} (hpar : SuzukiParityPair A E) :
    Function.Even (suzukiZeroShiftBilateralMultiplierChannel A E) := by
  intro z
  rw [suzukiZeroShiftBilateralMultiplierChannel,
    suzukiZeroShiftBilateralMultiplierChannel,
    suzukiZeroShiftMultiplier_odd z,
    suzukiCharacteristicPencil_one_odd hpar z]
  ring

/-- The correctly projected phase-one interval sine clock is odd. -/
theorem suzukiProjectedSineClock_odd (a : ℝ) (A : ℂ) :
    Function.Odd (suzukiProjectedSineClock a A) := by
  intro z
  simp only [suzukiProjectedSineClock]
  rw [show (a : ℂ) * -z = -((a : ℂ) * z) by ring, Complex.sin_neg]
  ring

/-- **Bilateral source no-go.**  A nonzero projected sine clock cannot equal the proposed global
bilateral multiplier channel: the former is odd and the latter even.  This is the formal parity
certificate that Suzuki's one-sided transform cannot be used as one bilateral Fourier
multiplier. -/
theorem suzukiZeroShiftBilateralMultiplierChannel_ne_projectedSineClock
    {A E : ℂ → ℂ} (hpar : SuzukiParityPair A E)
    {a : ℝ} (ha : a ≠ 0) {endpointSum : ℂ} (hendpoint : endpointSum ≠ 0) :
    suzukiZeroShiftBilateralMultiplierChannel A E ≠
      suzukiProjectedSineClock a endpointSum := by
  intro heq
  have heven := suzukiZeroShiftBilateralMultiplierChannel_even hpar I
  have hodd := suzukiProjectedSineClock_odd a endpointSum I
  have hpos := congrFun heq I
  have hneg := congrFun heq (-I)
  have hzero : suzukiProjectedSineClock a endpointSum I = 0 := by
    linear_combination (hodd + hneg - heven - hpos) / 2
  exact suzukiProjectedSineClock_ne_zero_of_im_ne_zero ha hendpoint (by norm_num) hzero

/-! ## Correct one-sheet RH frontier -/

/-- Source-semantic name for the right Carleman sheet. -/
def suzukiRightCarlemanExterior
    (eta : ℂ) (W rightTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiShiftedXiMultiplier eta z * W z - rightTriangle z

theorem suzukiRightCarlemanExterior_eq_exteriorRemainder
    (eta : ℂ) (W rightTriangle : ℂ → ℂ) :
    suzukiRightCarlemanExterior eta W rightTriangle =
      suzukiExteriorRemainder eta W rightTriangle := by
  rfl

/-- **Upper-sheet RH criterion.**  Once the right convolution triangle is identified with an
entire function and one all-angle Suzuki characteristic is used, continuation of this one
Carleman sheet through the complete upper half-plane is equivalent to RH.  Lower-half-plane zeros
are excluded by centered Xi evenness; no bilateral exterior premise is needed. -/
theorem riemannHypothesis_iff_suzukiRightCarlemanExterior_analytic_upper
    {A E rightTriangle : ℂ → ℂ} {eta u : ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hE : ∀ z, AnalyticAt ℂ E z)
    (hT : ∀ z, AnalyticAt ℂ rightTriangle z)
    (hreal : SuzukiAllAngleRealZeros A E) (hu : ‖u‖ = 1) :
    RiemannHypothesis ↔
      ∀ z : ℂ, 0 < z.im →
        AnalyticAt ℂ
          (suzukiRightCarlemanExterior eta
            (suzukiCharacteristicPencil A E u) rightTriangle) z := by
  constructor
  · intro hRH z hz
    rw [suzukiRightCarlemanExterior_eq_exteriorRemainder]
    exact (riemannHypothesis_iff_suzukiExteriorRemainder_analytic_offReal
      hA hE hT hreal hu).mp hRH z (ne_of_gt hz)
  · intro han
    have hnoUpper : ∀ z : ℂ, 0 < z.im → XiC z ≠ 0 := by
      intro z hzIm hzero
      have hW : AnalyticAt ℂ (suzukiCharacteristicPencil A E u) z :=
        (hA z).add (analyticAt_const.mul (hE z))
      have hW0 : suzukiCharacteristicPencil A E u z ≠ 0 :=
        suzukiCharacteristicPencil_ne_zero_of_im_ne_zero hreal hu (ne_of_gt hzIm)
      have hpole := meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one
        (eta := eta) (W := suzukiCharacteristicPencil A E u)
        (intervalPart := rightTriangle) hzero hW hW0 (hT z)
      have hnonneg : (0 : WithTop ℤ) ≤
          meromorphicOrderAt
            (suzukiExteriorRemainder eta
              (suzukiCharacteristicPencil A E u) rightTriangle) z := by
        rw [← suzukiRightCarlemanExterior_eq_exteriorRemainder]
        exact (han z hzIm).meromorphicOrderAt_nonneg
      rw [hpole] at hnonneg
      have hnot : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) := by
        exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
      exact hnot hnonneg
    rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
    intro z hzero
    by_contra hzIm
    rcases lt_or_gt_of_ne hzIm with hzNeg | hzPos
    · have hnegZero : XiC (-z) = 0 := by simpa [XiC_even] using hzero
      exact hnoUpper (-z) (by simpa using neg_pos.mpr hzNeg) hnegZero
    · exact hnoUpper z hzPos hzero

end

end RHTower
