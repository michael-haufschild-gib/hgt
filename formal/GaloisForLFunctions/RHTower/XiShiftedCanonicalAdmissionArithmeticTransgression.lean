import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionBilinearContactSource

/-!
# Source-first arithmetic transgression between shifted-Xi admissions

The completed adaptive source is a quadratic function of its admitted amplitude.  Polarizing that
quadratic *before* rational--Gamma and von Mangoldt aggregation gives an exact comparison between
a current canonical admission and any frozen amplitude.

For the literal completed source `Q_w` and its literal bilinear polarization `B_w`, define

`T_w(P,A) = 2 B_w(P,A-P) + Q_w(A-P)`.

Then

`Q_w(A) = Q_w(P) + T_w(P,A)`.

The comparison is therefore source-native and admission-sensitive: both `B_w` and `Q_w` are
formed from the adaptive mixed packet before reflection aggregation.  It is not an orientation map
or a fixed linear reporter.

The stronger structural conclusion is that fixed-mass admission transport is exact:

`T_w(A,B) + T_w(B,C) = T_w(A,C)`.

Thus the apparent frozen/current "shape holonomy" has zero curvature while source mass is held
fixed.  Any genuine obstruction must be mixed mass--admission curvature.  For actual canonical
admissions, a negative frozen completed packet is equivalent to this arithmetic transgression
overcoming the full positive current Jacobi energy.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- On the diagonal, the literal bilinear rational--Gamma/von Mangoldt source is exactly the
completed adaptive mixed source. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A A =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw,
    ← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw A]
  have hpoly :
      xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A =
        xiShiftedBoundaryAdaptiveShearPolynomial A +
          xiShiftedBoundaryAdaptiveShearPolynomial A := by
    simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
      xiShiftedBoundaryAdaptiveShearPolynomial]
  rw [hpoly, HTGeometry.momentFunctional_add]
  simp only [HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial]
  ring

/-- Literal arithmetic formation is additive in its first amplitude before aggregation. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_left
    {w : ℝ} (hw : 1 / 2 < w) (A B C : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w (A + B) C =
      xiShiftedAdaptiveBilinearCompletedArithmeticSource w A C +
        xiShiftedAdaptiveBilinearCompletedArithmeticSource w B C := by
  simp only [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw]
  have hpoly :
      xiShiftedBoundaryAdaptiveBilinearShearPolynomial (A + B) C =
        xiShiftedBoundaryAdaptiveBilinearShearPolynomial A C +
          xiShiftedBoundaryAdaptiveBilinearShearPolynomial B C := by
    simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
      xiShiftedBoundaryShiftedEuler, Polynomial.derivative_add]
    ring
  rw [hpoly, HTGeometry.momentFunctional_add]

/-- Literal arithmetic formation is additive in its second amplitude before aggregation. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_right
    {w : ℝ} (hw : 1 / 2 < w) (A B C : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A (B + C) =
      xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B +
        xiShiftedAdaptiveBilinearCompletedArithmeticSource w A C := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm w A (B + C),
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_left hw,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm w B A,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm w C A]

/-- **Source-first admission decomposition.**  The completed source of `A` is the source of an
admitted base `P`, twice their literal mixed arithmetic formation, and the source energy of the
admission defect. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_admission_decomposition
    {w : ℝ} (hw : 1 / 2 < w) (P A : Polynomial ℝ) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w A =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w P +
        2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w P (A - P) +
        xiShiftedAdaptiveMixedCompletedArithmeticSource w (A - P) := by
  rw [← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw A,
    ← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw P,
    ← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw (A - P)]
  have hA : A = P + (A - P) := by ring
  conv_lhs => rw [hA]
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_left hw,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_right hw,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_add_right hw,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_comm w (A - P) P]
  ring

/-- Literal source difference generated by moving the admitted amplitude from `P` to `A` at fixed
source mass `w`.  Both summands are adaptive arithmetic sources formed before reflection. -/
def xiShiftedAdaptiveArithmeticAdmissionTransgression
    (w : ℝ) (P A : Polynomial ℝ) : ℝ :=
  2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w P (A - P) +
    xiShiftedAdaptiveMixedCompletedArithmeticSource w (A - P)

/-- The source-first transgression is exactly the endpoint difference of completed arithmetic
sources. -/
theorem xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub
    {w : ℝ} (hw : 1 / 2 < w) (P A : Polynomial ℝ) :
    xiShiftedAdaptiveArithmeticAdmissionTransgression w P A =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w A -
        xiShiftedAdaptiveMixedCompletedArithmeticSource w P := by
  have hsplit :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_admission_decomposition hw P A
  unfold xiShiftedAdaptiveArithmeticAdmissionTransgression
  linarith

/-- Fixed-source admission transgression vanishes on the diagonal. -/
theorem xiShiftedAdaptiveArithmeticAdmissionTransgression_self
    {w : ℝ} (hw : 1 / 2 < w) (A : Polynomial ℝ) :
    xiShiftedAdaptiveArithmeticAdmissionTransgression w A A = 0 := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw]
  ring

/-- **Exact admission cocycle law.**  Fixed-mass source transport is path-independent. -/
theorem xiShiftedAdaptiveArithmeticAdmissionTransgression_trans
    {w : ℝ} (hw : 1 / 2 < w) (A B C : Polynomial ℝ) :
    xiShiftedAdaptiveArithmeticAdmissionTransgression w A B +
        xiShiftedAdaptiveArithmeticAdmissionTransgression w B C =
      xiShiftedAdaptiveArithmeticAdmissionTransgression w A C := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw]
  ring

/-- Reversing admission transport reverses its literal arithmetic transgression. -/
theorem xiShiftedAdaptiveArithmeticAdmissionTransgression_antisymm
    {w : ℝ} (hw : 1 / 2 < w) (A B : Polynomial ℝ) :
    xiShiftedAdaptiveArithmeticAdmissionTransgression w A B =
      -xiShiftedAdaptiveArithmeticAdmissionTransgression w B A := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw]
  ring

/-- **Mixed mass--admission rectangle law.**  The only curvature left after fixed-mass exactness is
the failure of source-mass change to be independent of admitted amplitude. -/
theorem xiShiftedAdaptiveArithmeticAdmissionTransgression_mass_rectangle
    {w v : ℝ} (hw : 1 / 2 < w) (hv : 1 / 2 < v)
    (P A : Polynomial ℝ) :
    xiShiftedAdaptiveArithmeticAdmissionTransgression w P A -
        xiShiftedAdaptiveArithmeticAdmissionTransgression v P A =
      (xiShiftedAdaptiveMixedCompletedArithmeticSource w A -
          xiShiftedAdaptiveMixedCompletedArithmeticSource v A) -
        (xiShiftedAdaptiveMixedCompletedArithmeticSource w P -
          xiShiftedAdaptiveMixedCompletedArithmeticSource v P) := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw,
    xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hv]
  ring

/-- A negative frozen source is exactly a transgression debt exceeding the current source. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_neg_iff_transgression_lt
    {w : ℝ} (hw : 1 / 2 < w) (P A : Polynomial ℝ) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w A < 0 ↔
      xiShiftedAdaptiveArithmeticAdmissionTransgression w P A <
        -xiShiftedAdaptiveMixedCompletedArithmeticSource w P := by
  rw [xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub hw]
  constructor <;> intro h <;> linarith

/-- Two-mass specialization: source is formed at current mass `w`, while the amplitude was
canonically admitted at frozen mass `a`. -/
def xiShiftedCanonicalFrozenCurrentArithmeticTransgression
    (w a : ℝ) (n : ℕ) : ℝ :=
  xiShiftedAdaptiveArithmeticAdmissionTransgression w
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence a) n)

/-- No arithmetic admission debt is created when frozen and current mass coincide. -/
theorem xiShiftedCanonicalFrozenCurrentArithmeticTransgression_self
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalFrozenCurrentArithmeticTransgression w w n = 0 := by
  unfold xiShiftedCanonicalFrozenCurrentArithmeticTransgression
  exact xiShiftedAdaptiveArithmeticAdmissionTransgression_self hw _

/-- **Frozen/current completed `P^sharp` law.**  In a current positive chamber, the completed
adaptive packet of the admission frozen at `a` is current positive Jacobi energy plus the literal
mixed arithmetic transgression from current admission to frozen admission. -/
theorem xiShiftedCompletedMomentAggregate_frozenAdmission_eq_currentJacobiEnergy_add_transgression
    {w : ℝ} (hw : 1 / 2 < w) (a : ℝ) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence a) n))) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
          HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n +
        xiShiftedCanonicalFrozenCurrentArithmeticTransgression w a n := by
  rw [xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw,
    xiShiftedAdaptiveMixedCompletedArithmeticSource_admission_decomposition hw
      (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
      (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence a) n),
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH]
  unfold xiShiftedCanonicalFrozenCurrentArithmeticTransgression
    xiShiftedAdaptiveArithmeticAdmissionTransgression
  ring

/-- **Exact frozen/current obstruction.**  A frozen completed packet is negative at a current
positive mass if and only if the admission transgression pays more than the entire positive current
Jacobi source. -/
theorem xiShiftedCompletedMomentAggregate_frozenAdmission_neg_iff_transgression_lt_neg_currentEnergy
    {w : ℝ} (hw : 1 / 2 < w) (a : ℝ) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    xiShiftedCompletedMomentAggregate (w ^ 2) 2
        (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
          (xiShiftedOddCrossingCoefficientPacket
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence a) n))) < 0 ↔
      xiShiftedCanonicalFrozenCurrentArithmeticTransgression w a n <
        -(2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
          HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedCompletedMomentAggregate_frozenAdmission_eq_currentJacobiEnergy_add_transgression
    hw a hn hH]
  constructor <;> intro h <;> linarith

end

end RHTower
