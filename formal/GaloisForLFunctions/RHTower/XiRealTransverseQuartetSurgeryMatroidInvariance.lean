import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw
import GaloisForLFunctions.RHTower.XiRealTransverseShiftDefectDifferentialRank
import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization

/-!
# Real-aperture Xi matroid invariance under off-critical quartet surgery

The compact-open quartet-escape theorem previously controlled integral even
shifts.  The physical Hedenmalm aperture is instead the continuum
`0 < a < 1/2`.  This file closes that mismatch.

For an arbitrary real shift, multiplying completed Xi by a normalized
off-critical quartet changes the corrected logarithmic shift defect by a
rational function of the upper-end coordinate.  Rational base translation
does not change a represented differential matroid.  Hence every quartet
multiplicity, including arbitrarily large Ward charge, has exactly the same
pointed-collision matroid on the entire real aperture line as the actual Xi
prime-source family.
-/

namespace RHTower

open Complex Set
open scoped Differential UpperEndDifferentialInstances

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- The rational logarithmic correction
`q(-iz+h)-q(-iz)` for an arbitrary real transverse shift `h`. -/
def escapingQuartetRealShiftCorrectionRatFunc
    (d : ℝ) (n : ℕ) (h : ℝ) : RatFunc ℂ :=
  let P := normalizedEscapingQuartetPolynomial d n
  let σh := upperEndSpectralSubstitutionPolynomial (h : ℂ)
  let σ0 := upperEndSpectralSubstitutionPolynomial 0
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.derivative.comp σh) /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp σh) -
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.derivative.comp σ0) /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp σ0)

/-- The arbitrary-real-shift quartet correction inside the genuine rational
upper-end coordinate field. -/
def escapingQuartetRealShiftCorrectionCoordinate
    (d : ℝ) (n : ℕ) (h : ℝ) : upperEndRationalCoordinateField :=
  upperEndRatfuncToRationalCoordinateField
    (escapingQuartetRealShiftCorrectionRatFunc d n h)

/-- Corrected completed-Xi real-shift prime carrier after one normalized
quartet surgery. -/
def escapingQuartetRealShiftUpperEndCarrier
    (d : ℝ) (n : ℕ) (h : ℝ) : upperEndMeroField :=
  xiRealTransverseShiftUpperEndCarrier h +
    algebraMap upperEndRationalCoordinateField upperEndMeroField
      (escapingQuartetRealShiftCorrectionCoordinate d n h)

/-- Every real-aperture packet after quartet surgery generates the same
differential field as the actual completed-Xi prime-source packet. -/
theorem escapingQuartetRealShiftUpperEndCarrier_differentialAdjoin_eq_raw
    {A : Type*} (d : ℝ) (n : ℕ) (shift : A → ℝ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun i =>
          escapingQuartetRealShiftUpperEndCarrier d n (shift i)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range fun i =>
          xiRealTransverseShiftUpperEndCarrier (shift i)) := by
  unfold escapingQuartetRealShiftUpperEndCarrier
  simpa using differentialAdjoin_range_affineBase_eq
    (fun i => xiRealTransverseShiftUpperEndCarrier (shift i))
    (fun _ => 1)
    (fun i => escapingQuartetRealShiftCorrectionCoordinate d n (shift i))
    (fun _ => one_ne_zero)

/-- Rational quartet surgery preserves the represented differential matroid
of every arbitrary real-shift family. -/
theorem escapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw
    {A : Type*} (d : ℝ) (n : ℕ) (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => escapingQuartetRealShiftUpperEndCarrier d n (shift i)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiRealTransverseShiftUpperEndCarrier (shift i)) := by
  unfold escapingQuartetRealShiftUpperEndCarrier
  exact differentialFamilyMatroid_addBase_eq _ _

/-- **Continuum quartet-blindness law.**  After an off-critical quartet
surgery, zero real shifts remain loops, repeated shifts remain parallel, and
distinct nonzero shifts remain the only differential directions. -/
theorem
    escapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (d : ℝ) (n : ℕ) (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => escapingQuartetRealShiftUpperEndCarrier d n (shift i)) =
      affinePointedCollisionMatroid shift 0 := by
  rw [escapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw,
    xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision]

/-- Multiplicity-`N` correction for an arbitrary real transverse shift. -/
def multiplicityEscapingQuartetRealShiftCorrectionCoordinate
    (d : ℝ) (N n : ℕ) (h : ℝ) : upperEndRationalCoordinateField :=
  N • escapingQuartetRealShiftCorrectionCoordinate d n h

/-- Corrected real-shift carrier after inserting an escaping quartet with
arbitrary divisor multiplicity `N`. -/
def multiplicityEscapingQuartetRealShiftUpperEndCarrier
    (d : ℝ) (N n : ℕ) (h : ℝ) : upperEndMeroField :=
  xiRealTransverseShiftUpperEndCarrier h +
    algebraMap upperEndRationalCoordinateField upperEndMeroField
      (multiplicityEscapingQuartetRealShiftCorrectionCoordinate d N n h)

/-- Arbitrary inserted divisor multiplicity remains invisible to the complete
real-aperture differential matroid. -/
theorem
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw
    {A : Type*} (d : ℝ) (N n : ℕ) (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i =>
          multiplicityEscapingQuartetRealShiftUpperEndCarrier
            d N n (shift i)) =
      differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i => xiRealTransverseShiftUpperEndCarrier (shift i)) := by
  unfold multiplicityEscapingQuartetRealShiftUpperEndCarrier
  exact differentialFamilyMatroid_addBase_eq _ _

/-- **Unbounded-charge continuum blindness.**  Every Ward-charge level has
the exact pointed-collision matroid of actual Xi on the full real aperture
line. -/
theorem
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (d : ℝ) (N n : ℕ) (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun i =>
          multiplicityEscapingQuartetRealShiftUpperEndCarrier
            d N n (shift i)) =
      affinePointedCollisionMatroid shift 0 := by
  rw [
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw,
    xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision]

/-- Multiplicity correction embedded in the field containing every scalar
Euler valuation layer. -/
def multiplicityEscapingQuartetRealShiftCorrectionAllValuation
    (d : ℝ) (N n : ℕ) (h : ℝ) :
    analyticScalarValuationLayerDifferentialField :=
  ⟨(multiplicityEscapingQuartetRealShiftCorrectionCoordinate d N n h :
      upperEndMeroField),
    IntermediateField.algebraMap_mem
      analyticScalarValuationLayerDifferentialField
      (multiplicityEscapingQuartetRealShiftCorrectionCoordinate d N n h)⟩

/-- Even after every scalar Euler valuation layer is adjoined, arbitrary
quartet charge does not change the real-aperture differential matroid. -/
theorem
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw
    {A : Type*} (d : ℝ) (N n : ℕ) (shift : A → ℝ) :
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i =>
          multiplicityEscapingQuartetRealShiftUpperEndCarrier
            d N n (shift i)) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (fun i => xiRealTransverseShiftUpperEndCarrier (shift i)) := by
  change differentialFamilyMatroid
      (F := analyticScalarValuationLayerDifferentialField)
      (fun i => xiRealTransverseShiftUpperEndCarrier (shift i) +
        algebraMap analyticScalarValuationLayerDifferentialField
          upperEndMeroField
          (multiplicityEscapingQuartetRealShiftCorrectionAllValuation
            d N n (shift i))) = _
  exact differentialFamilyMatroid_addBase_eq _ _

/-! ## Orientation-width visibility versus hypertranscendental blindness -/

/-- Pointwise nonnegativity of the unsquared theta normal current at every
aperture strictly beyond `alpha`.  Unlike a squared divisor index, this
predicate retains the horizontal orientation. -/
def XiThetaNormalOrientationAbove (alpha : ℝ) : Prop :=
  ∀ (a : ℝ) (ha : |a| < 1), alpha < a →
    ∀ b : ℝ, 0 ≤ thetaCuspCenterMixedFourierCurrent a ha b

/-- **Exact normal-orientation width law.**  The unsquared theta normal current
is nonnegative at every aperture beyond `alpha` exactly when `alpha` bounds
the horizontal displacement of every completed-Xi zero. -/
theorem xiThetaNormalOrientationAbove_iff_zeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiThetaNormalOrientationAbove alpha ↔ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro horientation
    apply xiZeroHalfPlaneBound_of_hedenmalmGaussianHankelTailCone
      (tau := 1) one_pos halpha
    intro a ha haalpha
    exact (hedenmalmGaussianHankelCone_at_iff_pointwise one_pos ha).2
      (horientation a ha haalpha)
  · intro hzeros a ha haalpha b
    have haOne : a < 1 := (abs_lt.mp ha).2
    exact thetaCuspCenterMixedFourierCurrent_nonneg_of_halfPlaneBound
      halpha hzeros haalpha haOne b

/-- The same phase transition is the exact projective reflection radius of
the Xi divisor.  Thus the normal current measures a quantitative width, not
merely the endpoint proposition RH. -/
theorem xiThetaNormalOrientationAbove_iff_projectiveReflectionRadius_le
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiThetaNormalOrientationAbove alpha ↔
      xiProjectiveReflectionRadius ≤ alpha := by
  exact (xiThetaNormalOrientationAbove_iff_zeroHalfPlaneBound halpha).trans
    (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha)

/-- No invariant of the complete real-aperture differential matroid can
recover the inserted quartet multiplicity.  All charge levels represent the
same pointed-collision matroid. -/
theorem no_realApertureDifferentialMatroid_quartetMultiplicityClassifier
    {A : Type*} (d : ℝ) (n : ℕ) (shift : A → ℝ) :
    ¬ ∃ charge : Matroid A → ℕ,
      ∀ N : ℕ,
        charge
          (differentialFamilyMatroid
            (F := upperEndRationalCoordinateField)
            (fun i =>
              multiplicityEscapingQuartetRealShiftUpperEndCarrier
                d N n (shift i))) = N := by
  rintro ⟨charge, hcharge⟩
  have hOne := hcharge 1
  have hTwo := hcharge 2
  rw [
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
      d 1 n shift] at hOne
  rw [
    multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision
      d 2 n shift] at hTwo
  omega

/-- The source-marked Ward boundary does recover the integer quartet charge:
its exact mass is injective in the multiplicity. -/
theorem multiplicityEscapingQuartetWardMass_injective
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Function.Injective
      (fun N : ℕ => multiplicityEscapingQuartetWardMass d N n) := by
  intro N M hmass
  dsimp only at hmass
  rw [multiplicityEscapingQuartetWardMass_eq hd,
    multiplicityEscapingQuartetWardMass_eq hd] at hmass
  have hquantumPos :
      0 < ENNReal.ofReal (8 * Real.pi) :=
    ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hreal := congrArg ENNReal.toReal hmass
  simp only [nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at hreal
  have hquantumReal :
      (ENNReal.ofReal (8 * Real.pi)).toReal = 8 * Real.pi :=
    ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  rw [hquantumReal] at hreal
  have hcast : (N : ℝ) = (M : ℝ) := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hcast

/-- **Orientation-boundary fracture.**  The unsquared theta current exactly
detects the horizontal Xi divisor width.  In contrast, arbitrary inserted
Ward charge is invisible to the complete continuum aperture differential
matroid, while its source-marked boundary mass remains an injective charge
coordinate. -/
theorem xiOrientationBoundary_fracture_law
    {A : Type*} {alpha d : ℝ} (halpha : 0 ≤ alpha) (hd : 0 < d)
    (n : ℕ) (shift : A → ℝ) :
    (XiThetaNormalOrientationAbove alpha ↔
      xiProjectiveReflectionRadius ≤ alpha) ∧
    (¬ ∃ charge : Matroid A → ℕ,
      ∀ N : ℕ,
        charge
          (differentialFamilyMatroid
            (F := upperEndRationalCoordinateField)
            (fun i =>
              multiplicityEscapingQuartetRealShiftUpperEndCarrier
                d N n (shift i))) = N) ∧
    Function.Injective
      (fun N : ℕ => multiplicityEscapingQuartetWardMass d N n) := by
  exact ⟨
    xiThetaNormalOrientationAbove_iff_projectiveReflectionRadius_le halpha,
    no_realApertureDifferentialMatroid_quartetMultiplicityClassifier d n shift,
    multiplicityEscapingQuartetWardMass_injective hd n⟩

/-- **Orientation-carrier fracture universality.**  The correct-polarity
theta current measures the exact horizontal divisor width.  Its natural
positive source-core Hilbert extension cannot have the one-dimensional
theta kernel as its exact radical.  Meanwhile the canonical unsquared
Julia defect is nonnegative at every nonnegative aperture and its first
Euler-edge variation is the Ward density.  Thus unsquaring preserves
orientation but does not choose its polarity: the positive Julia
polarization counts the charge which the continuum differential matroid
cannot see. -/
theorem xiOrientationCarrier_fracture_universality
    {A : Type*} {alpha d : ℝ} (halpha : 0 ≤ alpha) (hd : 0 < d)
    (n : ℕ) (shift : A → ℝ) :
    ((XiThetaNormalOrientationAbove alpha ↔
        xiProjectiveReflectionRadius ≤ alpha) ∧
      (¬ ∃ charge : Matroid A → ℕ,
        ∀ N : ℕ,
          charge
            (differentialFamilyMatroid
              (F := upperEndRationalCoordinateField)
              (fun i =>
                multiplicityEscapingQuartetRealShiftUpperEndCarrier
                  d N n (shift i))) = N) ∧
      Function.Injective
        (fun N : ℕ => multiplicityEscapingQuartetWardMass d N n)) ∧
    (¬ ∃ Q : SchwartzMap.ContinuousSchwartzSesquilinearForm,
      Q.MomentumSymmetric ∧
      Q.IsNonnegative ∧
      Q xiThetaSchwartzSource xiThetaSchwartzSource = 0 ∧
      Q.leftRadical = xiThetaSchwartzSourceLine ∧
      ∃ u v : SchwartzMap ℝ ℂ, Q u v ≠ 0) ∧
    (∀ (w : ℂ), 0 < w.re →
      ∀ a : ℝ, 0 ≤ a → 0 ≤ xiWardBoundaryPhaseDefect w a) ∧
    (∀ t : ℝ,
      HasDerivAt
        (xiWardBoundaryPhaseDefect
          ((1 / 2 : ℂ) + I * (t : ℂ)))
        (xiWardInfinitesimalDefectDensity t) 0) := by
  exact ⟨
    xiOrientationBoundary_fracture_law halpha hd n shift,
    not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical,
    fun w hw a ha => xiWardBoundaryPhaseDefect_nonneg hw ha,
    hasDerivAt_xiWardBoundaryPhaseDefect_eulerEdge_zero⟩

end

end RHTower
