import GaloisForLFunctions.RHTower.XiResolventRationalNodeCriterion
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionBilinearContactSource

/-!
# Nodal adaptive arithmetic source landing

A polynomial weight `p` selects its own division-free degree-one successor

`Q = L(p²) • (X p) - L(p X p) • p`.

The successor is orthogonal to `p`; its mixed crossing `L(p X Q)` is exactly the weighted
Turán determinant. At square mass this crossing is the literal rational–Gamma-minus-von-Mangoldt
completed packet formed from `(p,Q)` before reflection aggregation. Differentiating moving
admission retains both terms: completed bilinear arithmetic source and exact admission connection.

For nodal weights, and even for the countable rational-node subfamily, nonnegativity of these
arithmetic landings is equivalent to RH. This does not prove their signs.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Zeroth moment of the source reweighted by `p²`. -/
def xiShiftedPolynomialWeightedMass (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment y k).re) p p

/-- First moment of the source reweighted by `p²`. -/
def xiShiftedPolynomialWeightedCurrent (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment y k).re) p (X * p)

/-- Division-free degree-one successor selected by the `p²`-reweighted source. -/
def xiShiftedPolynomialWeightAdaptiveSuccessor (y : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedPolynomialWeightedMass y p • (X * p) -
    xiShiftedPolynomialWeightedCurrent y p • p

/-- Real shifted-Xi moment functional equals its bounded atomic divisor realization. -/
theorem ofReal_momentFunctional_xiShifted_eq_atomicPolynomialMoment
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    ((HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) p : ℝ) : ℂ) =
      atomicPolynomialMoment
        (fun q => xiShiftedReciprocalSquare y q)
        (fun q => xiShiftedReciprocalSquare y q) p := by
  let u : XiZeroCopy → ℂ := fun q => xiShiftedReciprocalSquare y q
  have hu : Summable u := by
    change Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q)
    simpa only [Nat.zero_add, pow_one] using
      summable_xiShiftedReciprocalSquare_pow hy 0
  have hubound : ∀ q, ‖u q‖ ≤ (1 : ℝ) := by
    intro q
    change ‖xiShiftedReciprocalSquare y q‖ ≤ 1
    rw [xiShiftedReciprocalSquare_eq_xiResolventPoint hy]
    exact norm_xiResolventPoint_le_one hy q
  have hmom : ∀ n,
      (((xiShiftedReciprocalMoment y n).re : ℝ) : ℂ) =
        atomicPowerMoment u u n := by
    intro n
    calc
      (((xiShiftedReciprocalMoment y n).re : ℝ) : ℂ) =
          xiShiftedReciprocalMoment y n := by
            apply Complex.ext <;>
              simp [xiShiftedReciprocalMoment_im_eq_zero hy n]
      _ = atomicPowerMoment u u n := by
        rw [xiShiftedReciprocalMoment, atomicPowerMoment]
        apply tsum_congr
        intro q
        simp only [u]
        rw [pow_succ']
  simpa only [u] using
    ofReal_momentFunctional_eq_atomicPolynomialMoment hu hubound hmom p

/-- Polynomial-weighted shifted moments are exactly resolvent polynomial moments. -/
theorem ofReal_xiShiftedPolynomialWeightedMoment_eq_xiPolyMoment
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) (k : ℕ) :
    ((HTGeometry.momentFunctional
      (fun n => (xiShiftedReciprocalMoment y n).re)
      (X ^ k * (p * p)) : ℝ) : ℂ) = xiPolyMoment p k y := by
  rw [ofReal_momentFunctional_xiShifted_eq_atomicPolynomialMoment hy]
  rw [atomicPolynomialMoment]
  change (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q *
        evalRealPolynomial (X ^ k * (p * p))
          (xiShiftedReciprocalSquare y q)) =
    ∑' q : XiZeroCopy, xiResolventPoint y q ^ (k + 1) *
      evalRealPolynomial p (xiResolventPoint y q) ^ (2 : ℕ)
  apply tsum_congr
  intro q
  rw [xiShiftedReciprocalSquare_eq_xiResolventPoint hy]
  simp only [evalRealPolynomial_mul, evalRealPolynomial_pow,
    evalRealPolynomial_X]
  rw [pow_succ']
  ring

/-- Zeroth weighted real moment is the zeroth complex resolvent moment. -/
theorem ofReal_xiShiftedPolynomialWeightedMass_eq_xiPolyMoment
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    ((xiShiftedPolynomialWeightedMass y p : ℝ) : ℂ) = xiPolyMoment p 0 y := by
  rw [xiShiftedPolynomialWeightedMass, HTGeometry.momentInner_def,
    show p * p = X ^ (0 : ℕ) * (p * p) by simp,
    ofReal_xiShiftedPolynomialWeightedMoment_eq_xiPolyMoment hy]

/-- First weighted real moment is the first complex resolvent moment. -/
theorem ofReal_xiShiftedPolynomialWeightedCurrent_eq_xiPolyMoment
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    ((xiShiftedPolynomialWeightedCurrent y p : ℝ) : ℂ) = xiPolyMoment p 1 y := by
  rw [xiShiftedPolynomialWeightedCurrent, HTGeometry.momentInner_def,
    show p * (X * p) = X ^ (1 : ℕ) * (p * p) by ring,
    ofReal_xiShiftedPolynomialWeightedMoment_eq_xiPolyMoment hy]

/-- Second weighted real moment is the second complex resolvent moment. -/
theorem ofReal_xiShiftedPolynomialWeightedSecond_eq_xiPolyMoment
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    ((HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (X * p) (X * p) : ℝ) : ℂ) = xiPolyMoment p 2 y := by
  rw [HTGeometry.momentInner_def,
    show (X * p) * (X * p) = X ^ (2 : ℕ) * (p * p) by ring,
    ofReal_xiShiftedPolynomialWeightedMoment_eq_xiPolyMoment hy]

/-- Admission makes the division-free successor orthogonal to its source amplitude. -/
theorem momentInner_xiShiftedPolynomialWeightAdaptiveSuccessor_eq_zero (y : ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) p
      (xiShiftedPolynomialWeightAdaptiveSuccessor y p) = 0 := by
  rw [xiShiftedPolynomialWeightAdaptiveSuccessor, HTGeometry.momentInner_sub_right,
    HTGeometry.momentInner_smul_right, HTGeometry.momentInner_smul_right]
  rw [xiShiftedPolynomialWeightedMass, xiShiftedPolynomialWeightedCurrent]
  ring

/-- Mixed admitted crossing is exactly the weighted Turán determinant. -/
theorem xiShiftedPolynomialWeightAdaptiveSuccessor_mixedLanding (y : ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment y k).re) p
      (X * xiShiftedPolynomialWeightAdaptiveSuccessor y p) =
    xiShiftedPolynomialWeightedMass y p *
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * p) (X * p) -
      xiShiftedPolynomialWeightedCurrent y p ^ (2 : ℕ) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let A := xiShiftedPolynomialWeightedMass y p
  let B := xiShiftedPolynomialWeightedCurrent y p
  have hpoly : X * xiShiftedPolynomialWeightAdaptiveSuccessor y p =
      A • (X * (X * p)) - B • (X * p) := by
    dsimp only [A, B]
    rw [xiShiftedPolynomialWeightAdaptiveSuccessor]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, HTGeometry.momentInner_sub_right,
    HTGeometry.momentInner_smul_right, HTGeometry.momentInner_smul_right]
  rw [← HTGeometry.momentInner_X_mul]
  dsimp only [A, B]
  rw [xiShiftedPolynomialWeightedMass, xiShiftedPolynomialWeightedCurrent]
  ring

/-- Successor energy is base mass times its mixed Turán landing. -/
theorem xiShiftedPolynomialWeightAdaptiveSuccessor_energy_eq_mass_mul_landing
    (y : ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedPolynomialWeightAdaptiveSuccessor y p)
        (xiShiftedPolynomialWeightAdaptiveSuccessor y p) =
      xiShiftedPolynomialWeightedMass y p *
        (xiShiftedPolynomialWeightedMass y p *
            HTGeometry.momentInner
              (fun k => (xiShiftedReciprocalMoment y k).re)
              (X * p) (X * p) -
          xiShiftedPolynomialWeightedCurrent y p ^ (2 : ℕ)) := by
  simp only [xiShiftedPolynomialWeightAdaptiveSuccessor, HTGeometry.momentInner_sub_left,
    HTGeometry.momentInner_sub_right, HTGeometry.momentInner_smul_left,
    HTGeometry.momentInner_smul_right]
  rw [HTGeometry.momentInner_comm _ (X * p) p,
    xiShiftedPolynomialWeightedMass, xiShiftedPolynomialWeightedCurrent]
  ring

/-- Literal rational–Gamma-minus-von-Mangoldt landing selected by `(p,Q)`. -/
def xiShiftedAdaptiveMixedCompletedArithmeticLanding
    (w : ℝ) (p : Polynomial ℝ) : ℝ :=
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p
  let c := xiShiftedBilinearCrossingCoefficientPacket p Q
  xiShiftedBoundaryRationalGammaAggregate w 1 c -
    xiShiftedBoundaryVonMangoldtAggregate w 1 c

/-- Landing retains one amplitude-dependent kernel in continuum and prime-label formations. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_commonKernel_sourceFormation
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p
    let c := xiShiftedBilinearCrossingCoefficientPacket p Q
    xiShiftedAdaptiveMixedCompletedArithmeticLanding w p =
      xiShiftedBoundaryArchimedeanAggregate w 1 c +
        (∫ x in Ioi (1 : ℝ),
          xiShiftedHankelBoundaryRadialKernel w 1 c x) -
        ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
          xiShiftedHankelBoundaryRadialKernel w 1 c (m : ℝ) := by
  dsimp only
  rw [xiShiftedAdaptiveMixedCompletedArithmeticLanding,
    xiShiftedBoundaryRationalGammaAggregate_eq_archimedean_add_lebesgue hw,
    xiShiftedBoundaryVonMangoldtAggregate_eq_labelwise hw]

/-- Literal completed arithmetic landing equals the real weighted Turán determinant. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_turan
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedAdaptiveMixedCompletedArithmeticLanding w p =
      xiShiftedPolynomialWeightedMass (w ^ (2 : ℕ)) p *
          HTGeometry.momentInner
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
            (X * p) (X * p) -
        xiShiftedPolynomialWeightedCurrent (w ^ (2 : ℕ)) p ^ (2 : ℕ) := by
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p
  let c := xiShiftedBilinearCrossingCoefficientPacket p Q
  rw [xiShiftedAdaptiveMixedCompletedArithmeticLanding]
  change xiShiftedBoundaryRationalGammaAggregate w 1 c -
      xiShiftedBoundaryVonMangoldtAggregate w 1 c = _
  rw [← xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw,
    ← xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w)]
  change xiShiftedCompletedMomentAggregate (w ^ (2 : ℕ)) 1
      (xiShiftedBilinearCrossingCoefficientPacket p Q) = _
  rw [xiShiftedCompletedMomentAggregate_bilinearPacket_eq_momentInner]
  exact xiShiftedPolynomialWeightAdaptiveSuccessor_mixedLanding (w ^ (2 : ℕ)) p

/-- Arithmetic landing is the real part of the resolvent single minor. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_re_xiPolyTuranMinor
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedAdaptiveMixedCompletedArithmeticLanding w p =
      (xiPolyMoment p 0 (w ^ (2 : ℕ)) * xiPolyMoment p 2 (w ^ (2 : ℕ)) -
        xiPolyMoment p 1 (w ^ (2 : ℕ)) ^ (2 : ℕ)).re := by
  rw [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_turan hw]
  have h0 := ofReal_xiShiftedPolynomialWeightedMass_eq_xiPolyMoment (sq_nonneg w) p
  have h1 := ofReal_xiShiftedPolynomialWeightedCurrent_eq_xiPolyMoment (sq_nonneg w) p
  have h2 := ofReal_xiShiftedPolynomialWeightedSecond_eq_xiPolyMoment (sq_nonneg w) p
  have hcast :
      (((xiShiftedPolynomialWeightedMass (w ^ (2 : ℕ)) p *
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
          (X * p) (X * p) -
        xiShiftedPolynomialWeightedCurrent (w ^ (2 : ℕ)) p ^ (2 : ℕ) : ℝ) : ℂ)) =
      xiPolyMoment p 0 (w ^ (2 : ℕ)) * xiPolyMoment p 2 (w ^ (2 : ℕ)) -
        xiPolyMoment p 1 (w ^ (2 : ℕ)) ^ (2 : ℕ) := by
    push_cast
    rw [h0, h1, h2]
  have hre := congrArg Complex.re hcast
  simpa only [Complex.ofReal_re] using hre

/-- After admission, frozen mixed landing differentiates to literal bilinear arithmetic source. -/
theorem hasDerivAt_xiShiftedAdaptiveMixedCompletedLanding_frozenSource
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p
    HasDerivAt
      (fun y => xiShiftedCompletedMomentAggregate y 1
        (xiShiftedBilinearCrossingCoefficientPacket p Q))
      (-xiShiftedAdaptiveBilinearCompletedArithmeticSource w p Q) (w ^ (2 : ℕ)) := by
  dsimp only
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p
  let c := xiShiftedBilinearCrossingCoefficientPacket p Q
  have h := hasDerivAt_xiShiftedCompletedMomentAggregate
    (sq_pos_of_pos (by linarith : 0 < w)) 1 c
  rw [xiShiftedCompletedMomentAggregate_adaptiveBilinearPacket_eq_arithmeticSource hw]
    at h
  exact h

/-- Second moment of the source reweighted by `p²`. -/
def xiShiftedPolynomialWeightedSecond (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment y k).re) (X * p) (X * p)

/-- Source rate consumed by weighted mass. -/
def xiShiftedPolynomialWeightedMassSource (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentFunctional
    (fun k => (xiShiftedReciprocalMoment y k).re)
    (X * xiShiftedBoundaryShiftedEuler 1 (p * p))

/-- Bilinear source rate consumed by weighted current. -/
def xiShiftedPolynomialWeightedCurrentSource (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentFunctional
    (fun k => (xiShiftedReciprocalMoment y k).re)
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial p p)

/-- Bilinear source rate consumed by weighted second moment. -/
def xiShiftedPolynomialWeightedSecondSource (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentFunctional
    (fun k => (xiShiftedReciprocalMoment y k).re)
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial (X * p) p)

/-- Exact source cost of moving the division-free admission coefficients. -/
def xiShiftedPolynomialWeightAdmissionConnectionSource
    (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  xiShiftedPolynomialWeightedMassSource y p * xiShiftedPolynomialWeightedSecond y p -
    xiShiftedPolynomialWeightedCurrentSource y p * xiShiftedPolynomialWeightedCurrent y p

/-- Moving-admission mixed landing in the shifted moment chart. -/
def xiShiftedAdaptiveMixedMomentLanding (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.momentInner
    (fun k => (xiShiftedReciprocalMoment y k).re) p
    (X * xiShiftedPolynomialWeightAdaptiveSuccessor y p)

/-- Moving mixed landing remains exactly the weighted Turán determinant. -/
theorem xiShiftedAdaptiveMixedMomentLanding_eq_turan
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedAdaptiveMixedMomentLanding y p =
      xiShiftedPolynomialWeightedMass y p * xiShiftedPolynomialWeightedSecond y p -
        xiShiftedPolynomialWeightedCurrent y p ^ (2 : ℕ) := by
  rw [xiShiftedAdaptiveMixedMomentLanding, xiShiftedPolynomialWeightedSecond]
  exact xiShiftedPolynomialWeightAdaptiveSuccessor_mixedLanding y p

/-- Bilinear producer splits into second-moment source minus current source. -/
theorem xiShiftedBilinearSource_adaptiveSuccessor_eq
    (y : ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial p
          (xiShiftedPolynomialWeightAdaptiveSuccessor y p)) =
      xiShiftedPolynomialWeightedMass y p * xiShiftedPolynomialWeightedSecondSource y p -
        xiShiftedPolynomialWeightedCurrent y p * xiShiftedPolynomialWeightedCurrentSource y p := by
  let A := xiShiftedPolynomialWeightedMass y p
  let B := xiShiftedPolynomialWeightedCurrent y p
  have hshear :
      xiShiftedBoundaryAdaptiveBilinearShearPolynomial p
          (xiShiftedPolynomialWeightAdaptiveSuccessor y p) =
        A • xiShiftedBoundaryAdaptiveBilinearShearPolynomial (X * p) p -
          B • xiShiftedBoundaryAdaptiveBilinearShearPolynomial p p := by
    dsimp only [A, B]
    rw [xiShiftedPolynomialWeightAdaptiveSuccessor]
    simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
      xiShiftedBoundaryShiftedEuler, Polynomial.smul_eq_C_mul,
      Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, one_mul, C_1]
    ring
  rw [hshear, HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_smul]
  dsimp only [A, B, xiShiftedPolynomialWeightedSecondSource,
    xiShiftedPolynomialWeightedCurrentSource]

/-- Literal completed arithmetic producer has the same division-free source split. -/
theorem xiShiftedArithmeticSource_adaptiveSuccessor_eq
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w p
        (xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p) =
      xiShiftedPolynomialWeightedMass (w ^ (2 : ℕ)) p *
          xiShiftedPolynomialWeightedSecondSource (w ^ (2 : ℕ)) p -
        xiShiftedPolynomialWeightedCurrent (w ^ (2 : ℕ)) p *
          xiShiftedPolynomialWeightedCurrentSource (w ^ (2 : ℕ)) p := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw]
  exact xiShiftedBilinearSource_adaptiveSuccessor_eq (w ^ (2 : ℕ)) p

/-- Actual moving-admission law: derivative is minus arithmetic producer plus connection source. -/
theorem hasDerivAt_xiShiftedAdaptiveMixedMomentLanding_eq_source_add_connection
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    HasDerivAt (fun y => xiShiftedAdaptiveMixedMomentLanding y p)
      (-(xiShiftedAdaptiveBilinearCompletedArithmeticSource w p
          (xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ (2 : ℕ)) p) +
        xiShiftedPolynomialWeightAdmissionConnectionSource (w ^ (2 : ℕ)) p)) (w ^ (2 : ℕ)) := by
  have hy : 0 < w ^ (2 : ℕ) := sq_pos_of_pos (by linarith : 0 < w)
  have hA : HasDerivAt (fun y => xiShiftedPolynomialWeightedMass y p)
      (-xiShiftedPolynomialWeightedMassSource (w ^ (2 : ℕ)) p) (w ^ (2 : ℕ)) := by
    simpa only [xiShiftedPolynomialWeightedMass, HTGeometry.momentInner_def,
      xiShiftedPolynomialWeightedMassSource] using
      hasDerivAt_xiShiftedMomentFunctional_sourceConnection hy (p * p)
  have hB : HasDerivAt (fun y => xiShiftedPolynomialWeightedCurrent y p)
      (-xiShiftedPolynomialWeightedCurrentSource (w ^ (2 : ℕ)) p) (w ^ (2 : ℕ)) := by
    simpa only [xiShiftedPolynomialWeightedCurrent, xiShiftedPolynomialWeightedCurrentSource] using
      hasDerivAt_xiShiftedMomentInner_bilinearCrossing_eq_adaptiveShear hy p p
  have hC : HasDerivAt (fun y => xiShiftedPolynomialWeightedSecond y p)
      (-xiShiftedPolynomialWeightedSecondSource (w ^ (2 : ℕ)) p) (w ^ (2 : ℕ)) := by
    simpa only [xiShiftedPolynomialWeightedSecond, xiShiftedPolynomialWeightedSecondSource] using
      hasDerivAt_xiShiftedMomentInner_bilinearCrossing_eq_adaptiveShear hy (X * p) p
  have hdet := (hA.mul hC).sub (hB.pow 2)
  have hfun : (fun y => xiShiftedAdaptiveMixedMomentLanding y p) =
      (fun y => xiShiftedPolynomialWeightedMass y p * xiShiftedPolynomialWeightedSecond y p -
        xiShiftedPolynomialWeightedCurrent y p ^ (2 : ℕ)) := by
    funext y
    exact xiShiftedAdaptiveMixedMomentLanding_eq_turan y p
  rw [hfun, xiShiftedArithmeticSource_adaptiveSuccessor_eq hw]
  have hderiv :
      -(xiShiftedPolynomialWeightedMass (w ^ (2 : ℕ)) p *
            xiShiftedPolynomialWeightedSecondSource (w ^ (2 : ℕ)) p -
          xiShiftedPolynomialWeightedCurrent (w ^ (2 : ℕ)) p *
            xiShiftedPolynomialWeightedCurrentSource (w ^ (2 : ℕ)) p +
        xiShiftedPolynomialWeightAdmissionConnectionSource (w ^ (2 : ℕ)) p) =
      -xiShiftedPolynomialWeightedMassSource (w ^ (2 : ℕ)) p *
          xiShiftedPolynomialWeightedSecond (w ^ (2 : ℕ)) p +
        xiShiftedPolynomialWeightedMass (w ^ (2 : ℕ)) p *
          -xiShiftedPolynomialWeightedSecondSource (w ^ (2 : ℕ)) p -
        (2 : ℝ) * xiShiftedPolynomialWeightedCurrent (w ^ (2 : ℕ)) p ^ (2 - 1) *
          -xiShiftedPolynomialWeightedCurrentSource (w ^ (2 : ℕ)) p := by
    simp only [xiShiftedPolynomialWeightAdmissionConnectionSource]
    ring
  rw [hderiv]
  exact hdet

/-- RH iff every real nodal adaptive arithmetic landing is nonnegative. -/
theorem riemannHypothesis_iff_forall_nodal_adaptiveArithmeticLanding_nonneg
    {w : ℝ} (hw : 1 / 2 < w) :
    RiemannHypothesis ↔
      ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
        0 ≤ xiShiftedAdaptiveMixedCompletedArithmeticLanding w
          (X ^ m * nodalPolynomial R) := by
  constructor
  · intro hRH R hR m
    have h := (riemannHypothesis_iff_forall_nodal_single_minor (sq_nonneg w)).mp
      hRH R hR m
    rwa [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_re_xiPolyTuranMinor hw]
  · intro h
    apply (riemannHypothesis_iff_forall_nodal_single_minor (sq_nonneg w)).mpr
    intro R hR m
    have h' := h R hR m
    rwa [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_re_xiPolyTuranMinor hw] at h'

/-- RH iff the countable rational-node adaptive arithmetic landing family is nonnegative. -/
theorem riemannHypothesis_iff_forall_rationalNodal_adaptiveArithmeticLanding_nonneg
    {w : ℝ} (hw : 1 / 2 < w) :
    RiemannHypothesis ↔
      ∀ (j m : ℕ) (c : Fin j → ℚ),
        (∀ i, 0 < c i ∧ (c i : ℝ) ≤ 1) →
          0 ≤ xiShiftedAdaptiveMixedCompletedArithmeticLanding w
            (X ^ m * finNodalPolynomial (fun i => ((c i : ℝ)))) := by
  constructor
  · intro hRH j m c hc
    have h :=
      (riemannHypothesis_iff_forall_rational_nodal_single_minor (sq_nonneg w)).mp
        hRH j m c hc
    rwa [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_re_xiPolyTuranMinor hw]
  · intro h
    apply
      (riemannHypothesis_iff_forall_rational_nodal_single_minor (sq_nonneg w)).mpr
    intro j m c hc
    have h' := h j m c hc
    rwa [xiShiftedAdaptiveMixedCompletedArithmeticLanding_eq_re_xiPolyTuranMinor hw] at h'

end

end RHTower

