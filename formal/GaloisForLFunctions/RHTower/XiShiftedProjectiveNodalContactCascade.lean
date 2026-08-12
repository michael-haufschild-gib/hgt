import GaloisForLFunctions.RHTower.XiShiftedNodalAdaptiveArithmeticSourceLanding
import GaloisForLFunctions.RHTower.XiShiftedHalfDensityMobiusSourceConnection

/-!
# Projective nodal contact cascade for the shifted-Xi arithmetic source

Moving a nodal amplitude by the degree-lowered Möbius tangent cancels the full coefficient
connection in every polynomial-weighted moment.  The remaining transport is bidiagonal.  Its
first Turán compound differentiates to a scalar gauge term minus one higher mixed completed
arithmetic landing.  Thus projective transport does not preserve a finite positivity cone: at a
flat contact it raises the source obstruction by one mixed moment level.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Degree-lowered projective Möbius tangent with arbitrary scalar gauge. -/
def xiShiftedProjectiveMobiusVelocity
    (n : ℕ) (a : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  X ^ 2 * p.derivative - (n : ℝ) • (X * p) + a • p

/-- `p²`-weighted shifted-Xi moment at level `k`. -/
def xiShiftedProjectiveNodalWeightedMoment
    (y : ℝ) (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  HTGeometry.momentFunctional
    (fun j => (xiShiftedReciprocalMoment y j).re) (X ^ k * (p * p))

/-- Complete instantaneous moving-amplitude rate: fixed shifted-moment source plus polynomial
tangent. -/
def xiShiftedProjectiveNodalWeightedMomentCovariantRate
    (y : ℝ) (p V : Polynomial ℝ) (k : ℕ) : ℝ :=
  -HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re)
      (X * xiShiftedBoundaryShiftedEuler 1 (X ^ k * (p * p))) +
    2 * HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (X ^ k * (p * V))

/-- Polynomial identity behind projective cancellation of the moving-amplitude connection. -/
theorem xiShiftedProjectiveMobiusVelocity_source_polynomial
    (n k : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    (2 : ℝ) •
          (X ^ k * (p * xiShiftedProjectiveMobiusVelocity n a p)) -
        X * xiShiftedBoundaryShiftedEuler 1 (X ^ k * (p * p)) =
      (2 * a) • (X ^ k * (p * p)) -
        ((2 * n + k + 1 : ℕ) : ℝ) • (X ^ (k + 1) * (p * p)) := by
  cases k with
  | zero =>
      simp only [xiShiftedProjectiveMobiusVelocity,
        xiShiftedBoundaryShiftedEuler, pow_zero, one_mul,
        Polynomial.derivative_mul, zero_add,
        Polynomial.smul_eq_C_mul]
      push_cast [map_add, map_mul, map_ofNat, map_natCast, map_zero]
      ring
  | succ k =>
      simp only [xiShiftedProjectiveMobiusVelocity,
        xiShiftedBoundaryShiftedEuler, Polynomial.derivative_mul,
        Polynomial.derivative_pow, Polynomial.derivative_X,
        Polynomial.smul_eq_C_mul]
      rw [pow_succ, pow_succ]
      push_cast [map_add, map_mul, map_ofNat, map_natCast]
      ring

/-- Projective Möbius coflow turns every weighted moment into a bidiagonal transport law. -/
theorem xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq
    (y : ℝ) (n k : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
        (xiShiftedProjectiveMobiusVelocity n a p) k =
      2 * a * xiShiftedProjectiveNodalWeightedMoment y p k -
        ((2 * n + k + 1 : ℕ) : ℝ) *
          xiShiftedProjectiveNodalWeightedMoment y p (k + 1) := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let A : Polynomial ℝ := X ^ k *
    (p * xiShiftedProjectiveMobiusVelocity n a p)
  let B : Polynomial ℝ :=
    X * xiShiftedBoundaryShiftedEuler 1 (X ^ k * (p * p))
  have hpoly := xiShiftedProjectiveMobiusVelocity_source_polynomial n k a p
  change -HTGeometry.momentFunctional s B +
      2 * HTGeometry.momentFunctional s A = _
  calc
    -HTGeometry.momentFunctional s B + 2 * HTGeometry.momentFunctional s A =
        HTGeometry.momentFunctional s ((2 : ℝ) • A - B) := by
          rw [HTGeometry.momentFunctional_sub, HTGeometry.momentFunctional_smul]
          ring
    _ = HTGeometry.momentFunctional s
        ((2 * a) • (X ^ k * (p * p)) -
          ((2 * n + k + 1 : ℕ) : ℝ) • (X ^ (k + 1) * (p * p))) := by
          rw [hpoly]
    _ = _ := by
      rw [HTGeometry.momentFunctional_sub,
        HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_smul]
      rfl

/-- Weighted Turán determinant carried by one nodal amplitude. -/
def xiShiftedProjectiveNodalTuranLanding
    (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMoment y p 0 *
      xiShiftedProjectiveNodalWeightedMoment y p 2 -
    xiShiftedProjectiveNodalWeightedMoment y p 1 ^ 2

/-- Next mixed compound reached by the projective contact cascade. -/
def xiShiftedProjectiveNodalHigherMixedLanding
    (y : ℝ) (p : Polynomial ℝ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMoment y p 0 *
      xiShiftedProjectiveNodalWeightedMoment y p 3 -
    xiShiftedProjectiveNodalWeightedMoment y p 1 *
      xiShiftedProjectiveNodalWeightedMoment y p 2

/-- Product-rule rate of the first Turán compound under projective Möbius coflow. -/
def xiShiftedProjectiveNodalTuranCovariantRate
    (y : ℝ) (n : ℕ) (a : ℝ) (p : Polynomial ℝ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
      (xiShiftedProjectiveMobiusVelocity n a p) 0 *
      xiShiftedProjectiveNodalWeightedMoment y p 2 +
    xiShiftedProjectiveNodalWeightedMoment y p 0 *
      xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
        (xiShiftedProjectiveMobiusVelocity n a p) 2 -
    2 * xiShiftedProjectiveNodalWeightedMoment y p 1 *
      xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
        (xiShiftedProjectiveMobiusVelocity n a p) 1

/-- **Projective nodal contact cascade.**  Full coefficient connection collapses to scalar gauge
plus one higher mixed landing. -/
theorem xiShiftedProjectiveNodalTuranCovariantRate_eq
    (y : ℝ) (n : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalTuranCovariantRate y n a p =
      4 * a * xiShiftedProjectiveNodalTuranLanding y p -
        ((2 * n + 3 : ℕ) : ℝ) *
          xiShiftedProjectiveNodalHigherMixedLanding y p := by
  rw [xiShiftedProjectiveNodalTuranCovariantRate,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq]
  simp only [Nat.zero_add, Nat.reduceAdd]
  unfold xiShiftedProjectiveNodalTuranLanding
    xiShiftedProjectiveNodalHigherMixedLanding
  push_cast
  ring

/-- At a flat Turán contact, orientation is exactly the negative next mixed source. -/
theorem xiShiftedProjectiveNodalTuranCovariantRate_eq_neg_higher_of_contact
    {y : ℝ} {n : ℕ} {a : ℝ} {p : Polynomial ℝ}
    (hcontact : xiShiftedProjectiveNodalTuranLanding y p = 0) :
    xiShiftedProjectiveNodalTuranCovariantRate y n a p =
      -((2 * n + 3 : ℕ) : ℝ) *
        xiShiftedProjectiveNodalHigherMixedLanding y p := by
  rw [xiShiftedProjectiveNodalTuranCovariantRate_eq, hcontact]
  ring

/-- Level zero is the existing polynomial-weighted mass. -/
theorem xiShiftedProjectiveNodalWeightedMoment_zero_eq_mass
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalWeightedMoment y p 0 =
      xiShiftedPolynomialWeightedMass y p := by
  simp only [xiShiftedProjectiveNodalWeightedMoment,
    xiShiftedPolynomialWeightedMass, HTGeometry.momentInner_def,
    pow_zero, one_mul]

/-- Level one is the existing polynomial-weighted odd current. -/
theorem xiShiftedProjectiveNodalWeightedMoment_one_eq_current
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalWeightedMoment y p 1 =
      xiShiftedPolynomialWeightedCurrent y p := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  change HTGeometry.momentFunctional s (X ^ 1 * (p * p)) =
    HTGeometry.momentFunctional s (p * (X * p))
  congr 1
  ring

/-- Level two is the existing polynomial-weighted second moment. -/
theorem xiShiftedProjectiveNodalWeightedMoment_two_eq_second
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalWeightedMoment y p 2 =
      xiShiftedPolynomialWeightedSecond y p := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  change HTGeometry.momentFunctional s (X ^ 2 * (p * p)) =
    HTGeometry.momentFunctional s ((X * p) * (X * p))
  congr 1
  ring

/-- The projective Turán compound is exactly the moving adaptive mixed landing already used by
the rational nodal RH criterion. -/
theorem xiShiftedProjectiveNodalTuranLanding_eq_adaptiveMixedMomentLanding
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalTuranLanding y p =
      xiShiftedAdaptiveMixedMomentLanding y p := by
  rw [xiShiftedAdaptiveMixedMomentLanding_eq_turan]
  unfold xiShiftedProjectiveNodalTuranLanding
  rw [xiShiftedProjectiveNodalWeightedMoment_zero_eq_mass,
    xiShiftedProjectiveNodalWeightedMoment_one_eq_current,
    xiShiftedProjectiveNodalWeightedMoment_two_eq_second]

/-- Higher compound is the same division-free successor landed one additional odd level above
the original Turán crossing. -/
theorem xiShiftedProjectiveNodalHigherMixedLanding_eq_successorLanding
    (y : ℝ) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalHigherMixedLanding y p =
      HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) p
        (X * (X * xiShiftedPolynomialWeightAdaptiveSuccessor y p)) := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let M0 := xiShiftedProjectiveNodalWeightedMoment y p 0
  let M1 := xiShiftedProjectiveNodalWeightedMoment y p 1
  let M2 := xiShiftedProjectiveNodalWeightedMoment y p 2
  let M3 := xiShiftedProjectiveNodalWeightedMoment y p 3
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor y p
  have hM0 : M0 = xiShiftedPolynomialWeightedMass y p :=
    xiShiftedProjectiveNodalWeightedMoment_zero_eq_mass y p
  have hM1 : M1 = xiShiftedPolynomialWeightedCurrent y p :=
    xiShiftedProjectiveNodalWeightedMoment_one_eq_current y p
  have hpoly :
      p * (X * (X * Q)) =
        M0 • (X ^ 3 * (p * p)) - M1 • (X ^ 2 * (p * p)) := by
    dsimp only [Q]
    rw [xiShiftedPolynomialWeightAdaptiveSuccessor, ← hM0, ← hM1]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  change M0 * M3 - M1 * M2 =
    HTGeometry.momentFunctional s (p * (X * (X * Q)))
  rw [hpoly, HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_smul]
  rfl

/-- Literal rational–Gamma-minus-von-Mangoldt packet for the next mixed contact level.  Admission
selects `Q` first; arithmetic aggregation is performed only afterward on `(p,XQ)`. -/
def xiShiftedProjectiveNodalNextCompletedArithmeticLanding
    (w : ℝ) (p : Polynomial ℝ) : ℝ :=
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ 2) p
  let c := xiShiftedBilinearCrossingCoefficientPacket p (X * Q)
  xiShiftedBoundaryRationalGammaAggregate w 1 c -
    xiShiftedBoundaryVonMangoldtAggregate w 1 c

/-- Next contact landing retains one admission-selected kernel in continuum and prime-label
formations. -/
theorem xiShiftedProjectiveNodalNextCompletedArithmeticLanding_eq_commonKernel_sourceFormation
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ 2) p
    let c := xiShiftedBilinearCrossingCoefficientPacket p (X * Q)
    xiShiftedProjectiveNodalNextCompletedArithmeticLanding w p =
      xiShiftedBoundaryArchimedeanAggregate w 1 c +
        (∫ x in Set.Ioi (1 : ℝ),
          xiShiftedHankelBoundaryRadialKernel w 1 c x) -
        ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
          xiShiftedHankelBoundaryRadialKernel w 1 c (m : ℝ) := by
  dsimp only
  rw [xiShiftedProjectiveNodalNextCompletedArithmeticLanding,
    xiShiftedBoundaryRationalGammaAggregate_eq_archimedean_add_lebesgue hw,
    xiShiftedBoundaryVonMangoldtAggregate_eq_labelwise hw]

/-- Literal completed arithmetic packet is exactly the higher mixed compound. -/
theorem xiShiftedProjectiveNodalNextCompletedArithmeticLanding_eq_higherMixed
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) :
    xiShiftedProjectiveNodalNextCompletedArithmeticLanding w p =
      xiShiftedProjectiveNodalHigherMixedLanding (w ^ 2) p := by
  let Q := xiShiftedPolynomialWeightAdaptiveSuccessor (w ^ 2) p
  let c := xiShiftedBilinearCrossingCoefficientPacket p (X * Q)
  rw [xiShiftedProjectiveNodalNextCompletedArithmeticLanding]
  change xiShiftedBoundaryRationalGammaAggregate w 1 c -
      xiShiftedBoundaryVonMangoldtAggregate w 1 c = _
  rw [← xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw,
    ← xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w)]
  change xiShiftedCompletedMomentAggregate (w ^ 2) 1
      (xiShiftedBilinearCrossingCoefficientPacket p (X * Q)) = _
  rw [xiShiftedCompletedMomentAggregate_bilinearPacket_eq_momentInner]
  exact
    (xiShiftedProjectiveNodalHigherMixedLanding_eq_successorLanding
      (w ^ 2) p).symm

/-- **Arithmetic first-contact transmutation.**  At a flat nodal Turán face, projective coflow
lands exactly on the negative next completed rational–Gamma-minus-von-Mangoldt packet. -/
theorem xiShiftedProjectiveNodalTuranCovariantRate_eq_neg_nextArithmetic_of_contact
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} {a : ℝ} {p : Polynomial ℝ}
    (hcontact : xiShiftedProjectiveNodalTuranLanding (w ^ 2) p = 0) :
    xiShiftedProjectiveNodalTuranCovariantRate (w ^ 2) n a p =
      -((2 * n + 3 : ℕ) : ℝ) *
        xiShiftedProjectiveNodalNextCompletedArithmeticLanding w p := by
  rw [xiShiftedProjectiveNodalTuranCovariantRate_eq_neg_higher_of_contact hcontact,
    xiShiftedProjectiveNodalNextCompletedArithmeticLanding_eq_higherMixed hw]

/-- Adjacent Turán compound at arbitrary moment grade. -/
def xiShiftedProjectiveNodalGradedTuranLanding
    (y : ℝ) (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMoment y p k *
      xiShiftedProjectiveNodalWeightedMoment y p (k + 2) -
    xiShiftedProjectiveNodalWeightedMoment y p (k + 1) ^ 2

/-- Higher mixed Plücker coordinate reached from grade `k`. -/
def xiShiftedProjectiveNodalGradedHigherMixedLanding
    (y : ℝ) (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMoment y p k *
      xiShiftedProjectiveNodalWeightedMoment y p (k + 3) -
    xiShiftedProjectiveNodalWeightedMoment y p (k + 1) *
      xiShiftedProjectiveNodalWeightedMoment y p (k + 2)

/-- Product-rule rate of an arbitrary adjacent Turán grade. -/
def xiShiftedProjectiveNodalGradedTuranCovariantRate
    (y : ℝ) (n : ℕ) (a : ℝ) (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
      (xiShiftedProjectiveMobiusVelocity n a p) k *
      xiShiftedProjectiveNodalWeightedMoment y p (k + 2) +
    xiShiftedProjectiveNodalWeightedMoment y p k *
      xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
        (xiShiftedProjectiveMobiusVelocity n a p) (k + 2) -
    2 * xiShiftedProjectiveNodalWeightedMoment y p (k + 1) *
      xiShiftedProjectiveNodalWeightedMomentCovariantRate y p
        (xiShiftedProjectiveMobiusVelocity n a p) (k + 1)

/-- **All-grade contact cascade.** Every adjacent Turán grade raises to its next mixed Plücker
coordinate with exact coefficient `2n+k+3`. -/
theorem xiShiftedProjectiveNodalGradedTuranCovariantRate_eq
    (y : ℝ) (n : ℕ) (a : ℝ) (p : Polynomial ℝ) (k : ℕ) :
    xiShiftedProjectiveNodalGradedTuranCovariantRate y n a p k =
      4 * a * xiShiftedProjectiveNodalGradedTuranLanding y p k -
        ((2 * n + k + 3 : ℕ) : ℝ) *
          xiShiftedProjectiveNodalGradedHigherMixedLanding y p k := by
  rw [xiShiftedProjectiveNodalGradedTuranCovariantRate,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq,
    xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  unfold xiShiftedProjectiveNodalGradedTuranLanding
    xiShiftedProjectiveNodalGradedHigherMixedLanding
  push_cast
  ring

/-- At any flat adjacent grade, projective orientation is exactly the negative next mixed grade. -/
theorem xiShiftedProjectiveNodalGradedTuranCovariantRate_eq_neg_higher_of_contact
    {y : ℝ} {n : ℕ} {a : ℝ} {p : Polynomial ℝ} {k : ℕ}
    (hcontact : xiShiftedProjectiveNodalGradedTuranLanding y p k = 0) :
    xiShiftedProjectiveNodalGradedTuranCovariantRate y n a p k =
      -((2 * n + k + 3 : ℕ) : ℝ) *
        xiShiftedProjectiveNodalGradedHigherMixedLanding y p k := by
  rw [xiShiftedProjectiveNodalGradedTuranCovariantRate_eq, hcontact]
  ring

/-- Division-free successor selected at arbitrary moment grade. -/
def xiShiftedProjectiveNodalGradedAdaptiveSuccessor
    (y : ℝ) (p : Polynomial ℝ) (k : ℕ) : Polynomial ℝ :=
  xiShiftedProjectiveNodalWeightedMoment y p k • (X * p) -
    xiShiftedProjectiveNodalWeightedMoment y p (k + 1) • p

/-- Every higher Plücker coordinate is an admission-selected bilinear landing. -/
theorem xiShiftedProjectiveNodalGradedHigherMixedLanding_eq_successorLanding
    (y : ℝ) (p : Polynomial ℝ) (k : ℕ) :
    xiShiftedProjectiveNodalGradedHigherMixedLanding y p k =
      HTGeometry.momentInner
        (fun j => (xiShiftedReciprocalMoment y j).re) p
        (X * (X ^ (k + 1) *
          xiShiftedProjectiveNodalGradedAdaptiveSuccessor y p k)) := by
  let s : ℕ → ℝ := fun j => (xiShiftedReciprocalMoment y j).re
  let Mk := xiShiftedProjectiveNodalWeightedMoment y p k
  let Mk1 := xiShiftedProjectiveNodalWeightedMoment y p (k + 1)
  let Mk2 := xiShiftedProjectiveNodalWeightedMoment y p (k + 2)
  let Mk3 := xiShiftedProjectiveNodalWeightedMoment y p (k + 3)
  let Q := xiShiftedProjectiveNodalGradedAdaptiveSuccessor y p k
  have hpoly :
      p * (X * (X ^ (k + 1) * Q)) =
        Mk • (X ^ (k + 3) * (p * p)) -
          Mk1 • (X ^ (k + 2) * (p * p)) := by
    dsimp only [Q, xiShiftedProjectiveNodalGradedAdaptiveSuccessor]
    simp only [Polynomial.smul_eq_C_mul, pow_succ]
    ring
  change Mk * Mk3 - Mk1 * Mk2 =
    HTGeometry.momentFunctional s (p * (X * (X ^ (k + 1) * Q)))
  rw [hpoly, HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_smul]
  rfl

/-- Literal completed arithmetic packet at arbitrary contact grade. -/
def xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding
    (w : ℝ) (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  let Q := xiShiftedProjectiveNodalGradedAdaptiveSuccessor (w ^ 2) p k
  let c := xiShiftedBilinearCrossingCoefficientPacket p (X ^ (k + 1) * Q)
  xiShiftedBoundaryRationalGammaAggregate w 1 c -
    xiShiftedBoundaryVonMangoldtAggregate w 1 c

/-- Every graded packet keeps one admission-selected radial kernel before continuum/prime
aggregation. -/
theorem xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding_eq_commonKernel_sourceFormation
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) (k : ℕ) :
    let Q := xiShiftedProjectiveNodalGradedAdaptiveSuccessor (w ^ 2) p k
    let c := xiShiftedBilinearCrossingCoefficientPacket p (X ^ (k + 1) * Q)
    xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding w p k =
      xiShiftedBoundaryArchimedeanAggregate w 1 c +
        (∫ x in Set.Ioi (1 : ℝ),
          xiShiftedHankelBoundaryRadialKernel w 1 c x) -
        ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) *
          xiShiftedHankelBoundaryRadialKernel w 1 c (m : ℝ) := by
  dsimp only
  rw [xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding,
    xiShiftedBoundaryRationalGammaAggregate_eq_archimedean_add_lebesgue hw,
    xiShiftedBoundaryVonMangoldtAggregate_eq_labelwise hw]

/-- Literal completed packet at grade `k` is exactly its higher mixed Plücker coordinate. -/
theorem xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding_eq_higherMixed
    {w : ℝ} (hw : 1 / 2 < w) (p : Polynomial ℝ) (k : ℕ) :
    xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding w p k =
      xiShiftedProjectiveNodalGradedHigherMixedLanding (w ^ 2) p k := by
  let Q := xiShiftedProjectiveNodalGradedAdaptiveSuccessor (w ^ 2) p k
  let c := xiShiftedBilinearCrossingCoefficientPacket p (X ^ (k + 1) * Q)
  rw [xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding]
  change xiShiftedBoundaryRationalGammaAggregate w 1 c -
      xiShiftedBoundaryVonMangoldtAggregate w 1 c = _
  rw [← xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw,
    ← xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w)]
  change xiShiftedCompletedMomentAggregate (w ^ 2) 1
      (xiShiftedBilinearCrossingCoefficientPacket p (X ^ (k + 1) * Q)) = _
  rw [xiShiftedCompletedMomentAggregate_bilinearPacket_eq_momentInner]
  exact
    (xiShiftedProjectiveNodalGradedHigherMixedLanding_eq_successorLanding
      (w ^ 2) p k).symm

/-- **All-grade arithmetic contact transmutation.** Every flat grade lands on its own next
admission-selected completed Gamma–prime packet. -/
theorem xiShiftedProjectiveNodalGradedTuranCovariantRate_eq_neg_nextArithmetic_of_contact
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} {a : ℝ} {p : Polynomial ℝ} {k : ℕ}
    (hcontact : xiShiftedProjectiveNodalGradedTuranLanding (w ^ 2) p k = 0) :
    xiShiftedProjectiveNodalGradedTuranCovariantRate (w ^ 2) n a p k =
      -((2 * n + k + 3 : ℕ) : ℝ) *
        xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding w p k := by
  rw [xiShiftedProjectiveNodalGradedTuranCovariantRate_eq_neg_higher_of_contact hcontact,
    xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding_eq_higherMixed hw]

/-! ## Hostile two-atom audit of cumulative cascade closure -/

/-- Abstract two-atom moment model used to test whether growing cascade coefficients alone force
nonsummable work. -/
def projectiveTuranCascadeTwoAtomMoment
    (A B r s : ℝ) (k : ℕ) : ℝ :=
  A * r ^ k + B * s ^ k

/-- Adjacent Turán grade of a two-atom moment sequence factors into positive pair separation. -/
theorem projectiveTuranCascadeTwoAtom_turan_factorization
    (A B r s : ℝ) (k : ℕ) :
    projectiveTuranCascadeTwoAtomMoment A B r s k *
        projectiveTuranCascadeTwoAtomMoment A B r s (k + 2) -
      projectiveTuranCascadeTwoAtomMoment A B r s (k + 1) ^ 2 =
        A * B * (r * s) ^ k * (r - s) ^ 2 := by
  simp only [projectiveTuranCascadeTwoAtomMoment, pow_succ]
  ring

/-- Higher mixed grade has the same separation square and one additional pair-sum factor. -/
theorem projectiveTuranCascadeTwoAtom_higherMixed_factorization
    (A B r s : ℝ) (k : ℕ) :
    projectiveTuranCascadeTwoAtomMoment A B r s k *
        projectiveTuranCascadeTwoAtomMoment A B r s (k + 3) -
      projectiveTuranCascadeTwoAtomMoment A B r s (k + 1) *
        projectiveTuranCascadeTwoAtomMoment A B r s (k + 2) =
      A * B * (r * s) ^ k * (r + s) * (r - s) ^ 2 := by
  simp only [projectiveTuranCascadeTwoAtomMoment, pow_succ]
  ring

/-- Positive separated atoms make every adjacent and higher mixed grade strictly positive. -/
theorem projectiveTuranCascadeTwoAtom_all_grades_pos
    {A B r s : ℝ} (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hrs : r < s)
    (k : ℕ) :
    0 < projectiveTuranCascadeTwoAtomMoment A B r s k *
          projectiveTuranCascadeTwoAtomMoment A B r s (k + 2) -
        projectiveTuranCascadeTwoAtomMoment A B r s (k + 1) ^ 2 ∧
      0 < projectiveTuranCascadeTwoAtomMoment A B r s k *
          projectiveTuranCascadeTwoAtomMoment A B r s (k + 3) -
        projectiveTuranCascadeTwoAtomMoment A B r s (k + 1) *
          projectiveTuranCascadeTwoAtomMoment A B r s (k + 2) := by
  have hs : 0 < s := lt_trans hr hrs
  have hrs0 : r - s ≠ 0 := sub_ne_zero.mpr (ne_of_lt hrs)
  rw [projectiveTuranCascadeTwoAtom_turan_factorization,
    projectiveTuranCascadeTwoAtom_higherMixed_factorization]
  constructor
  · exact mul_pos (mul_pos (mul_pos hA hB) (pow_pos (mul_pos hr hs) k))
      (sq_pos_of_ne_zero hrs0)
  · exact mul_pos
      (mul_pos (mul_pos (mul_pos hA hB) (pow_pos (mul_pos hr hs) k))
        (add_pos hr hs))
      (sq_pos_of_ne_zero hrs0)

/-- **Coefficient-growth no-go.** Even if every higher mixed packet is strictly positive, linear
growth of contact coefficients does not force nonsummable cumulative work: every separated
two-atom model inside the geometric disk has a summable weighted cascade. -/
theorem summable_projectiveTuranCascadeTwoAtom_weighted_higherMixed
    {A B r s : ℝ} (hcontract : ‖r * s‖ < 1) (c : ℝ) :
    Summable fun k : ℕ =>
      (c + k) *
        (projectiveTuranCascadeTwoAtomMoment A B r s k *
            projectiveTuranCascadeTwoAtomMoment A B r s (k + 3) -
          projectiveTuranCascadeTwoAtomMoment A B r s (k + 1) *
            projectiveTuranCascadeTwoAtomMoment A B r s (k + 2)) := by
  have hgeo : Summable fun k : ℕ => (r * s) ^ k :=
    summable_geometric_of_norm_lt_one hcontract
  have hlinear : Summable fun k : ℕ => (k : ℝ) * (r * s) ^ k := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hcontract)
  have hbase : Summable fun k : ℕ => (c + k) * (r * s) ^ k := by
    refine ((hgeo.mul_left c).add hlinear).congr ?_
    intro k
    ring
  refine (hbase.mul_right (A * B * (r + s) * (r - s) ^ 2)).congr ?_
  intro k
  rw [projectiveTuranCascadeTwoAtom_higherMixed_factorization]
  ring

end

end RHTower
