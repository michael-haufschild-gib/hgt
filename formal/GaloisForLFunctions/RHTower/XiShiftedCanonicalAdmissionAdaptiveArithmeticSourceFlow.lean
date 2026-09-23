import GaloisForLFunctions.RHTower.XiShiftedHardEdgeRadialSourceConnection
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionConnection

/-!
# Actual adaptive arithmetic-source flow

The flat radial hard-edge connection transports a source polynomial with its hard-edge
coefficients frozen.  The actual completed source does something stronger: the reciprocal
polynomial, its hard-edge chart, and canonical inverse-Hankel admission all move together.

This module gives the exact coefficient law.  The first term is the next completed
prime--Gamma source layer; the other two terms are the bilinear velocities of the two admitted
amplitudes.  On the diagonal they combine into twice the current-admission/velocity source.
Thus no coefficient drift is hidden in a frozen reporter.
-/

open Complex Matrix Polynomial Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Source-mass form of the actual bilinear completed arithmetic producer, written before
aggregation in finite admission coordinates. -/
def xiShiftedAdaptiveBilinearCoefficientSourceMass
    {M N : ℕ} (y : ℝ) (a : Fin M → ℝ) (b : Fin N → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N,
    (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i * b j *
      (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re

/-- One further source differentiation of the bilinear coefficient producer. -/
def xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass
    {M N : ℕ} (y : ℝ) (a : Fin M → ℝ) (b : Fin N → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N,
    (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
      (((i : ℕ) + (j : ℕ) + 3 : ℕ) : ℝ) * a i * b j *
        (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 3)).re

/-- **Fully moving bilinear source law.**  Source differentiation raises the completed moment
layer and also differentiates each admitted amplitude.  No positivity or orthogonality is used. -/
theorem hasDerivAt_xiShiftedAdaptiveBilinearCoefficientSourceMass
    {y : ℝ} (hy : 0 < y) {M N : ℕ}
    (a : Fin M → ℝ → ℝ) (da : Fin M → ℝ)
    (b : Fin N → ℝ → ℝ) (db : Fin N → ℝ)
    (ha : ∀ i : Fin M, HasDerivAt (a i) (da i) y)
    (hb : ∀ j : Fin N, HasDerivAt (b j) (db j) y) :
    HasDerivAt
      (fun v => xiShiftedAdaptiveBilinearCoefficientSourceMass v
        (fun i => a i v) (fun j => b j v))
      (-xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y
          (fun i => a i y) (fun j => b j y) +
        xiShiftedAdaptiveBilinearCoefficientSourceMass y da (fun j => b j y) +
        xiShiftedAdaptiveBilinearCoefficientSourceMass y (fun i => a i y) db) y := by
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin M))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin N))) (fun j _ =>
      (((ha i).mul (hb j)).mul
        (hasDerivAt_re_xiShiftedReciprocalMoment hy
          ((i : ℕ) + (j : ℕ) + 2))).const_mul
            (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ)))
  have hfun :
      (∑ i : Fin M, ∑ j : Fin N,
        fun v => (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
          ((a i * b j *
            (fun u => (xiShiftedReciprocalMoment u
              ((i : ℕ) + (j : ℕ) + 2)).re)) v)) =
        (fun v => xiShiftedAdaptiveBilinearCoefficientSourceMass v
          (fun i => a i v) (fun j => b j v)) := by
    funext v
    simp only [Finset.sum_apply, xiShiftedAdaptiveBilinearCoefficientSourceMass]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.mul_apply]
    ring
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  unfold xiShiftedAdaptiveBilinearCoefficientSourceMass
    xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass
  calc
    (∑ i : Fin M, ∑ j : Fin N,
        (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
          ((da i * b j y + a i y * db j) *
              (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re +
            (a i * b j) y *
              (-((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) + 1) *
                (xiShiftedReciprocalMoment y
                  ((i : ℕ) + (j : ℕ) + 2 + 1)).re))) =
      ∑ i : Fin M, ∑ j : Fin N,
        (-((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
            (((i : ℕ) + (j : ℕ) + 3 : ℕ) : ℝ) * a i y * b j y *
              (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 3)).re) +
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * da i * b j y *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re +
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i y * db j *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.mul_apply]
        push_cast
        ring
    _ =
        -(∑ i : Fin M, ∑ j : Fin N,
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
            (((i : ℕ) + (j : ℕ) + 3 : ℕ) : ℝ) * a i y * b j y *
              (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 3)).re) +
        (∑ i : Fin M, ∑ j : Fin N,
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * da i * b j y *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re) +
        ∑ i : Fin M, ∑ j : Fin N,
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i y * db j *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re := by
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Bilinear coefficient source is symmetric in its two amplitude slots. -/
theorem xiShiftedAdaptiveBilinearCoefficientSourceMass_comm
    {N : ℕ} (y : ℝ) (a b : Fin N → ℝ) :
    xiShiftedAdaptiveBilinearCoefficientSourceMass y a b =
      xiShiftedAdaptiveBilinearCoefficientSourceMass y b a := by
  unfold xiShiftedAdaptiveBilinearCoefficientSourceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (j : ℕ) + (i : ℕ) + 2 = (i : ℕ) + (j : ℕ) + 2 by omega]
  ring

/-- Diagonal specialization: the two admission-velocity slots fuse into one factor `2`. -/
theorem hasDerivAt_xiShiftedAdaptiveDiagonalCoefficientSourceMass
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (a : Fin N → ℝ → ℝ) (da : Fin N → ℝ)
    (ha : ∀ i : Fin N, HasDerivAt (a i) (da i) y) :
    HasDerivAt
      (fun v => xiShiftedAdaptiveBilinearCoefficientSourceMass v
        (fun i => a i v) (fun i => a i v))
      (-xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y
          (fun i => a i y) (fun i => a i y) +
        2 * xiShiftedAdaptiveBilinearCoefficientSourceMass y da
          (fun i => a i y)) y := by
  have h := hasDerivAt_xiShiftedAdaptiveBilinearCoefficientSourceMass
    hy a da a da ha ha
  refine h.congr_deriv ?_
  rw [xiShiftedAdaptiveBilinearCoefficientSourceMass_comm y
    (fun i => a i y) da]
  ring

/-- Finite coefficient source is exactly the source-first bilinear shear polynomial paired with
the shifted-Xi moment tower. -/
theorem xiShiftedAdaptiveBilinearCoefficientSourceMass_eq_momentFunctional
    {y : ℝ} (hy : 0 < y) {N : ℕ} (a b : Fin N → ℝ) :
    xiShiftedAdaptiveBilinearCoefficientSourceMass y a b =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial
          (finitePolynomialVelocity a) (finitePolynomialVelocity b)) := by
  let acurve : Fin N → ℝ → ℝ := fun i _ => a i
  let bcurve : Fin N → ℝ → ℝ := fun j _ => b j
  let A := finitePolynomialVelocity a
  let B := finitePolynomialVelocity b
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin N))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin N))) (fun j _ =>
      (hasDerivAt_re_xiShiftedReciprocalMoment hy
        ((i : ℕ) + (j : ℕ) + 1)).const_mul (a i * b j)))
  have hfun :
      (∑ i : Fin N, ∑ j : Fin N,
        fun v => a i * b j *
          (xiShiftedReciprocalMoment v ((i : ℕ) + (j : ℕ) + 1)).re) =
        (fun v => HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment v k).re) A (X * B)) := by
    funext v
    have h := momentInner_finitePolynomialCurve_X_curve
      (fun k => (xiShiftedReciprocalMoment v k).re) acurve bcurve v
    simpa only [Finset.sum_apply, acurve, bcurve, A, B, finitePolynomialCurve,
      finitePolynomialVelocity] using h.symm
  rw [hfun] at hsum
  have hsum' : HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re) A (X * B))
      (-xiShiftedAdaptiveBilinearCoefficientSourceMass y a b) y := by
    refine hsum.congr_deriv ?_
    unfold xiShiftedAdaptiveBilinearCoefficientSourceMass
    calc
      (∑ i : Fin N, ∑ j : Fin N,
          a i * b j *
            (-((((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) + 1) *
              (xiShiftedReciprocalMoment y
                ((i : ℕ) + (j : ℕ) + 1 + 1)).re)) =
        ∑ i : Fin N, ∑ j : Fin N,
          -((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i * b j *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = -(∑ i : Fin N, ∑ j : Fin N,
          (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i * b j *
            (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 2)).re) := by
        simp only [Finset.sum_neg_distrib]
  have hsource :=
    hasDerivAt_xiShiftedMomentInner_bilinearCrossing_eq_adaptiveShear hy A B
  have hunique := hsum'.unique hsource
  linarith

/-- The coefficient acceleration is the next completed Euler source layer of the actual
bilinear shear polynomial. -/
theorem xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_momentFunctional
    {y : ℝ} (hy : 0 < y) {N : ℕ} (a b : Fin N → ℝ) :
    xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y a b =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * xiShiftedBoundaryShiftedEuler 1
          (xiShiftedBoundaryAdaptiveBilinearShearPolynomial
            (finitePolynomialVelocity a) (finitePolynomialVelocity b))) := by
  let acurve : Fin N → ℝ → ℝ := fun i _ => a i
  let bcurve : Fin N → ℝ → ℝ := fun j _ => b j
  let zeroM : Fin N → ℝ := fun _ => 0
  let zeroN : Fin N → ℝ := fun _ => 0
  let A := finitePolynomialVelocity a
  let B := finitePolynomialVelocity b
  have hcoeff := hasDerivAt_xiShiftedAdaptiveBilinearCoefficientSourceMass hy
    acurve zeroM bcurve zeroN
    (fun i => hasDerivAt_const (x := y) (a i))
    (fun j => hasDerivAt_const (x := y) (b j))
  have hcoeff' : HasDerivAt
      (fun v => xiShiftedAdaptiveBilinearCoefficientSourceMass v a b)
      (-xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y a b) y := by
    simpa only [acurve, bcurve, zeroM, zeroN,
      xiShiftedAdaptiveBilinearCoefficientSourceMass, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero] using hcoeff
  have hpos : ∀ᶠ v in nhds y, 0 < v := Ioi_mem_nhds hy
  have heq :
      (fun v => xiShiftedAdaptiveBilinearCoefficientSourceMass v a b) =ᶠ[nhds y]
        (fun v => HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment v k).re)
          (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B)) := by
    filter_upwards [hpos] with v hv
    simpa only [A, B] using
      xiShiftedAdaptiveBilinearCoefficientSourceMass_eq_momentFunctional hv a b
  have hcoeffMoment := hcoeff'.congr_of_eventuallyEq heq.symm
  have hsource := hasDerivAt_xiShiftedMomentFunctional_sourceConnection hy
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B)
  have hunique := hcoeffMoment.unique hsource
  linarith

/-- Literal rational--Gamma minus von Mangoldt formation of an arbitrary polynomial source.
The polynomial is selected before either arithmetic aggregation. -/
def xiShiftedPolynomialCompletedArithmeticSource
    (w : ℝ) (Q : Polynomial ℝ) : ℝ :=
  let c := Polynomial.toFn (Q.natDegree + 1) Q
  xiShiftedBoundaryRationalGammaAggregate w 0 c -
    xiShiftedBoundaryVonMangoldtAggregate w 0 c

/-- Arbitrary polynomial source formation is exactly its shifted-Xi moment pairing. -/
theorem xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional
    {w : ℝ} (hw : 1 / 2 < w) (Q : Polynomial ℝ) :
    xiShiftedPolynomialCompletedArithmeticSource w Q =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w) Q := by
  let N := Q.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N Q
  have hc : Polynomial.ofFn N c = Q := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  rw [xiShiftedPolynomialCompletedArithmeticSource]
  change xiShiftedBoundaryRationalGammaAggregate w 0 c -
      xiShiftedBoundaryVonMangoldtAggregate w 0 c = _
  rw [← xiShiftedBoundaryCompletedAggregate_eq_rationalGamma_sub_vonMangoldt hw,
    ← xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w)]
  rw [← hc, Polynomial.ofFn_eq_sum_monomial,
    HTGeometry.momentFunctional_finset_sum]
  simp only [xiShiftedCompletedMomentAggregate, zero_add,
    HTGeometry.momentFunctional_monomial, xiShiftedRealMomentSequence]

/-- At square mass, finite coefficient source is the literal rational--Gamma minus von Mangoldt
bilinear formation. -/
theorem xiShiftedAdaptiveBilinearCoefficientSourceMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) {N : ℕ} (a b : Fin N → ℝ) :
    xiShiftedAdaptiveBilinearCoefficientSourceMass (w ^ (2 : ℕ)) a b =
      xiShiftedAdaptiveBilinearCompletedArithmeticSource w
        (finitePolynomialVelocity a) (finitePolynomialVelocity b) := by
  rw [xiShiftedAdaptiveBilinearCoefficientSourceMass_eq_momentFunctional
    (sq_pos_of_pos (by linarith : 0 < w))]
  exact (xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw
    (finitePolynomialVelocity a) (finitePolynomialVelocity b)).symm

/-- Frozen-hard-edge depth raise of the coefficient source.  It shifts the already formed
bilinear source by one moment without differentiating its reciprocal coefficients. -/
def xiShiftedAdaptiveBilinearCoefficientSourceRadialRaiseMass
    {M N : ℕ} (y : ℝ) (a : Fin M → ℝ) (b : Fin N → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N,
    (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * a i * b j *
      (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 3)).re

/-- Exact chart drift between actual reciprocal-source differentiation and a frozen hard-edge
grading of depth `D`. -/
def xiShiftedAdaptiveBilinearCoefficientSourceChartDriftMass
    {M N : ℕ} (y : ℝ) (D : ℕ) (a : Fin M → ℝ) (b : Fin N → ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N,
    (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) *
      (((D : ℕ) : ℝ) - (((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ)) * a i * b j *
        (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ) + 3)).re

/-- **Radial/actual connection identity.**  Actual source acceleration is frozen radial depth
raise minus the exact grading defect.  This is the coefficient drift omitted by a frozen chart. -/
theorem xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_radialRaise_sub_chartDrift
    {M N : ℕ} (y : ℝ) (D : ℕ) (a : Fin M → ℝ) (b : Fin N → ℝ) :
    xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y a b =
      ((D + 1 : ℕ) : ℝ) *
          xiShiftedAdaptiveBilinearCoefficientSourceRadialRaiseMass y a b -
        xiShiftedAdaptiveBilinearCoefficientSourceChartDriftMass y D a b := by
  unfold xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass
    xiShiftedAdaptiveBilinearCoefficientSourceRadialRaiseMass
    xiShiftedAdaptiveBilinearCoefficientSourceChartDriftMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Actual moving canonical completed source, in squared-mass coordinates. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedAdaptiveBilinearCoefficientSourceMass y
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)

/-- Next completed source layer of the actual canonical admission. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass y
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)

/-- Literal completed rational--Gamma/von Mangoldt presentation of next adaptive source layer. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration
    (w : ℝ) (n : ℕ) : ℝ :=
  let P := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  xiShiftedPolynomialCompletedArithmeticSource w
    (X * xiShiftedBoundaryShiftedEuler 1
      (xiShiftedBoundaryAdaptiveBilinearShearPolynomial P P))

/-- Bilinear inverse-Hankel connection source created by current admission velocity. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass
    (y : ℝ) (n : ℕ) : ℝ :=
  2 * xiShiftedAdaptiveBilinearCoefficientSourceMass y
    (xiShiftedCanonicalAdmissionVelocity y n)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)

/-- Frozen radial component of current canonical source flow. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRadialRaiseMass
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedAdaptiveBilinearCoefficientSourceRadialRaiseMass y
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)

/-- Reciprocal/hard-edge chart drift of current canonical source flow. -/
def xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceChartDriftMass
    (y : ℝ) (n : ℕ) : ℝ :=
  xiShiftedAdaptiveBilinearCoefficientSourceChartDriftMass y (2 * n + 2)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)
    (fun i => xiShiftedCanonicalAdmissionCurve n i y)

/-- **Actual canonical source-flow law.**  Wherever inverse-Hankel admission is effective, the
moving completed source differentiates to next arithmetic layer plus its intrinsic bilinear
admission connection.  No Hankel positivity hypothesis is used. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n)
      (-xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass y n +
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n) y := by
  simpa only [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass] using
    hasDerivAt_xiShiftedAdaptiveDiagonalCoefficientSourceMass hy
      (xiShiftedCanonicalAdmissionCurve n)
      (xiShiftedCanonicalAdmissionVelocity y n)
      (hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet)

/-- **Three-term covariant producer law.**  The actual moving source is frozen radial transport
plus reciprocal-chart drift plus bilinear admission velocity.  These are the three terms that a
fixed hard-edge reporter conflates. -/
theorem hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_radial_add_chart_add_connection
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n)
      (-((2 * n + 3 : ℕ) : ℝ) *
          xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRadialRaiseMass y n +
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceChartDriftMass y n +
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n) y := by
  have h := hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass hy n hdet
  have hsplit :=
    xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_radialRaise_sub_chartDrift
      y (2 * n + 2)
        (fun i => xiShiftedCanonicalAdmissionCurve n i y)
        (fun i => xiShiftedCanonicalAdmissionCurve n i y)
  refine h.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRadialRaiseMass,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceChartDriftMass] at hsplit ⊢
  rw [hsplit]
  push_cast
  ring

/-- Exact source-monotonicity burden in intrinsic coordinates. -/
theorem deriv_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_nonpos_iff
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    deriv (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n) y ≤ 0 ↔
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n ≤
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass y n := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
    hy n hdet).deriv]
  constructor <;> intro h <;> linarith

/-- Same exact burden in hard-edge covariant coordinates.  Frozen radial transport dominates
precisely when it pays both chart drift and admission velocity. -/
theorem deriv_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_nonpos_iff_chart_add_connection_le_radial
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0) :
    deriv (fun v => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass v n) y ≤ 0 ↔
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceChartDriftMass y n +
          xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass y n ≤
        ((2 * n + 3 : ℕ) : ℝ) *
          xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceRadialRaiseMass y n := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_eq_radial_add_chart_add_connection
    hy n hdet).deriv]
  constructor <;> intro h <;> linarith

/-- At square mass, canonical source-mass value is the literal adaptive mixed
rational--Gamma/von Mangoldt source. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ (2 : ℕ)) n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass,
    xiShiftedAdaptiveBilinearCoefficientSourceMass_sq_eq_arithmetic hw,
    ← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw]
  simp only [finitePolynomialVelocity, xiShiftedCanonicalAdmissionCurve]
  rfl

/-- At square mass, canonical connection source is itself the literal bilinear arithmetic
formation of inverse-Hankel velocity against current `P^sharp`. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass (w ^ (2 : ℕ)) n =
      2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w
        (finitePolynomialVelocity
          (xiShiftedCanonicalAdmissionVelocity (w ^ (2 : ℕ)) n))
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass,
    xiShiftedAdaptiveBilinearCoefficientSourceMass_sq_eq_arithmetic hw]
  simp only [finitePolynomialVelocity, xiShiftedCanonicalAdmissionCurve]
  rfl

/-- The next source layer in squared-mass coordinates is its literal completed arithmetic
formation, not an abstract moment reporter. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass_sq_eq_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass (w ^ (2 : ℕ)) n =
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration w n := by
  rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass,
    xiShiftedAdaptiveBilinearCoefficientSourceAccelerationMass_eq_momentFunctional
      (sq_pos_of_pos (by linarith : 0 < w)),
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration,
    xiShiftedPolynomialCompletedArithmeticSource_eq_momentFunctional hw]
  simp only [finitePolynomialVelocity, xiShiftedCanonicalAdmissionCurve]
  rfl

/-- **Literal adaptive mixed source-flow capstone.**  Actual source value and its derivative use
the same current `P^sharp`; derivative contains the next completed source layer and the literal
bilinear admission-velocity source. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow_sq
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) n).det ≠ 0) :
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ (2 : ℕ)) n =
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) ∧
      HasDerivAt
        (fun y => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n)
        (-xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration w n +
          2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w
            (finitePolynomialVelocity
              (xiShiftedCanonicalAdmissionVelocity (w ^ (2 : ℕ)) n))
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n)) (w ^ (2 : ℕ)) := by
  constructor
  · exact xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_eq_arithmetic hw n
  · have h := hasDerivAt_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass
      (sq_pos_of_pos (by linarith : 0 < w)) n hdet
    rw [xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass_sq_eq_arithmetic
      hw n,
      xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass_sq_eq_arithmetic
        hw n] at h
    exact h

/-- Literal square-mass form of exact source-monotonicity burden. -/
theorem deriv_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_sq_nonpos_iff_arithmetic
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) n).det ≠ 0) :
    deriv (fun y => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n)
        (w ^ (2 : ℕ)) ≤ 0 ↔
      2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w
          (finitePolynomialVelocity
            (xiShiftedCanonicalAdmissionVelocity (w ^ (2 : ℕ)) n))
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) ≤
        xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration w n := by
  rw [deriv_xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass_nonpos_iff
      (sq_pos_of_pos (by linarith : 0 < w)) n hdet,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceConnectionMass_sq_eq_arithmetic
      hw n,
    xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAccelerationMass_sq_eq_arithmetic
      hw n]

/-- **Admission-effectivity classification.**  At every physical square mass, either canonical
admission is singular, or the full literal adaptive source-flow law holds.  This makes the only
possible failure location explicit rather than hiding it in a frozen chart. -/
theorem xiShiftedCanonicalAdmissionAdaptiveArithmeticSource_singular_or_flow
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) n).det = 0 ∨
      (xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass (w ^ (2 : ℕ)) n =
          xiShiftedAdaptiveMixedCompletedArithmeticSource w
            (HTGeometry.monicMomentAdmissionPolynomial
              (xiShiftedRealMomentSequence w) n) ∧
        HasDerivAt
          (fun y => xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceMass y n)
          (-xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceAcceleration w n +
            2 * xiShiftedAdaptiveBilinearCompletedArithmeticSource w
              (finitePolynomialVelocity
                (xiShiftedCanonicalAdmissionVelocity (w ^ (2 : ℕ)) n))
              (HTGeometry.monicMomentAdmissionPolynomial
                (xiShiftedRealMomentSequence w) n)) (w ^ (2 : ℕ))) := by
  by_cases hdet : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) n).det = 0
  · exact Or.inl hdet
  · exact Or.inr (xiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow_sq
      hw n hdet)

end

end RHTower
