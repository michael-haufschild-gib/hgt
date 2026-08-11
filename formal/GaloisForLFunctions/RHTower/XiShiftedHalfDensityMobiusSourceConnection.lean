import GaloisForLFunctions.RHTower.XiShiftedAdaptiveAdmissionCovariantSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionArithmeticTransgression

/-!
# Half-density Möbius connection for the shifted-Xi arithmetic source

Shifted reciprocal moments obey the Möbius transport law
`s_k' = -(k+1)s_(k+1)`.  Its polynomial metric has a unique first-order half-density
connection

`K P = X^2 P' + (1/2) X P`.

The connection is forced before arithmetic aggregation: it splits the literal completed adaptive
source into multiplication Gram bulk and connection cost.  Its covariant multiplication law is
the nonisospectral Riccati identity `nabla(XP) - X nabla(P) = -X^2 P`.  Consequently a
source-parallel amplitude has strictly decreasing odd current on every positive moment form.

The final statement also exposes the exact effectivity wall.  `K` raises polynomial degree by one,
so strict source-parallel dissipation does not remain inside any fixed finite admission flag.
-/

open Complex Matrix Polynomial

namespace RHTower

noncomputable section

/-- Weight-`c` polynomial lift of the infinitesimal mass Möbius vector field. -/
def xiShiftedMobiusDensityGenerator (c : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  X ^ 2 * P.derivative + c • (X * P)

/-- The uniquely metric-compatible weight is one half. -/
def xiShiftedMobiusHalfDensityGenerator (P : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedMobiusDensityGenerator (1 / 2) P

/-- Covariant velocity of a polynomial amplitude under shifted mass transport. -/
def xiShiftedMobiusHalfDensityCovariantVelocity
    (V P : Polynomial ℝ) : Polynomial ℝ :=
  V - xiShiftedMobiusHalfDensityGenerator P

/-- Leibniz expansion for a general density weight. -/
theorem xiShiftedMobiusDensityGenerator_product
    (c : ℝ) (P Q : Polynomial ℝ) :
    xiShiftedMobiusDensityGenerator c P * Q +
        P * xiShiftedMobiusDensityGenerator c Q =
      X ^ 2 * (P * Q).derivative + c • (X * (P * Q)) +
        c • (X * (P * Q)) := by
  simp only [xiShiftedMobiusDensityGenerator, Polynomial.derivative_mul,
    Polynomial.smul_eq_C_mul]
  ring

/-- Half-density generator exactly splits the shifted moment source of a product. -/
theorem xiShiftedMobiusHalfDensityGenerator_product
    (P Q : Polynomial ℝ) :
    xiShiftedMobiusHalfDensityGenerator P * Q +
        P * xiShiftedMobiusHalfDensityGenerator Q =
      X * xiShiftedBoundaryShiftedEuler 1 (P * Q) := by
  simp only [xiShiftedMobiusHalfDensityGenerator]
  rw [xiShiftedMobiusDensityGenerator_product]
  simp only [xiShiftedBoundaryShiftedEuler, Polynomial.smul_eq_C_mul]
  simp only [Polynomial.C_1, one_mul]
  have hhalf : Polynomial.C (1 / 2 : ℝ) + Polynomial.C (1 / 2 : ℝ) = 1 := by
    rw [← Polynomial.C_add]
    norm_num
  linear_combination (X * (P * Q)) * hhalf

/-- **Uniqueness of half density.**  Among generators `X^2 d/dX + cX`, metric compatibility
for every polynomial pair forces `c = 1/2`. -/
theorem xiShiftedMobiusDensityGenerator_product_eq_source_iff
    (c : ℝ) :
    (∀ P Q : Polynomial ℝ,
      xiShiftedMobiusDensityGenerator c P * Q +
          P * xiShiftedMobiusDensityGenerator c Q =
        X * xiShiftedBoundaryShiftedEuler 1 (P * Q)) ↔
      c = 1 / 2 := by
  constructor
  · intro h
    have hcoeff := congrArg (fun R : Polynomial ℝ => R.coeff 1)
      (h (1 : Polynomial ℝ) (1 : Polynomial ℝ))
    norm_num [xiShiftedMobiusDensityGenerator,
      xiShiftedBoundaryShiftedEuler] at hcoeff
    linarith
  · rintro rfl
    exact xiShiftedMobiusHalfDensityGenerator_product

/-- The half-density generator has the exact quadratic commutator with multiplication. -/
theorem xiShiftedMobiusHalfDensityGenerator_X_mul (P : Polynomial ℝ) :
    xiShiftedMobiusHalfDensityGenerator (X * P) =
      X * xiShiftedMobiusHalfDensityGenerator P + X ^ 2 * P := by
  simp only [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
    Polynomial.derivative_mul, Polynomial.derivative_X, one_mul,
    Polynomial.smul_eq_C_mul]
  ring

/-- **Covariant multiplication Riccati law.**  Multiplication by `X` has covariant derivative
`-X^2` under the source-forced half-density connection. -/
theorem xiShiftedMobiusHalfDensityCovariantVelocity_X
    (V P : Polynomial ℝ) :
    xiShiftedMobiusHalfDensityCovariantVelocity (X * V) (X * P) =
      X * xiShiftedMobiusHalfDensityCovariantVelocity V P - X ^ 2 * P := by
  rw [xiShiftedMobiusHalfDensityCovariantVelocity,
    xiShiftedMobiusHalfDensityCovariantVelocity,
    xiShiftedMobiusHalfDensityGenerator_X_mul]
  ring

/-- The source-forced connection raises every monomial by one, with nonvanishing half-integral
coefficient.  This is the algebraic mechanism behind its finite-admission obstruction. -/
theorem xiShiftedMobiusHalfDensityGenerator_X_pow (n : ℕ) :
    xiShiftedMobiusHalfDensityGenerator ((X : Polynomial ℝ) ^ n) =
      ((n : ℝ) + 1 / 2) • (X : Polynomial ℝ) ^ (n + 1) := by
  cases n with
  | zero =>
      norm_num [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator]
  | succ n =>
      simp only [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
        Polynomial.derivative_X_pow_succ, Polynomial.smul_eq_C_mul]
      push_cast
      have hc : Polynomial.C (1 + (n : ℝ)) + Polynomial.C (1 / 2 : ℝ) =
          Polynomial.C (3 / 2 + (n : ℝ)) := by
        rw [← Polynomial.C_add]
        congr 1
        ring
      calc
        _ = X ^ 2 * X ^ n *
            (Polynomial.C (1 + (n : ℝ)) + Polynomial.C (1 / 2 : ℝ)) := by ring
        _ = X ^ 2 * X ^ n * Polynomial.C (3 / 2 + (n : ℝ)) := by rw [hc]
        _ = _ := by ring

/-- Exact degree growth of the source connection on the top monomial. -/
theorem natDegree_xiShiftedMobiusHalfDensityGenerator_X_pow (n : ℕ) :
    (xiShiftedMobiusHalfDensityGenerator ((X : Polynomial ℝ) ^ n)).natDegree =
      n + 1 := by
  rw [xiShiftedMobiusHalfDensityGenerator_X_pow, Polynomial.smul_eq_C_mul,
    Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_X_pow]

/-- **Finite-admission effectivity obstruction.**  No fixed degree flag is invariant under the
arithmetic source connection.  Thus a finite Hankel face can observe the source flow but cannot
faithfully carry source-parallel transport. -/
theorem xiShiftedMobiusHalfDensityGenerator_not_preserve_degree_flag (n : ℕ) :
    ¬ ∀ P : Polynomial ℝ, P.natDegree ≤ n →
      (xiShiftedMobiusHalfDensityGenerator P).natDegree ≤ n := by
  intro h
  have hout := h ((X : Polynomial ℝ) ^ n) (by simp)
  rw [natDegree_xiShiftedMobiusHalfDensityGenerator_X_pow] at hout
  omega

/-- The adaptive bilinear shear is exactly multiplication Gram bulk plus the two half-density
connection costs. -/
theorem xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_halfDensityLanding
    (P Q : Polynomial ℝ) :
    xiShiftedBoundaryAdaptiveBilinearShearPolynomial P Q =
      xiShiftedMobiusHalfDensityGenerator P * (X * Q) +
        (X * P) * xiShiftedMobiusHalfDensityGenerator Q +
        (X * P) * (X * Q) := by
  simp only [xiShiftedBoundaryAdaptiveBilinearShearPolynomial,
    xiShiftedBoundaryShiftedEuler, xiShiftedMobiusHalfDensityGenerator,
    xiShiftedMobiusDensityGenerator, Polynomial.smul_eq_C_mul]
  simp only [Polynomial.C_1, one_mul]
  have hhalf : Polynomial.C (1 / 2 : ℝ) + Polynomial.C (1 / 2 : ℝ) = 1 := by
    rw [← Polynomial.C_add]
    norm_num
  have hscaled :
      Polynomial.C (1 / 2 : ℝ) * ((X * P) * (X * Q)) +
          Polynomial.C (1 / 2 : ℝ) * ((X * P) * (X * Q)) =
        (X * P) * (X * Q) := by
    calc
      _ = (Polynomial.C (1 / 2 : ℝ) + Polynomial.C (1 / 2 : ℝ)) *
          ((X * P) * (X * Q)) := by ring
      _ = (X * P) * (X * Q) := by rw [hhalf, one_mul]
  calc
    _ = X ^ 2 * P.derivative * (X * Q) +
        (X * P) * (X ^ 2 * Q.derivative) +
        2 * ((X * P) * (X * Q)) := by ring
    _ = X ^ 2 * P.derivative * (X * Q) +
        (X * P) * (X ^ 2 * Q.derivative) +
        (Polynomial.C (1 / 2 : ℝ) * ((X * P) * (X * Q)) +
          Polynomial.C (1 / 2 : ℝ) * ((X * P) * (X * Q))) +
        (X * P) * (X * Q) := by rw [hscaled]; ring
    _ = _ := by ring

/-- **Literal bilinear arithmetic half-density landing.**  Amplitudes enter the forced connection
before rational--Gamma and von Mangoldt aggregation. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_halfDensityLanding
    {w : ℝ} (hw : 1 / 2 < w) (P Q : Polynomial ℝ) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w P Q =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedMobiusHalfDensityGenerator P * (X * Q) +
          (X * P) * xiShiftedMobiusHalfDensityGenerator Q +
          (X * P) * (X * Q)) := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw,
    xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_halfDensityLanding]
  rfl

/-- **Completed `P^sharp` half-density source law.**  On the diagonal, the literal completed
adaptive source is positive multiplication Gram bulk plus twice the connection cost. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_halfDensityLanding
    {w : ℝ} (hw : 1 / 2 < w) (P : Polynomial ℝ) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w P =
      HTGeometry.momentInner (xiShiftedRealMomentSequence w) (X * P) (X * P) +
        2 * HTGeometry.momentInner (xiShiftedRealMomentSequence w)
          (xiShiftedMobiusHalfDensityGenerator P) (X * P) := by
  rw [← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw,
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_halfDensityLanding hw]
  rw [HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_add]
  simp only [HTGeometry.momentInner_def]
  have hcomm :
      xiShiftedMobiusHalfDensityGenerator P * (X * P) =
        (X * P) * xiShiftedMobiusHalfDensityGenerator P := by ring
  rw [hcomm]
  ring

/-- **Moving odd-current half-density law.**  The full derivative is a covariant connection
pairing minus the multiplication Gram bulk. -/
theorem hasDerivAt_xiShiftedMovingOddCurrent_eq_halfDensityConnection
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c : Fin N → ℝ → ℝ) (dc : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v))
      (2 * HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (xiShiftedMobiusHalfDensityCovariantVelocity
            (finitePolynomialVelocity dc) (finitePolynomialCurve c y))
          (X * finitePolynomialCurve c y) -
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * finitePolynomialCurve c y) (X * finitePolynomialCurve c y)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := finitePolynomialCurve c y
  let V := finitePolynomialVelocity dc
  have hraw := hasDerivAt_xiShiftedMomentInner_movingOddCurrent hy c dc hc
  have hsource : X * xiShiftedBoundaryShiftedEuler 1 P =
      xiShiftedMobiusHalfDensityGenerator P + (1 / 2 : ℝ) • (X * P) := by
    simp only [xiShiftedMobiusHalfDensityGenerator,
      xiShiftedMobiusDensityGenerator, xiShiftedBoundaryShiftedEuler,
      Polynomial.smul_eq_C_mul]
    simp only [Polynomial.C_1, one_mul]
    have hhalf : Polynomial.C (1 / 2 : ℝ) + Polynomial.C (1 / 2 : ℝ) = 1 := by
      rw [← Polynomial.C_add]
      norm_num
    have hscaled :
        Polynomial.C (1 / 2 : ℝ) * (X * P) +
            Polynomial.C (1 / 2 : ℝ) * (X * P) = X * P := by
      calc
        _ = (Polynomial.C (1 / 2 : ℝ) + Polynomial.C (1 / 2 : ℝ)) *
            (X * P) := by ring
        _ = X * P := by rw [hhalf, one_mul]
    calc
      _ = X ^ 2 * P.derivative + X * P := by ring
      _ = X ^ 2 * P.derivative +
          (Polynomial.C (1 / 2 : ℝ) * (X * P) +
            Polynomial.C (1 / 2 : ℝ) * (X * P)) := by rw [hscaled]
      _ = _ := by ring
  have hcomm : HTGeometry.momentInner s (X * P)
      (xiShiftedMobiusHalfDensityGenerator P) =
      HTGeometry.momentInner s (xiShiftedMobiusHalfDensityGenerator P)
        (X * P) := HTGeometry.momentInner_comm _ _ _
  rw [show finitePolynomialCurve c y = P by rfl,
    show finitePolynomialVelocity dc = V by rfl, hsource,
    HTGeometry.momentInner_add_right, HTGeometry.momentInner_smul_right,
    hcomm] at hraw
  apply hraw.congr_deriv
  simp only [xiShiftedMobiusHalfDensityCovariantVelocity,
    HTGeometry.momentInner_sub_left, s, P, V]
  ring

/-- Source-parallel half-density transport turns odd current into a negative multiplication
square at the chosen mass. -/
theorem hasDerivAt_xiShiftedMovingOddCurrent_eq_neg_sq_of_halfDensityParallel
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c : Fin N → ℝ → ℝ) (dc : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y)
    (hparallel : finitePolynomialVelocity dc =
      xiShiftedMobiusHalfDensityGenerator (finitePolynomialCurve c y)) :
    HasDerivAt
      (fun v => HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (finitePolynomialCurve c v) (X * finitePolynomialCurve c v))
      (-HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * finitePolynomialCurve c y) (X * finitePolynomialCurve c y)) y := by
  have h := hasDerivAt_xiShiftedMovingOddCurrent_eq_halfDensityConnection hy c dc hc
  rw [xiShiftedMobiusHalfDensityCovariantVelocity, hparallel, sub_self,
    HTGeometry.momentInner_zero_left] at h
  simpa only [mul_zero, zero_sub] using h

/-- Under a positive moment form, every nonzero source-parallel amplitude has strictly decreasing
odd current.  This is the exact positive survivor of the connection law. -/
theorem deriv_xiShiftedMovingOddCurrent_neg_of_halfDensityParallel
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (c : Fin N → ℝ → ℝ) (dc : Fin N → ℝ)
    (hc : ∀ i : Fin N, HasDerivAt (c i) (dc i) y)
    (hparallel : finitePolynomialVelocity dc =
      xiShiftedMobiusHalfDensityGenerator (finitePolynomialCurve c y))
    (hpos : HTGeometry.PositiveMomentForm
      (fun k => (xiShiftedReciprocalMoment y k).re))
    (hP : finitePolynomialCurve c y ≠ 0) :
    deriv (fun v => HTGeometry.momentInner
      (fun k => (xiShiftedReciprocalMoment v k).re)
      (finitePolynomialCurve c v) (X * finitePolynomialCurve c v)) y < 0 := by
  rw [(hasDerivAt_xiShiftedMovingOddCurrent_eq_neg_sq_of_halfDensityParallel
    hy c dc hc hparallel).deriv]
  have hXP : X * finitePolynomialCurve c y ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero hP
  exact neg_lt_zero.mpr (hpos.pos_of_ne_zero _ hXP)

end

end RHTower
