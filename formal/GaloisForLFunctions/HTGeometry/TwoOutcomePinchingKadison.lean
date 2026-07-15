import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# Two-outcome pinching and its exact Kadison defect

For an idempotent effect `e`, the two-outcome pinching

`Phi_e(X) = eXe + (1-e)X(1-e)`

has an exact multiplicativity defect.  On a self-adjoint observable it is not merely positive by
the Kadison--Schwarz inequality: it is the sum of the two transition-channel master constraints.
Consequently every state reads the defect as the sum of two squared transition amplitudes.

This is a general static value identity for the hypertranscendental constraint corpus.  It does
not assume a Hamiltonian, a time evolution, finite dimension, or a zeta specialization.

Physics provenance: the nonselective projective state change is due to G. Lueders, Annalen der
Physik 443 (1950), 322--328, DOI 10.1002/andp.19504430510.  The encompassing operator Schwarz
inequality is due to R. V. Kadison, Annals of Mathematics 56 (1952), 494--503,
DOI 10.2307/1969657.
-/

namespace HTGeometry

noncomputable section

variable {R : Type*} [Ring R]

/-- The nonselective two-outcome pinching associated with an algebraic cutoff. -/
def twoOutcomePinching (e X : R) : R :=
  e * X * e + (1 - e) * X * (1 - e)

/-- Failure of the two-outcome pinching to preserve the square of one observable. -/
def twoOutcomePinchingKadisonDefect (e X : R) : R :=
  twoOutcomePinching e (X * X) -
    twoOutcomePinching e X * twoOutcomePinching e X

/-- Transition from the measured sector to its complement. -/
def twoOutcomeLowerTransition (e X : R) : R :=
  (1 - e) * X * e

/-- Transition from the complementary sector back to the measured sector. -/
def twoOutcomeUpperTransition (e X : R) : R :=
  e * X * (1 - e)

/-- **Exact two-outcome Kadison defect.**  For an idempotent cutoff, the multiplicativity defect
of pinching is the sum of the two oriented round-trip transition products. -/
theorem twoOutcomePinchingKadisonDefect_eq_transitionProducts
    {e : R} (he : IsIdempotentElem e) (X : R) :
    twoOutcomePinchingKadisonDefect e X =
      twoOutcomeUpperTransition e X * twoOutcomeLowerTransition e X +
        twoOutcomeLowerTransition e X * twoOutcomeUpperTransition e X := by
  have hee : e * e = e := he
  simp only [twoOutcomePinchingKadisonDefect, twoOutcomePinching,
    twoOutcomeLowerTransition, twoOutcomeUpperTransition]
  let f : R := 1 - e
  let A : R := e * X * e
  let B : R := f * X * f
  let C : R := e * X * f
  let D : R := f * X * e
  have hff : f * f = f := by
    dsimp only [f]
    noncomm_ring [hee]
  have hef : e * f = 0 := by
    dsimp only [f]
    noncomm_ring [hee]
  have hfe : f * e = 0 := by
    dsimp only [f]
    noncomm_ring [hee]
  have hsum : e + f = 1 := by
    dsimp only [f]
    noncomm_ring
  have hAA : A * A = e * X * e * X * e := by
    dsimp only [A]
    calc
      (e * X * e) * (e * X * e) = e * X * (e * e) * X * e := by
        noncomm_ring
      _ = e * X * e * X * e := by rw [hee]
  have hBB : B * B = f * X * f * X * f := by
    dsimp only [B]
    calc
      (f * X * f) * (f * X * f) = f * X * (f * f) * X * f := by
        noncomm_ring
      _ = f * X * f * X * f := by rw [hff]
  have hCD : C * D = e * X * f * X * e := by
    dsimp only [C, D]
    calc
      (e * X * f) * (f * X * e) = e * X * (f * f) * X * e := by
        noncomm_ring
      _ = e * X * f * X * e := by rw [hff]
  have hDC : D * C = f * X * e * X * f := by
    dsimp only [D, C]
    calc
      (f * X * e) * (e * X * f) = f * X * (e * e) * X * f := by
        noncomm_ring
      _ = f * X * e * X * f := by rw [hee]
  have hExx : e * (X * X) * e = A * A + C * D := by
    rw [hAA, hCD]
    calc
      e * (X * X) * e = e * X * 1 * X * e := by noncomm_ring
      _ = e * X * (e + f) * X * e := by rw [hsum]
      _ = e * X * e * X * e + e * X * f * X * e := by noncomm_ring
  have hFxx : f * (X * X) * f = B * B + D * C := by
    rw [hBB, hDC]
    calc
      f * (X * X) * f = f * X * 1 * X * f := by noncomm_ring
      _ = f * X * (e + f) * X * f := by rw [hsum]
      _ = f * X * f * X * f + f * X * e * X * f := by noncomm_ring
  have hAB : A * B = 0 := by
    calc
      A * B = e * X * (e * f) * X * f := by
        dsimp only [A, B]
        noncomm_ring
      _ = 0 := by rw [hef]; simp
  have hBA : B * A = 0 := by
    calc
      B * A = f * X * (f * e) * X * e := by
        dsimp only [B, A]
        noncomm_ring
      _ = 0 := by rw [hfe]; simp
  change e * (X * X) * e + f * (X * X) * f -
      (A + B) * (A + B) = C * D + D * C
  rw [hExx, hFxx]
  simp only [mul_add, add_mul, hAB, hBA, add_zero, zero_add]
  abel

variable [StarRing R]

/-- For self-adjoint cutoff and observable, the exact Kadison defect is a sum of two positive
master products.  This is the algebraic equality underlying Kadison--Schwarz positivity for a
two-block Lueders channel. -/
theorem twoOutcomePinchingKadisonDefect_eq_transitionMasterProducts
    {e X : R} (he : IsIdempotentElem e) (heStar : star e = e)
    (hXStar : star X = X) :
    twoOutcomePinchingKadisonDefect e X =
      star (twoOutcomeLowerTransition e X) * twoOutcomeLowerTransition e X +
        star (twoOutcomeUpperTransition e X) * twoOutcomeUpperTransition e X := by
  rw [twoOutcomePinchingKadisonDefect_eq_transitionProducts he X]
  simp only [twoOutcomeLowerTransition, twoOutcomeUpperTransition, star_mul,
    star_sub, star_one, heStar, hXStar]
  noncomm_ring

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

/-- Operator form: the Lueders/Kadison defect is exactly the sum of the two transition-channel
quantum master constraints. -/
theorem twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_sum
    (e X : E →L[k] E) (he : IsIdempotentElem e)
    (heAdj : e.adjoint = e) (hXAdj : X.adjoint = X) :
    twoOutcomePinchingKadisonDefect e X =
      quantumMasterConstraint (twoOutcomeLowerTransition e X) +
        quantumMasterConstraint (twoOutcomeUpperTransition e X) := by
  have heStar : star e = e := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using heAdj
  have hXStar : star X = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hXAdj
  simpa only [quantumMasterConstraint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint] using
      (twoOutcomePinchingKadisonDefect_eq_transitionMasterProducts
        he heStar hXStar)

/-- State-value form: every vector reads the pinching multiplicativity defect as the sum of the
squared lower and upper transition amplitudes. -/
theorem re_inner_twoOutcomePinchingKadisonDefect_eq_transitionNormSq_add
    (e X : E →L[k] E) (he : IsIdempotentElem e)
    (heAdj : e.adjoint = e) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re (inner k psi (twoOutcomePinchingKadisonDefect e X psi)) =
      ‖twoOutcomeLowerTransition e X psi‖ ^ 2 +
        ‖twoOutcomeUpperTransition e X psi‖ ^ 2 := by
  rw [twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_sum
    e X he heAdj hXAdj]
  simp only [ContinuousLinearMap.add_apply, inner_add_right, map_add,
    re_inner_quantumMasterConstraint_eq_normSq]

/-- The two-outcome Kadison defect has nonnegative expectation with no additional positivity
hypothesis on the defect operator. -/
theorem re_inner_twoOutcomePinchingKadisonDefect_nonneg
    (e X : E →L[k] E) (he : IsIdempotentElem e)
    (heAdj : e.adjoint = e) (hXAdj : X.adjoint = X) (psi : E) :
    0 ≤ RCLike.re (inner k psi (twoOutcomePinchingKadisonDefect e X psi)) := by
  rw [re_inner_twoOutcomePinchingKadisonDefect_eq_transitionNormSq_add
    e X he heAdj hXAdj psi]
  positivity

end

end HTGeometry
