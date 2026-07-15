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

/-- The part of an observable erased by two-outcome pinching is exactly the sum of its two
oriented cross-sector transitions. -/
theorem sub_twoOutcomePinching_eq_transition_sum
    {e : R} (he : IsIdempotentElem e) (X : R) :
    X - twoOutcomePinching e X =
      twoOutcomeUpperTransition e X + twoOutcomeLowerTransition e X := by
  have hee : e * e = e := he
  simp only [twoOutcomePinching, twoOutcomeUpperTransition,
    twoOutcomeLowerTransition]
  noncomm_ring [hee]

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

/-- **Kadison defect as erased-observable master product.**  The complete multiplicativity
defect of a two-outcome measurement is the positive square of precisely the part of the
observable erased by that measurement. -/
theorem twoOutcomePinchingKadisonDefect_eq_disturbanceMasterProduct
    {e X : R} (he : IsIdempotentElem e) (heStar : star e = e)
    (hXStar : star X = X) :
    twoOutcomePinchingKadisonDefect e X =
      star (X - twoOutcomePinching e X) * (X - twoOutcomePinching e X) := by
  have hee : e * e = e := he
  rw [twoOutcomePinchingKadisonDefect_eq_transitionMasterProducts he heStar hXStar]
  rw [sub_twoOutcomePinching_eq_transition_sum he X]
  have hUpperStar : star (twoOutcomeUpperTransition e X) =
      twoOutcomeLowerTransition e X := by
    simp [twoOutcomeUpperTransition, twoOutcomeLowerTransition, star_mul,
      star_sub, heStar, hXStar, mul_assoc]
  have hLowerStar : star (twoOutcomeLowerTransition e X) =
      twoOutcomeUpperTransition e X := by
    simp [twoOutcomeUpperTransition, twoOutcomeLowerTransition, star_mul,
      star_sub, heStar, hXStar, mul_assoc]
  have hef : e * (1 - e) = 0 := by
    noncomm_ring [hee]
  have hfe : (1 - e) * e = 0 := by
    noncomm_ring [hee]
  have hUpperSq : twoOutcomeUpperTransition e X *
      twoOutcomeUpperTransition e X = 0 := by
    simp only [twoOutcomeUpperTransition]
    calc
      (e * X * (1 - e)) * (e * X * (1 - e)) =
          e * X * ((1 - e) * e) * X * (1 - e) := by noncomm_ring
      _ = 0 := by rw [hfe]; simp
  have hLowerSq : twoOutcomeLowerTransition e X *
      twoOutcomeLowerTransition e X = 0 := by
    simp only [twoOutcomeLowerTransition]
    calc
      ((1 - e) * X * e) * ((1 - e) * X * e) =
          (1 - e) * X * (e * (1 - e)) * X * e := by noncomm_ring
      _ = 0 := by rw [hef]; simp
  rw [star_add, hUpperStar, hLowerStar]
  noncomm_ring [hUpperSq, hLowerSq]

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

/-- Operator form of the erased-observable identity.  It collapses the two transition master
constraints to the single master constraint of the measurement disturbance `X - Φ(X)`. -/
theorem twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_disturbance
    (e X : E →L[k] E) (he : IsIdempotentElem e)
    (heAdj : e.adjoint = e) (hXAdj : X.adjoint = X) :
    twoOutcomePinchingKadisonDefect e X =
      quantumMasterConstraint (X - twoOutcomePinching e X) := by
  have heStar : star e = e := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using heAdj
  have hXStar : star X = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hXAdj
  simpa only [quantumMasterConstraint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint] using
      (twoOutcomePinchingKadisonDefect_eq_disturbanceMasterProduct
        he heStar hXStar)

/-- Every state reads the pinching Kadison defect as exactly the squared norm of the erased
observable component. -/
theorem re_inner_twoOutcomePinchingKadisonDefect_eq_disturbanceNormSq
    (e X : E →L[k] E) (he : IsIdempotentElem e)
    (heAdj : e.adjoint = e) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re (inner k psi (twoOutcomePinchingKadisonDefect e X psi)) =
      ‖(X - twoOutcomePinching e X) psi‖ ^ 2 := by
  rw [twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_disturbance
    e X he heAdj hXAdj]
  exact re_inner_quantumMasterConstraint_eq_normSq
    (X - twoOutcomePinching e X) psi

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

/-! ### Involutive clock twirling is projective pinching -/

omit [CompleteSpace E] in
/-- The two-element state average is the symmetric/antisymmetric projector `(1 + U) / 2`.
This formula requires no period hypothesis. -/
theorem finiteInvolutiveGaugeAverage_apply
    (U : E →L[k] E) (psi : E) :
    finiteCyclicGaugeAverage U 2 psi =
      ((2 : k)⁻¹) • (psi + U psi) := by
  simp [finiteCyclicGaugeAverage, finiteCyclicGaugeSum, add_comm]

omit [CompleteSpace E] in
/-- For an involutive clock step, the two-element observable twirl is the exact conjugation
symmetrizer `(A + U A U) / 2`. -/
theorem finiteInvolutiveObservableTwirl_eq_symmetrizer
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    finiteCyclicObservableTwirl U X 2 =
      ((2 : k)⁻¹) • (U * X * U + X) := by
  simp [finiteCyclicObservableTwirl, finiteCyclicObservableTwirlNumerator,
    hsq, add_comm, mul_assoc]

omit [CompleteSpace E] in
/-- The observable component erased by a two-reading clock is exactly half the clock--observable
commutator, followed by the clock step.  This is an operator identity and requires neither a
state nor a temporal evolution. -/
theorem sub_finiteInvolutiveObservableTwirl_eq_half_commutator_mul
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    X - finiteCyclicObservableTwirl U X 2 =
      ((2 : k)⁻¹) • ((X * U - U * X) * U) := by
  rw [finiteInvolutiveObservableTwirl_eq_symmetrizer U X hsq]
  have hUU : U * U = 1 := by
    simpa only [pow_two] using hsq
  have hcomm_mul : (X * U - U * X) * U = X - U * X * U := by
    calc
      (X * U - U * X) * U = X * (U * U) - U * X * U := by noncomm_ring
      _ = X - U * X * U := by rw [hUU]; simp
  rw [hcomm_mul]
  module

omit [CompleteSpace E] in
/-- **Clock-observation/pinching identity.**  Twirling an observable by an involutive clock is
exactly the nonselective projective measurement associated with the clock's invariant and
anti-invariant sectors.  This identifies observer-algebra averaging with an existing static
measurement operation, without introducing a time parameter. -/
theorem twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    twoOutcomePinching (finiteCyclicGaugeAverage U 2) X =
      finiteCyclicObservableTwirl U X 2 := by
  apply ContinuousLinearMap.ext
  intro psi
  rw [finiteInvolutiveObservableTwirl_eq_symmetrizer U X hsq,
    ContinuousLinearMap.smul_apply]
  simp only [twoOutcomePinching, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]
  simp_rw [finiteInvolutiveGaugeAverage_apply U]
  simp only [map_add, map_sub, map_smul]
  module

/-- Multiplicativity defect of the two-reading clock-observer twirl on a self-adjoint
observable. -/
def finiteInvolutiveObservableTwirlKadisonDefect
    (U X : E →L[k] E) : E →L[k] E :=
  finiteCyclicObservableTwirl U (X * X) 2 -
    finiteCyclicObservableTwirl U X 2 * finiteCyclicObservableTwirl U X 2

omit [CompleteSpace E] in
/-- The clock-twirl defect is literally the already-formalized two-outcome pinching defect for
the invariant-sector projector. -/
theorem finiteInvolutiveObservableTwirlKadisonDefect_eq_pinching
    (U X : E →L[k] E) (hsq : U ^ 2 = 1) :
    finiteInvolutiveObservableTwirlKadisonDefect U X =
      twoOutcomePinchingKadisonDefect (finiteCyclicGaugeAverage U 2) X := by
  rw [finiteInvolutiveObservableTwirlKadisonDefect,
    twoOutcomePinchingKadisonDefect,
    twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl U (X * X) hsq,
    twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl U X hsq]

/-- **Static clock-observability energy.**  Every state reads the multiplicativity defect of an
involutive unitary clock twirl as the sum of the two squared transition amplitudes between the
clock's invariant and anti-invariant sectors. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_transitionNormSq_add
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) =
      ‖twoOutcomeLowerTransition (finiteCyclicGaugeAverage U 2) X psi‖ ^ 2 +
        ‖twoOutcomeUpperTransition (finiteCyclicGaugeAverage U 2) X psi‖ ^ 2 := by
  rw [finiteInvolutiveObservableTwirlKadisonDefect_eq_pinching U X hsq]
  have hPAdj : (finiteCyclicGaugeAverage U 2).adjoint =
      finiteCyclicGaugeAverage U 2 := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (finiteInvolutiveGaugeAverage_isSelfAdjoint U hadjoint_mul hsq).star_eq
  exact re_inner_twoOutcomePinchingKadisonDefect_eq_transitionNormSq_add
    (finiteCyclicGaugeAverage U 2) X
    (finiteInvolutiveGaugeAverage_isIdempotentElem U hsq) hPAdj hXAdj psi

/-- The involutive clock-twirl defect is the single master constraint of the observable part
erased by clock averaging.  This removes the two separate transition channels from downstream
master-constraint and Ward arguments. -/
theorem finiteInvolutiveObservableTwirlKadisonDefect_eq_quantumMasterConstraint_disturbance
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) :
    finiteInvolutiveObservableTwirlKadisonDefect U X =
      quantumMasterConstraint (X - finiteCyclicObservableTwirl U X 2) := by
  rw [finiteInvolutiveObservableTwirlKadisonDefect_eq_pinching U X hsq]
  have hPAdj : (finiteCyclicGaugeAverage U 2).adjoint =
      finiteCyclicGaugeAverage U 2 := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (finiteInvolutiveGaugeAverage_isSelfAdjoint U hadjoint_mul hsq).star_eq
  rw [twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_disturbance
    (finiteCyclicGaugeAverage U 2) X
    (finiteInvolutiveGaugeAverage_isIdempotentElem U hsq) hPAdj hXAdj,
    twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl U X hsq]

/-- **Exact clock-observability criterion.**  For a self-adjoint quantity observed by an
involutive unitary clock, the complete twirl defect vanishes exactly when the quantity belongs
to the clock commutant.  Hence the defect detects observational incompatibility without any
reference to temporal evolution or to a chosen state. -/
theorem finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutes
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) :
    finiteInvolutiveObservableTwirlKadisonDefect U X = 0 ↔
      U * X = X * U := by
  rw [finiteInvolutiveObservableTwirlKadisonDefect_eq_quantumMasterConstraint_disturbance
    U X hadjoint_mul hsq hXAdj]
  constructor
  · intro hzero
    have hdisturbance : X - finiteCyclicObservableTwirl U X 2 = 0 :=
      (quantumMasterConstraint_eq_zero_iff
        (X - finiteCyclicObservableTwirl U X 2)).mp hzero
    have hX : X = finiteCyclicObservableTwirl U X 2 :=
      sub_eq_zero.mp hdisturbance
    rw [hX]
    exact finiteCyclicObservableTwirl_commutes U X 2 hsq
  · intro hcomm
    have htwirl : finiteCyclicObservableTwirl U X 2 = X :=
      finiteCyclicObservableTwirl_eq_self_of_commutes U X 2 (by norm_num) hsq hcomm
    rw [htwirl, sub_self]
    exact (quantumMasterConstraint_eq_zero_iff (0 : E →L[k] E)).mpr rfl

/-- State-value form: the clock-observability energy is exactly the squared norm of the
observable component erased by the clock conditional expectation. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_disturbanceNormSq
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) =
      ‖(X - finiteCyclicObservableTwirl U X 2) psi‖ ^ 2 := by
  rw [finiteInvolutiveObservableTwirlKadisonDefect_eq_quantumMasterConstraint_disturbance
    U X hadjoint_mul hsq hXAdj]
  exact re_inner_quantumMasterConstraint_eq_normSq
    (X - finiteCyclicObservableTwirl U X 2) psi

/-- **State-independent clock commutator law.**  Every state reads the clock-observability
defect as one quarter of the squared commutator evaluated on the clock-shifted state.  The
stationary law below is the fixed-state specialization `U psi = psi`. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_shifted
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) =
      (4 : ℝ)⁻¹ * ‖((X * U - U * X) : E →L[k] E) (U psi)‖ ^ 2 := by
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_disturbanceNormSq
    U X hadjoint_mul hsq hXAdj,
    sub_finiteInvolutiveObservableTwirl_eq_half_commutator_mul U X hsq,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, norm_smul]
  have hhalfNorm : ‖((2 : k)⁻¹)‖ = (2 : ℝ)⁻¹ := by
    norm_num
  rw [hhalfNorm]
  ring

/-- A state has zero clock-observability energy exactly when the clock commutator annihilates
the clock-shifted state.  This is the statewise faithful-detection form of the operator
commutant criterion. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_shifted
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) (psi : E) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) = 0 ↔
      ((X * U - U * X) : E →L[k] E) (U psi) = 0 := by
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_shifted
    U X hadjoint_mul hsq hXAdj]
  constructor
  · intro hzero
    have hnormSq : ‖((X * U - U * X) : E →L[k] E) (U psi)‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)
  · intro hzero
    rw [hzero]
    simp

/-- **Stationary clock commutator law.**  On a clock-invariant state, the complete observable
twirl defect is one quarter of the squared clock--observable commutator.  The global state is
stationary; the nonzero value measures only whether the clock can distinguish the observable. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) {psi : E}
    (hpsi : U psi = psi) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) =
      (4 : ℝ)⁻¹ * ‖((X * U - U * X) : E →L[k] E) psi‖ ^ 2 := by
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_shifted
    U X hadjoint_mul hsq hXAdj, hpsi]

/-- On a stationary state, vanishing clock-observability energy is exactly annihilation by the
unshifted clock commutator. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_of_fixed
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) {psi : E}
    (hpsi : U psi = psi) :
    RCLike.re
        (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) = 0 ↔
      ((X * U - U * X) : E →L[k] E) psi = 0 := by
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_shifted
    U X hadjoint_mul hsq hXAdj, hpsi]

/-- Positivity of the clock-observability defect needs no separately supplied positive-operator
hypothesis: involutive unitarity and self-adjointness of the observed quantity discharge it. -/
theorem re_inner_finiteInvolutiveObservableTwirlKadisonDefect_nonneg
    (U X : E →L[k] E) (hadjoint_mul : U.adjoint * U = 1)
    (hsq : U ^ 2 = 1) (hXAdj : X.adjoint = X) (psi : E) :
    0 ≤ RCLike.re
      (inner k psi (finiteInvolutiveObservableTwirlKadisonDefect U X psi)) := by
  rw [re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_transitionNormSq_add
    U X hadjoint_mul hsq hXAdj psi]
  positivity

end

end HTGeometry
