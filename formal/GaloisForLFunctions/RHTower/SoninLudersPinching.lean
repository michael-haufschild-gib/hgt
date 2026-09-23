import GaloisForLFunctions.RHTower.CCMSoninResolventCommutator
import GaloisForLFunctions.RHTower.SoninEssentialNormExtensions
import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# Lüders pinching removes cutoff-commutation hypotheses

For an idempotent cutoff `e`, the nonselective two-outcome measurement channel

`D_e(X) = eXe + (1-e)X(1-e)`

deletes both off-diagonal cutoff corners.  Consequently `D_e(X)` commutes with `e` for every
input `X`.  The exact identity

`X + (1-2e)X(1-2e) = 2 D_e(X)`

also identifies this Lüders channel with the finite `Z₂` parity twirl whenever division by two is
available.

The final theorem substitutes the pinched observable into the existing resolvent-dressed Sonin
commutator formula.  It removes that theorem's assumed commutation with the physical cutoff; the
only surviving anomaly channel is again the Fourier-edge commutator.
-/

namespace RHTower

noncomputable section

variable {R : Type*} [Ring R]

/-- The nonselective two-outcome Lüders pinching associated with an idempotent cutoff. -/
def ludersPinching (e X : R) : R :=
  e * X * e + (1 - e) * X * (1 - e)

/-- The established RHTower Lueders channel is the general HTGeometry two-outcome pinching. -/
theorem ludersPinching_eq_twoOutcomePinching (e X : R) :
    ludersPinching e X = HTGeometry.twoOutcomePinching e X := by
  rfl

/-- The parity involution associated with a two-sector cutoff. -/
def cutoffParity (e : R) : R :=
  1 - 2 * e

/-- The Lüders channel is exactly the normalized `Z₂` parity twirl, stated without division:
the parity-orbit sum is twice the pinching.  This polynomial identity does not itself require
idempotence. -/
theorem parityTwirlNumerator_eq_two_mul_ludersPinching (e X : R) :
    X + cutoffParity e * X * cutoffParity e = 2 * ludersPinching e X := by
  simp only [cutoffParity, ludersPinching]
  noncomm_ring

/-- The disturbance deleted by a nonselective Lüders measurement is exactly the sum of the two
off-diagonal cutoff corners already used by the RHTower boundary calculus.  This block identity
does not require idempotence. -/
theorem sub_ludersPinching_eq_crossBoundary_add_upperBoundary (e X : R) :
    X - ludersPinching e X = crossBoundary e X + upperBoundary e X := by
  simp only [ludersPinching, crossBoundary, upperBoundary]
  noncomm_ring

/-- Every observable splits exactly into its cutoff-commuting Lüders block and the two native
RHTower boundary channels. -/
theorem ludersPinching_add_boundaries_eq (e X : R) :
    ludersPinching e X + (crossBoundary e X + upperBoundary e X) = X := by
  rw [← sub_ludersPinching_eq_crossBoundary_add_upperBoundary e X]
  abel

/-- The lower measurement-disturbance corner is the right cutoff block of the cutoff
commutator. -/
theorem crossBoundary_eq_ccmCommutator_mul_cutoff
    {e : R} (he : IsIdempotentElem e) (X : R) :
    crossBoundary e X = ccmCommutator X e * e := by
  have hee : e * e = e := he
  simp only [crossBoundary, ccmCommutator, sub_mul]
  rw [show X * e * e = X * e by rw [mul_assoc, hee]]
  noncomm_ring

/-- The upper measurement-disturbance corner is the negative left cutoff block of the cutoff
commutator. -/
theorem upperBoundary_eq_neg_cutoff_mul_ccmCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    upperBoundary e X = -(e * ccmCommutator X e) := by
  have hee : e * e = e := he
  simp only [upperBoundary, ccmCommutator, mul_sub]
  rw [show e * (e * X) = e * X by rw [← mul_assoc, hee]]
  noncomm_ring

/-- **Pure-dephasing double-commutator law.**  For an idempotent measurement cutoff, the part
deleted by the nonselective Lüders channel is exactly the double commutator with that cutoff. -/
theorem sub_ludersPinching_eq_doubleCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    X - ludersPinching e X = ccmCommutator e (ccmCommutator e X) := by
  have hee : e * e = e := he
  simp only [ludersPinching, ccmCommutator, mul_sub, sub_mul]
  rw [show e * (e * X) = e * X by rw [← mul_assoc, hee],
    show X * e * e = X * e by rw [mul_assoc, hee]]
  noncomm_ring

/-- The same dephasing disturbance is the reverse-oriented double commutator.  This form makes
compactness propagate directly from essential commutation with the cutoff. -/
theorem sub_ludersPinching_eq_reverseDoubleCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    X - ludersPinching e X = ccmCommutator (ccmCommutator X e) e := by
  rw [sub_ludersPinching_eq_crossBoundary_add_upperBoundary,
    crossBoundary_eq_ccmCommutator_mul_cutoff he,
    upperBoundary_eq_neg_cutoff_mul_ccmCommutator he]
  simp only [ccmCommutator]
  abel

/-- The cutoff commutator is the signed difference of the two off-diagonal measurement
corners.  Together with `sub_ludersPinching_eq_crossBoundary_add_upperBoundary`, this is the
sum/difference polarization behind the exact disturbance-energy law below. -/
theorem ccmCommutator_eq_crossBoundary_sub_upperBoundary (e X : R) :
    ccmCommutator X e = crossBoundary e X - upperBoundary e X := by
  simp only [ccmCommutator, crossBoundary, upperBoundary]
  noncomm_ring

/-- **Lueders/commutator square law.**  For every idempotent cutoff, the square of the
off-diagonal part deleted by the nonselective measurement is the negative square of the cutoff
commutator.  No adjoint or positivity premise is needed for this algebraic core. -/
theorem ludersDisturbance_sq_eq_neg_ccmCommutator_sq
    {e : R} (he : IsIdempotentElem e) (X : R) :
    (X - ludersPinching e X) * (X - ludersPinching e X) =
      -(ccmCommutator X e * ccmCommutator X e) := by
  simp only [sub_ludersPinching_eq_crossBoundary_add_upperBoundary,
    ccmCommutator_eq_crossBoundary_sub_upperBoundary]
  noncomm_ring [crossBoundary_mul_crossBoundary e X X he,
    upperBoundary_mul_upperBoundary e X X he]

/-- **Lueders--Kadison transition law.**  The failure of projective pinching to preserve the
square of an observable is exactly the sum of the two oriented cutoff transition products.  This
connects the RHTower boundary calculus directly to the general HTGeometry Kadison-defect API. -/
theorem ludersPinchingKadisonDefect_eq_boundaryProducts
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e (X * X) - ludersPinching e X * ludersPinching e X =
      upperBoundary e X * crossBoundary e X +
        crossBoundary e X * upperBoundary e X := by
  simpa only [ludersPinching_eq_twoOutcomePinching, crossBoundary, upperBoundary,
    HTGeometry.twoOutcomeLowerTransition, HTGeometry.twoOutcomeUpperTransition,
    HTGeometry.twoOutcomePinchingKadisonDefect] using
      (HTGeometry.twoOutcomePinchingKadisonDefect_eq_transitionProducts he X)

/-- For self-adjoint input and cutoff, the exact positive square of Lueders disturbance equals
the exact positive square of the cutoff commutator.  This is the operator-level form of the
quantum-measurement disturbance identity, stronger than equality of Hilbert--Schmidt traces. -/
theorem star_mul_self_ludersDisturbance_eq_cutoffCommutator
    [StarRing R] {e X : R} (he : IsIdempotentElem e)
    (heStar : star e = e) (hXStar : star X = X) :
    star (X - ludersPinching e X) * (X - ludersPinching e X) =
      star (ccmCommutator X e) * ccmCommutator X e := by
  have hdistStar : star (X - ludersPinching e X) = X - ludersPinching e X := by
    simp only [ludersPinching, star_sub, star_add, star_mul, star_one,
      heStar, hXStar, mul_assoc]
  have hcommStar : star (ccmCommutator X e) = -ccmCommutator X e := by
    simp only [ccmCommutator, star_sub, star_mul, heStar, hXStar]
    abel
  rw [hdistStar, hcommStar, neg_mul,
    ludersDisturbance_sq_eq_neg_ccmCommutator_sq he X]

/-- **Two-projection transition impurity.**  For self-adjoint idempotents `e,X`, the positive
square of the transition corner `(1-e)Xe` is exactly the failure of the compressed projection
`eXe` to remain idempotent.  This is the algebraic core of the prolate plunge-spectrum value. -/
theorem star_mul_self_crossBoundary_eq_compression_sub_sq
    [StarRing R] {e X : R} (he : IsIdempotentElem e) (hX : IsIdempotentElem X)
    (heStar : star e = e) (hXStar : star X = X) :
    star (crossBoundary e X) * crossBoundary e X =
      compression e X - compression e X * compression e X := by
  have hee : e * e = e := he
  have hXX : X * X = X := hX
  have hff : (1 - e) * (1 - e) = 1 - e := by
    noncomm_ring [hee]
  have hstar : star (crossBoundary e X) = e * X * (1 - e) := by
    simp only [crossBoundary, star_mul, star_sub, star_one, heStar, hXStar,
      mul_assoc]
  have hlowerProduct :
      (e * X * (1 - e)) * ((1 - e) * X * e) =
        e * X * (1 - e) * X * e := by
    calc
      (e * X * (1 - e)) * ((1 - e) * X * e) =
          e * X * ((1 - e) * (1 - e)) * X * e := by noncomm_ring
      _ = e * X * (1 - e) * X * e := by rw [hff]
  have hcompressionProduct :
      (e * X * e) * (e * X * e) = e * X * e * X * e := by
    calc
      (e * X * e) * (e * X * e) = e * X * (e * e) * X * e := by
        noncomm_ring
      _ = e * X * e * X * e := by rw [hee]
  rw [hstar]
  simp only [crossBoundary, compression]
  rw [hlowerProduct, hcompressionProduct]
  have hXXcompression : e * X * e = e * X * X * e := by
    calc
      e * X * e = e * (X * X) * e := by rw [hXX]
      _ = e * X * X * e := by noncomm_ring
  calc
    e * X * (1 - e) * X * e =
        e * X * X * e - e * X * e * X * e := by noncomm_ring
    _ = e * X * e - e * X * e * X * e := by rw [← hXXcompression]

/-- An idempotent cutoff acts on the left of its pinching by selecting the cutoff block. -/
theorem mul_ludersPinching_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    e * ludersPinching e X = e * X * e := by
  have hee : e * e = e := he
  have hec : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hee, sub_self]
  simp only [ludersPinching, mul_add, ← mul_assoc, hee, hec, zero_mul, add_zero]

/-- An idempotent cutoff acts on the right of its pinching by selecting the same cutoff block. -/
theorem ludersPinching_mul_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e X * e = e * X * e := by
  have hee : e * e = e := he
  have hce : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, hee, sub_self]
  simp only [ludersPinching, add_mul, mul_assoc, hee, hce, mul_zero, add_zero]

/-- A nonselective Lüders pinching commutes with the measured cutoff, with no premise on the
unpinched observable. -/
theorem ccmCommutator_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ccmCommutator (ludersPinching e X) e = 0 := by
  rw [ccmCommutator, ludersPinching_mul_eq_cutoffBlock he,
    mul_ludersPinching_eq_cutoffBlock he, sub_self]

/-- The cutoff commutator of an observable is exactly the cutoff commutator of the part deleted
by the Lüders channel.  Thus all failure of cutoff commutation lives in measurement disturbance,
not in the block-diagonal measured observable. -/
theorem ccmCommutator_eq_ludersDisturbance_commutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ccmCommutator X e = ccmCommutator (X - ludersPinching e X) e := by
  have hzero := ccmCommutator_ludersPinching_eq_zero he X
  rw [ccmCommutator] at hzero
  have hpinched : ludersPinching e X * e = e * ludersPinching e X :=
    sub_eq_zero.mp hzero
  simp only [ccmCommutator, sub_mul, mul_sub]
  rw [hpinched]
  abel

/-- The Lüders pinching deletes the lower cutoff-boundary corner of every observable. -/
theorem crossBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    crossBoundary e (ludersPinching e X) = 0 := by
  apply crossBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

/-- The Lüders pinching also deletes the upper cutoff-boundary corner. -/
theorem upperBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    upperBoundary e (ludersPinching e X) = 0 := by
  apply upperBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

/-- **Algebraic Lüders fixed-point classification.**  An observable is unchanged by an
idempotent cutoff's nonselective pinching exactly when it commutes with that cutoff.  Thus the
pinching fixed-point premise is not independent data. -/
theorem ludersPinching_eq_self_iff_commute
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e X = X ↔ X * e = e * X := by
  simpa only [ludersPinching, HTGeometry.twoOutcomePinching] using
    (HTGeometry.twoOutcomePinching_eq_self_iff_commute he X)

/-- Repeating the same Lüders measurement is exactly stable after its first application. -/
theorem ludersPinching_apply_twice
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e (ludersPinching e X) = ludersPinching e X := by
  simpa only [ludersPinching, HTGeometry.twoOutcomePinching] using
    (HTGeometry.twoOutcomePinching_apply_twice he X)

/-- The image of an idempotent cutoff's Lüders channel is exactly its cutoff commutant. -/
theorem range_ludersPinching_eq_commutant
    {e : R} (he : IsIdempotentElem e) :
    Set.range (ludersPinching e) = {X : R | X * e = e * X} := by
  simpa only [ludersPinching, HTGeometry.twoOutcomePinching] using!
    (HTGeometry.range_twoOutcomePinching_eq_commutant he)

/-- **One-corner Lüders fixed-point classification.**  For self-adjoint cutoff and source, the
upper boundary corner is the adjoint of the lower one.  Hence a single native RHTower boundary
condition is equivalent to exact invariance under nonselective measurement. -/
theorem ludersPinching_eq_self_iff_crossBoundary_eq_zero_of_star_eq
    [StarRing R] {e X : R} (he : IsIdempotentElem e)
    (heStar : star e = e) (hXStar : star X = X) :
    ludersPinching e X = X ↔ crossBoundary e X = 0 := by
  simpa only [ludersPinching, HTGeometry.twoOutcomePinching, crossBoundary,
    HTGeometry.twoOutcomeLowerTransition] using
      (HTGeometry.twoOutcomePinching_eq_self_iff_lowerTransition_eq_zero_of_star_eq
        he heStar hXStar)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A commutator is compact when its left entry is compact. -/
theorem isCompactOperator_ccmCommutator_of_leftCompact
    (K Y : H →L[ℂ] H) (hK : IsCompactOperator K) :
    IsCompactOperator (ccmCommutator K Y : H →L[ℂ] H) := by
  rw [ccmCommutator]
  exact (hK.comp_clm Y).sub (hK.clm_comp Y)

/-- **Compact disturbance/essential commutation equivalence.**  For an idempotent measurement
cutoff, compactness of the Lüders disturbance is equivalent to commutation with the cutoff modulo
compact operators.  This replaces an operator-algebra premise by the directly measurable
dephasing residual `X - D_e(X)`. -/
theorem isCompactOperator_ludersDisturbance_iff_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e) :
    IsCompactOperator (X - ludersPinching e X : H →L[ℂ] H) ↔
      IsCompactOperator (ccmCommutator X e : H →L[ℂ] H) := by
  constructor
  · intro hdist
    rw [ccmCommutator_eq_ludersDisturbance_commutator he]
    exact isCompactOperator_ccmCommutator_of_leftCompact _ _ hdist
  · intro hcomm
    rw [sub_ludersPinching_eq_reverseDoubleCommutator he]
    exact isCompactOperator_ccmCommutator_of_leftCompact _ _ hcomm

/-- Essential commutation with a projection makes its lower Lüders disturbance corner compact. -/
theorem isCompactOperator_crossBoundary_of_compact_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (hcomm : IsCompactOperator (ccmCommutator X e : H →L[ℂ] H)) :
    IsCompactOperator (crossBoundary e X : H →L[ℂ] H) := by
  simpa only [crossBoundary_eq_ccmCommutator_mul_cutoff he] using! hcomm.comp_clm e

/-- Essential commutation with a projection also makes its upper Lüders disturbance corner
compact. -/
theorem isCompactOperator_upperBoundary_of_compact_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (hcomm : IsCompactOperator (ccmCommutator X e : H →L[ℂ] H)) :
    IsCompactOperator (upperBoundary e X : H →L[ℂ] H) := by
  simpa only [upperBoundary_eq_neg_cutoff_mul_ccmCommutator he] using!
    (hcomm.clm_comp e).neg

variable [CompleteSpace H]

/-- For self-adjoint inputs, the Lueders--Kadison defect is the sum of the positive master
constraints of the lower and upper cutoff transitions. -/
theorem ludersPinchingKadisonDefect_eq_boundaryMasterConstraints
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) :
    ludersPinching e (X * X) - ludersPinching e X * ludersPinching e X =
      HTGeometry.quantumMasterConstraint (crossBoundary e X) +
        HTGeometry.quantumMasterConstraint (upperBoundary e X) := by
  simpa only [ludersPinching_eq_twoOutcomePinching, crossBoundary, upperBoundary,
    HTGeometry.twoOutcomeLowerTransition, HTGeometry.twoOutcomeUpperTransition,
    HTGeometry.twoOutcomePinchingKadisonDefect] using
      (HTGeometry.twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_sum
        e X he heAdj hXAdj)

/-- The symmetric physical dilation signal is self-adjoint. -/
theorem adjoint_dilationSum_eq_self (p : ℝ) (hp : 1 < p) :
    ContinuousLinearMap.adjoint (dilationSum p hp) = dilationSum p hp := by
  simpa only [dilationSum, ContinuousLinearMap.star_eq_adjoint] using
    (IsSelfAdjoint.add_star_self
      (dilationCLM p (zero_lt_one.trans hp))).star_eq

/-- **Concrete Sonin Kadison-defect consumer.**  Pinching the actual symmetric dilation signal by
the central Sonin projection has a multiplicativity defect equal to the two positive transition
master constraints.  This supplies a source-native positive observable for every retained scale;
it does not assert nonvanishing of the principal-subtracted residual. -/
theorem centralSoninDilation_ludersPinchingKadisonDefect_eq_boundaryMasterConstraints
    (a p : ℝ) (hp : 1 < p) :
    let Q := centralSoninProjection a
    let D := dilationSum p hp
    ludersPinching Q (D * D) - ludersPinching Q D * ludersPinching Q D =
      HTGeometry.quantumMasterConstraint (crossBoundary Q D) +
        HTGeometry.quantumMasterConstraint (upperBoundary Q D) := by
  dsimp
  exact ludersPinchingKadisonDefect_eq_boundaryMasterConstraints
    (centralSoninProjection a) (dilationSum p hp)
    (centralSoninCarrier a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
    (adjoint_dilationSum_eq_self p hp)

/-- State-value form of the concrete Sonin Kadison defect.  Every vector sees exactly the sum of
the two squared physical transition amplitudes of the symmetric dilation signal. -/
theorem re_inner_centralSoninDilation_ludersPinchingKadisonDefect_eq_transitionNormSq_add
    (a p : ℝ) (hp : 1 < p) (psi : SoninL2) :
    let Q := centralSoninProjection a
    let D := dilationSum p hp
    Complex.re (inner ℂ psi
      ((ludersPinching Q (D * D) - ludersPinching Q D * ludersPinching Q D) psi)) =
        ‖crossBoundary Q D psi‖ ^ (2 : ℕ) + ‖upperBoundary Q D psi‖ ^ (2 : ℕ) := by
  dsimp
  simpa only [ludersPinching_eq_twoOutcomePinching, crossBoundary, upperBoundary,
    HTGeometry.twoOutcomeLowerTransition, HTGeometry.twoOutcomeUpperTransition,
    HTGeometry.twoOutcomePinchingKadisonDefect] using!
      (HTGeometry.re_inner_twoOutcomePinchingKadisonDefect_eq_transitionNormSq_add
        (centralSoninProjection a) (dilationSum p hp)
        (centralSoninCarrier a).isIdempotentElem_starProjection
        (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
        (adjoint_dilationSum_eq_self p hp) psi)

/-- **Exact measurement-disturbance master constraint.**  For a self-adjoint observable and
self-adjoint idempotent cutoff, the Lueders disturbance and cutoff commutator determine literally
the same positive master operator.  Hence either residual can replace the other in the existing
master-constraint, Ward-value, trace, and singular-value APIs without a comparison constant. -/
theorem quantumMasterConstraint_ludersDisturbance_eq_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) :
    HTGeometry.quantumMasterConstraint (X - ludersPinching e X) =
      HTGeometry.quantumMasterConstraint (ccmCommutator X e) := by
  have heStar : star e = e := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using heAdj
  have hXStar : star X = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hXAdj
  simpa only [HTGeometry.quantumMasterConstraint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint] using
    (star_mul_self_ludersDisturbance_eq_cutoffCommutator he heStar hXStar)

/-- The continuous-operator master constraint of a transition corner is exactly the quadratic
idempotence defect of the corresponding two-projection compression. -/
theorem quantumMasterConstraint_crossBoundary_eq_compression_sub_sq
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e) (hX : IsIdempotentElem X)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) :
    HTGeometry.quantumMasterConstraint (crossBoundary e X) =
      compression e X - compression e X * compression e X := by
  have heStar : star e = e := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using heAdj
  have hXStar : star X = X := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hXAdj
  simpa only [HTGeometry.quantumMasterConstraint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.star_eq_adjoint] using
    (star_mul_self_crossBoundary_eq_compression_sub_sq
      he hX heStar hXStar)

/-- The directly observable value form of the master-constraint identity: every state has the
same squared Lueders disturbance as squared cutoff-commutator residual. -/
theorem norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) (ψ : H) :
    ‖(X - ludersPinching e X) ψ‖ ^ (2 : ℕ) = ‖ccmCommutator X e ψ‖ ^ (2 : ℕ) := by
  calc
    ‖(X - ludersPinching e X) ψ‖ ^ (2 : ℕ) =
        Complex.re (inner ℂ ψ
          (HTGeometry.quantumMasterConstraint (X - ludersPinching e X) ψ)) :=
      (HTGeometry.re_inner_quantumMasterConstraint_eq_normSq
        (X - ludersPinching e X) ψ).symm
    _ = Complex.re (inner ℂ ψ
          (HTGeometry.quantumMasterConstraint (ccmCommutator X e) ψ)) := by
      rw [quantumMasterConstraint_ludersDisturbance_eq_cutoffCommutator
        e X he heAdj hXAdj]
    _ = ‖ccmCommutator X e ψ‖ ^ (2 : ℕ) :=
      HTGeometry.re_inner_quantumMasterConstraint_eq_normSq
        (ccmCommutator X e) ψ

/-- Lüders disturbance is Hilbert--Schmidt exactly when the corresponding cutoff commutator is.
This converts a measurement-decoherence finiteness premise into the commutator premise already
used throughout the Sonin operator ideal. -/
theorem isHilbertSchmidt_ludersDisturbance_iff_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) :
    ContinuousLinearMap.IsHilbertSchmidt (X - ludersPinching e X) ↔
      ContinuousLinearMap.IsHilbertSchmidt (ccmCommutator X e) := by
  unfold ContinuousLinearMap.IsHilbertSchmidt
  constructor
  · intro hdist
    refine hdist.congr fun i => ?_
    exact norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq
      e X he heAdj hXAdj (ContinuousLinearMap.hsBasis ℂ H i)
  · intro hcomm
    refine hcomm.congr fun i => ?_
    exact (norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq
      e X he heAdj hXAdj (ContinuousLinearMap.hsBasis ℂ H i)).symm

/-- **Total Lüders-disturbance energy.**  The statewise master-constraint identity sums over the
canonical Hilbert basis to identify the complete Hilbert--Schmidt energy deleted by a
nonselective projective measurement with the cutoff-commutator energy.  No separate
Hilbert--Schmidt premise is required: the summands agree pointwise, so either side is finite
exactly when the other is. -/
theorem hsNormSq_ludersDisturbance_eq_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (heAdj : ContinuousLinearMap.adjoint e = e)
    (hXAdj : ContinuousLinearMap.adjoint X = X) :
    ContinuousLinearMap.hsNormSq (X - ludersPinching e X) =
      ContinuousLinearMap.hsNormSq (ccmCommutator X e) := by
  unfold ContinuousLinearMap.hsNormSq
  exact tsum_congr fun i =>
    norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq
      e X he heAdj hXAdj (ContinuousLinearMap.hsBasis ℂ H i)

/-- **Two-projection transition-energy law.**  Measuring one orthogonal projection with another
produces exactly the master energy of their commutator.  Applied to the physical and Fourier
cutoffs, this is the time-frequency/prolate transition-spectrum identity in the native Sonin
projection language. -/
theorem quantumMasterConstraint_starProjection_ludersDisturbance_eq_cutoffCommutator
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    HTGeometry.quantumMasterConstraint
        (B.starProjection - ludersPinching A.starProjection B.starProjection) =
      HTGeometry.quantumMasterConstraint
        (ccmCommutator B.starProjection A.starProjection) := by
  exact quantumMasterConstraint_ludersDisturbance_eq_cutoffCommutator
    A.starProjection B.starProjection A.isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection A).star_eq
    (isSelfAdjoint_starProjection B).star_eq

/-- **Sonin prolate transition-energy identity.**  The non-idempotence of the alternating
time-frequency block `P_B P_A P_B` is exactly the master constraint of the transition corner
from the `B` sector through `A`. -/
theorem soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    soninAlternatingBlock A B -
        soninAlternatingBlock A B * soninAlternatingBlock A B =
      HTGeometry.quantumMasterConstraint
        (crossBoundary B.starProjection A.starProjection) := by
  simpa only [soninAlternatingBlock, compression] using
    (quantumMasterConstraint_crossBoundary_eq_compression_sub_sq
      B.starProjection A.starProjection
      B.isIdempotentElem_starProjection A.isIdempotentElem_starProjection
      (isSelfAdjoint_starProjection B).star_eq
      (isSelfAdjoint_starProjection A).star_eq).symm

/-- Statewise prolate value law: the expectation of `T-T^(2 : ℕ)` is the squared norm of the
time-frequency transition corner. -/
theorem re_inner_soninAlternatingBlock_sub_sq_eq_norm_transition
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (ψ : H) :
    Complex.re (inner ℂ ψ
      ((soninAlternatingBlock A B -
        soninAlternatingBlock A B * soninAlternatingBlock A B) ψ)) =
      ‖crossBoundary B.starProjection A.starProjection ψ‖ ^ (2 : ℕ) := by
  rw [soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition]
  exact HTGeometry.re_inner_quantumMasterConstraint_eq_normSq
    (crossBoundary B.starProjection A.starProjection) ψ

/-- Vanishing of the prolate impurity constraint is exactly vanishing of the physical/Fourier
transition corner.  The master-constraint kernel theorem discharges this equivalence with no
spectral or positivity hypothesis. -/
theorem physicalState_soninAlternatingBlock_sub_sq_iff_transition
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (ψ : H) :
    GaloisForLFunctions.PhysicalState
        (soninAlternatingBlock A B -
          soninAlternatingBlock A B * soninAlternatingBlock A B).toLinearMap ψ ↔
      GaloisForLFunctions.PhysicalState
        (crossBoundary B.starProjection A.starProjection).toLinearMap ψ := by
  rw [soninAlternatingBlock_sub_sq_eq_quantumMasterConstraint_transition]
  exact HTGeometry.physicalState_quantumMasterConstraint_iff
    (crossBoundary B.starProjection A.starProjection) ψ

/-- **Pinched Sonin commutator law.**  Replacing an arbitrary observable by its nonselective
Lüders pinching at the physical cutoff removes the commutation premise from the exact
resolvent-dressed Sonin formula. -/
theorem ccmCommutator_ludersPinching_soninIntersectionProjection
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X₀ (soninIntersectionProjection A B) =
      -E * V *
        (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
            B.starProjection +
          B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
            B.starProjection +
          ccmCommutator X₀ B.starProjection) * E := by
  dsimp
  exact ccmCommutator_soninIntersectionProjection A B hT _
    (ccmCommutator_ludersPinching_eq_zero
      A.isIdempotentElem_starProjection X)

/-- **Hypothesis-free Sonin boundary split for the original observable.**  An arbitrary `X`
decomposes into its Lüders block, whose exact Sonin commutator is controlled solely by the
Fourier-edge commutator, and its two physical-cutoff boundary corners.  Thus the former assumed
commutation with the physical cutoff is replaced by an explicit residual in the boundary
language already consumed throughout RHTower. -/
theorem ccmCommutator_soninIntersectionProjection_ludersBoundarySplit
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H) :
    let X₀ := ludersPinching A.starProjection X
    let Xoff := crossBoundary A.starProjection X + upperBoundary A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X (soninIntersectionProjection A B) =
      -E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E +
        ccmCommutator Xoff (soninIntersectionProjection A B) := by
  dsimp
  have hsplit : X = ludersPinching A.starProjection X +
      (crossBoundary A.starProjection X + upperBoundary A.starProjection X) := by
    exact (ludersPinching_add_boundaries_eq A.starProjection X).symm
  nth_rw 1 [hsplit]
  have hadd : ∀ Y Z P : H →L[ℂ] H,
      ccmCommutator (Y + Z) P = ccmCommutator Y P + ccmCommutator Z P := by
    intro Y Z P
    simp only [ccmCommutator, add_mul, mul_add]
    abel
  nth_rw 1 [hadd]
  rw [ccmCommutator_ludersPinching_soninIntersectionProjection A B hT X]

omit [CompleteSpace H] in
/-- Compact physical-cutoff corners make the complete Lüders disturbance term compact after
commutation with the exact Sonin projection. -/
theorem isCompactOperator_soninLudersBoundaryResidual
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (X : H →L[ℂ] H)
    (hlower : IsCompactOperator
      (crossBoundary A.starProjection X : H →L[ℂ] H))
    (hupper : IsCompactOperator
      (upperBoundary A.starProjection X : H →L[ℂ] H)) :
    IsCompactOperator
      (ccmCommutator
        (crossBoundary A.starProjection X + upperBoundary A.starProjection X)
        (soninIntersectionProjection A B) : H →L[ℂ] H) := by
  exact isCompactOperator_ccmCommutator_of_leftCompact _ _ (hlower.add hupper)

/-- **Calkin-level Sonin formula without cutoff commutation.**  If the two physical-cutoff
corners of an arbitrary observable are compact, then its exact Sonin commutator differs by a
compact operator from the Fourier-edge dressed formula of its Lüders block.  This is the direct
consumer of the boundary split in the existing compact-operator layer. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hlower : IsCompactOperator
      (crossBoundary A.starProjection X : H →L[ℂ] H))
    (hupper : IsCompactOperator
      (upperBoundary A.starProjection X : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  dsimp
  let D : H →L[ℂ] H :=
    -A.orthogonal.starProjection * soninProjectionResolvent A B hT *
      (ccmCommutator (ludersPinching A.starProjection X) B.starProjection *
            A.starProjection * B.starProjection * soninProjectionResolvent A B hT *
            B.starProjection +
        B.starProjection * A.starProjection *
            ccmCommutator (ludersPinching A.starProjection X) B.starProjection *
            soninProjectionResolvent A B hT * B.starProjection +
        ccmCommutator (ludersPinching A.starProjection X) B.starProjection) *
      A.orthogonal.starProjection
  let L : H →L[ℂ] H :=
    ccmCommutator X (soninIntersectionProjection A B) - D
  let K : H →L[ℂ] H :=
    ccmCommutator
      (crossBoundary A.starProjection X + upperBoundary A.starProjection X)
      (soninIntersectionProjection A B)
  change IsCompactOperator (fun x : H => L x)
  have hresidual := isCompactOperator_soninLudersBoundaryResidual
    A B X hlower hupper
  change IsCompactOperator (fun x : H => K x) at hresidual
  have hsplit :=
    ccmCommutator_soninIntersectionProjection_ludersBoundarySplit A B hT X
  dsimp at hsplit
  have hdiff : L = K := by
    dsimp only [L, K, D]
    rw [hsplit]
    abel
  have hfun : (fun x : H => L x) = fun x : H => K x := by
    funext x
    rw [hdiff]
  rw [hfun]
  exact hresidual

/-- **Essential-commutation Sonin/Calkin law.**  The two separate compact-corner premises collapse
to the single physics-native assumption that `X` commutes with the physical cutoff modulo compact
operators.  Under that premise, the arbitrary-observable Sonin commutator still equals the
Lüders-block Fourier-edge dressed formula in the Calkin algebra. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hcomm : IsCompactOperator
      (ccmCommutator X A.starProjection : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  apply isCompactOperator_soninCommutator_sub_ludersDressed A B hT X
  · exact isCompactOperator_crossBoundary_of_compact_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection hcomm
  · exact isCompactOperator_upperBoundary_of_compact_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection hcomm

/-- **Measurement-disturbance Sonin/Calkin law.**  Compactness of the observable part erased by
the physical-cutoff Lüders measurement is sufficient for the exact Calkin-level Sonin formula.
This is the dephasing-native form of essential cutoff commutation. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed_of_compactDisturbance
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hdist : IsCompactOperator
      (X - ludersPinching A.starProjection X : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    A B hT X
    ((isCompactOperator_ludersDisturbance_iff_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection).mp hdist)

/-- **Concrete central-cutoff Sonin/Calkin law.**  For a positive central time-frequency cutoff,
compactness of the physical-cutoff commutator is the only remaining operator hypothesis.  The
strict-contraction premise is discharged by the concrete time-band geometry, while Lüders
pinching discharges both separate compact-corner premises. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hcomm : IsCompactOperator
      (ccmCommutator X (centralPhysicalForbidden a).starProjection :
        SoninL2 →L[ℂ] SoninL2)) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  dsimp only
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (norm_centralSoninAlternatingBlock_lt_one a ha) X hcomm

/-- **Hilbert--Schmidt central Sonin/Calkin law.**  A Hilbert--Schmidt observable automatically
commutes modulo compact operators with every bounded cutoff.  Thus the central Lüders formula
requires no separate cutoff-commutator premise on this operator class. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hX : ContinuousLinearMap.IsHilbertSchmidt X) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  apply isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator a ha X
  exact isCompactOperator_ccmCommutator_of_leftCompact
    X (centralPhysicalForbidden a).starProjection hX.isCompactOperator

/-- **Concrete central measurement-disturbance law.**  For a positive central time-frequency
cutoff, compactness of the part erased by the physical Lüders measurement is the sole operator
premise needed for the Calkin-level Sonin formula. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_compactDisturbance
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hdist : IsCompactOperator
      (X - ludersPinching (centralPhysicalForbidden a).starProjection X :
        SoninL2 →L[ℂ] SoninL2)) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  dsimp only
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_compactDisturbance
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (norm_centralSoninAlternatingBlock_lt_one a ha) X hdist

/-- The archimedean one-prime Euler observable inherits the exact measurement-disturbance master
constraint with no prime-size or aperture premise.  This directly places its physical-boundary
dephasing residual on the existing positive master-constraint theorem surface. -/
theorem quantumMasterConstraint_archimedeanPrimeEuler_ludersDisturbance_eq_commutator
    (a p : ℝ) :
    HTGeometry.quantumMasterConstraint
        (archimedeanPrimeEulerGram p -
          ludersPinching (archimedeanBoundaryCarrierProjection a)
            (archimedeanPrimeEulerGram p)) =
      HTGeometry.quantumMasterConstraint
        (ccmCommutator (archimedeanPrimeEulerGram p)
          (archimedeanBoundaryCarrierProjection a)) := by
  exact quantumMasterConstraint_ludersDisturbance_eq_cutoffCommutator
    (archimedeanBoundaryCarrierProjection a) (archimedeanPrimeEulerGram p)
    (isIdempotentElem_archimedeanBoundaryCarrierProjection a)
    (adjoint_archimedeanBoundaryCarrierProjection a)
    (adjoint_archimedeanPrimeEulerGram p)

/-- Every archimedean test state assigns the same positive value to one-prime boundary
dephasing and to the corresponding projection commutator. -/
theorem norm_archimedeanPrimeEuler_ludersDisturbance_apply_sq_eq_commutator
    (a p : ℝ) (ψ : ArchimedeanWeightedL2) :
    ‖(archimedeanPrimeEulerGram p -
        ludersPinching (archimedeanBoundaryCarrierProjection a)
          (archimedeanPrimeEulerGram p)) ψ‖ ^ (2 : ℕ) =
      ‖ccmCommutator (archimedeanPrimeEulerGram p)
          (archimedeanBoundaryCarrierProjection a) ψ‖ ^ (2 : ℕ) := by
  exact norm_ludersDisturbance_apply_sq_eq_norm_cutoffCommutator_apply_sq
    (archimedeanBoundaryCarrierProjection a) (archimedeanPrimeEulerGram p)
    (isIdempotentElem_archimedeanBoundaryCarrierProjection a)
    (adjoint_archimedeanBoundaryCarrierProjection a)
    (adjoint_archimedeanPrimeEulerGram p) ψ

/-- **One-prime dephasing obstruction.**  The positive archimedean Euler Gram loses a genuinely
noncompact part under the physical boundary measurement.  This is the measurement-disturbance
form of the existing one-prime noncompact-commutator theorem, obtained with no additional
hypothesis. -/
theorem archimedeanPrimeEuler_ludersDisturbance_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (archimedeanPrimeEulerGram p -
        ludersPinching (archimedeanBoundaryCarrierProjection a)
          (archimedeanPrimeEulerGram p) :
        ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) := by
  intro hdist
  apply archimedeanPrimeEuler_projectionCommutator_not_isCompactOperator a p ha hp
  have hcomm : IsCompactOperator
      (ccmCommutator (archimedeanPrimeEulerGram p)
        (archimedeanBoundaryCarrierProjection a) :
        ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) :=
    (isCompactOperator_ludersDisturbance_iff_cutoffCommutator
      (archimedeanBoundaryCarrierProjection a) (archimedeanPrimeEulerGram p)
      (isIdempotentElem_archimedeanBoundaryCarrierProjection a)).mp hdist
  have heq :
      archimedeanBoundaryCarrierProjection a * archimedeanPrimeEulerGram p -
          archimedeanPrimeEulerGram p * archimedeanBoundaryCarrierProjection a =
        -(ccmCommutator (archimedeanPrimeEulerGram p)
          (archimedeanBoundaryCarrierProjection a)) := by
    simp only [ccmCommutator]
    abel
  rw [heq]
  exact hcomm.neg

end

end RHTower
