import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk
import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy

/-!
# The Sonin cutoff pair as a two-reflection quantum walk

The central physical and Fourier forbidden-sector projections generate a canonical unitary
Szegedy walk.  The general two-projection identities make its two observable defects exact
repackagings of existing Sonin quantities:

* its master constraint is four times the physical/Fourier projection-mismatch master constraint;
* its anti-Hermitian part is four times the cutoff commutator whose Hilbert--Schmidt energy is
  already the prolate free-fermion number variance.

This supplies a unitary phase coordinate for the Sonin pair without adding a unitarity hypothesis
or hiding the existing source obstruction in a newly named positivity condition.  The associated
qubitization/Chebyshev law also proves that every symmetric phase power is already determined by
the physical/Fourier projection-mismatch master constraint, while every antisymmetric phase power
factors through the first cutoff commutator.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Product-of-reflections walk for the central physical/Fourier Sonin cutoffs. -/
def centralSoninProjectionQuantumWalk (a : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.twoProjectionQuantumWalk
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection

/-- The concrete Sonin walk is unitary solely from the two orthogonal-projection structures. -/
theorem centralSoninProjectionQuantumWalk_adjoint_mul_self (a : ℝ) :
    adjoint (centralSoninProjectionQuantumWalk a) *
        centralSoninProjectionQuantumWalk a = 1 := by
  exact HTGeometry.twoProjectionQuantumWalk_adjoint_mul_self
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

/-- The reverse multiplication order, needed to consume the concrete walk and its adjoint as a
two-sided inverse pair. -/
theorem centralSoninProjectionQuantumWalk_mul_adjoint (a : ℝ) :
    centralSoninProjectionQuantumWalk a *
        adjoint (centralSoninProjectionQuantumWalk a) = 1 := by
  exact HTGeometry.twoProjectionQuantumWalk_mul_adjoint
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

/-- **Direct prolate consumer.**  The central prolate/alternating block is exactly one half of
the `+1`-shifted quantum walk compressed to the Fourier-forbidden sector.  Existing prolate trace,
impurity, and power-difference theorems can therefore consume the walk coordinate without a new
spectral measure or comparison estimate. -/
theorem centralFourier_compress_centralSoninProjectionQuantumWalk_add_one_eq_two_mul_prolateBlock
    (a : ℝ) :
    (centralFourierForbidden a).starProjection *
        (centralSoninProjectionQuantumWalk a + 1) *
          (centralFourierForbidden a).starProjection =
      2 * soninAlternatingBlock
        (centralPhysicalForbidden a) (centralFourierForbidden a) := by
  simpa only [centralSoninProjectionQuantumWalk, soninAlternatingBlock] using
    HTGeometry.secondProjection_compress_twoProjectionQuantumWalk_add_one_eq_two_mul_compression
      (centralPhysicalForbidden a).starProjection
      (centralFourierForbidden a).starProjection
      (centralFourierForbidden a).isIdempotentElem_starProjection

/-- The Sonin walk defect carries exactly the already-existing projection-mismatch master
constraint, with the sharp factor four and no additional premise. -/
theorem quantumMasterConstraint_centralSoninProjectionQuantumWalk_sub_one_eq
    (a : ℝ) :
    HTGeometry.quantumMasterConstraint (centralSoninProjectionQuantumWalk a - 1) =
      4 * HTGeometry.quantumMasterConstraint
        ((centralPhysicalForbidden a).starProjection -
          (centralFourierForbidden a).starProjection) := by
  exact
    HTGeometry.quantumMasterConstraint_twoProjectionQuantumWalk_sub_one_eq_four_mul_difference
      (centralPhysicalForbidden a).starProjection
      (centralFourierForbidden a).starProjection
      (centralPhysicalForbidden a).isIdempotentElem_starProjection
      (centralFourierForbidden a).isIdempotentElem_starProjection
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

/-- The Hermitian Sonin walk signal is the affine image of the already-existing central
physical/Fourier mismatch master constraint. -/
theorem centralSoninProjectionQuantumWalk_add_adjoint_eq_two_sub_four_mul_difference
    (a : ℝ) :
    centralSoninProjectionQuantumWalk a +
        adjoint (centralSoninProjectionQuantumWalk a) =
      2 - 4 * HTGeometry.quantumMasterConstraint
        ((centralPhysicalForbidden a).starProjection -
          (centralFourierForbidden a).starProjection) := by
  exact HTGeometry.twoProjectionQuantumWalk_add_adjoint_eq_two_sub_four_mul_difference
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

/-- Every symmetric power of the concrete Sonin walk is a recurrence polynomial in the central
projection mismatch.  This is both a phase-coordinate theorem and a route no-go: symmetric walk
moments are not an independent RH input. -/
theorem unitaryCosineRecurrence_centralSoninProjectionQuantumWalk
    (a : ℝ) (n : ℕ) :
    HTGeometry.unitaryCosineRecurrence
        (2 - 4 * HTGeometry.quantumMasterConstraint
          ((centralPhysicalForbidden a).starProjection -
            (centralFourierForbidden a).starProjection)) n =
      centralSoninProjectionQuantumWalk a ^ n +
        adjoint (centralSoninProjectionQuantumWalk a) ^ n := by
  exact HTGeometry.unitaryCosineRecurrence_twoProjectionQuantumWalk
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq
    n

/-- Every antisymmetric power of the concrete Sonin walk factors through the first cutoff
commutator, with a coefficient recurrence determined by the central projection mismatch.  Thus
higher raw phase powers add no operator generator beyond the two existing Sonin channels. -/
theorem centralSoninProjectionQuantumWalk_pow_sub_adjoint_pow_eq_sineRecurrence_mul_commutator
    (a : ℝ) (n : ℕ) :
    centralSoninProjectionQuantumWalk a ^ n -
        adjoint (centralSoninProjectionQuantumWalk a) ^ n =
      HTGeometry.unitarySineRecurrence
          (2 - 4 * HTGeometry.quantumMasterConstraint
            ((centralPhysicalForbidden a).starProjection -
              (centralFourierForbidden a).starProjection)) n *
        (4 * ccmCommutator
          (centralPhysicalForbidden a).starProjection
          (centralFourierForbidden a).starProjection) := by
  simpa only [centralSoninProjectionQuantumWalk, ccmCommutator] using
    HTGeometry.twoProjectionQuantumWalk_pow_sub_adjoint_pow_eq_sineRecurrence_mul_commutator
      (centralPhysicalForbidden a).starProjection
      (centralFourierForbidden a).starProjection
      (centralPhysicalForbidden a).isIdempotentElem_starProjection
      (centralFourierForbidden a).isIdempotentElem_starProjection
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq
      n

/-- The anti-Hermitian walk phase is exactly the physical/Fourier cutoff commutator.  Combined
with `hsNormSq_centralCutoffCommutator_eq_two_mul_re_opTrace_prolateImpurity`, this identifies its
Hilbert--Schmidt phase energy with the existing free-fermion/prolate impurity channel. -/
theorem centralSoninProjectionQuantumWalk_sub_adjoint_eq_four_mul_cutoffCommutator
    (a : ℝ) :
    centralSoninProjectionQuantumWalk a -
        adjoint (centralSoninProjectionQuantumWalk a) =
      4 * ccmCommutator
        (centralPhysicalForbidden a).starProjection
        (centralFourierForbidden a).starProjection := by
  simpa only [centralSoninProjectionQuantumWalk, ccmCommutator] using
    HTGeometry.twoProjectionQuantumWalk_sub_adjoint_eq_four_mul_commutator
      (centralPhysicalForbidden a).starProjection
      (centralFourierForbidden a).starProjection
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

end

end RHTower
