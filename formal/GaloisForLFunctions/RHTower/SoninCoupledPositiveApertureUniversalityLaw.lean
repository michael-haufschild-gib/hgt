import GaloisForLFunctions.RHTower.XiSoninStrictHankelRayUniversalityLaw

/-!
# Coupled-Sonin nondegeneracy discharged at every positive aperture

The explicit prime-square residual makes the coupled all-prime Sonin source nonzero at every
positive aperture.  Hence the proof-carrying nondegenerate-aperture type is equivalent to the
plain positive-aperture type, and every determinant-collar classification can be stated without
an additional source-nondegeneracy interface.
-/

namespace RHTower

noncomputable section

/-- Coupled-source nondegeneracy imposes no restriction beyond positivity of the aperture. -/
def soninCoupledNondegenerateApertureEquiv :
    SoninCoupledNondegenerateAperture ≃ SoninPositiveAperture where
  toFun := fun a => a.1
  invFun := soninCoupledNondegenerateAperture
  left_inv := by
    intro a
    apply Subtype.ext
    rfl
  right_inv := by
    intro a
    rfl

@[simp]
theorem soninCoupledNondegenerateApertureEquiv_apply
    (a : SoninCoupledNondegenerateAperture) :
    soninCoupledNondegenerateApertureEquiv a = a.1 := rfl

@[simp]
theorem soninCoupledNondegenerateApertureEquiv_symm_apply
    (a : SoninPositiveAperture) :
    soninCoupledNondegenerateApertureEquiv.symm a =
      soninCoupledNondegenerateAperture a := rfl

/-- Simultaneous relative-determinant collars over the intrinsic domain `a > 0`, with source
nondegeneracy supplied by the explicit prime-square residual. -/
def SoninAllPositiveApertureUnitCollarPhase : Prop :=
  ∀ a : SoninPositiveAperture,
    UnitCollarExponentialEnvelope (fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
          (soninCoupledNondegenerateAperture a)) n)

/-- Synchronized collar failure over every positive aperture. -/
def SoninAllPositiveApertureUnitCollarFailurePhase : Prop :=
  ∀ a : SoninPositiveAperture,
    ¬UnitCollarExponentialEnvelope (fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
          (soninCoupledNondegenerateAperture a)) n)

/-- The old proof-carrying universal collar phase and the positive-aperture phase are identical. -/
theorem
    soninAllPositiveApertureUnitCollarPhase_iff_allNondegenerateApertureUnitCollarPhase :
    SoninAllPositiveApertureUnitCollarPhase ↔
      SoninAllNondegenerateApertureUnitCollarPhase := by
  constructor
  · intro h a
    have ha :
        soninCoupledNondegenerateAperture a.1 = a := by
      apply Subtype.ext
      rfl
    simpa only [ha] using h a.1
  · intro h a
    exact h (soninCoupledNondegenerateAperture a)

/-- At every positive aperture, the concrete relative determinant collar is exactly RH; no
source-nondegeneracy premise or witness remains in the statement. -/
theorem riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar
    (a : SoninPositiveAperture) :
    RiemannHypothesis ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment
            (soninCoupledNondegenerateAperture a)) n) :=
  riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar
    (soninCoupledNondegenerateAperture a)

/-- Exact prescribed Hilbert reconstruction of every finite prime--archimedean packet is
equivalent to determinant collars at every positive Sonin aperture. -/
theorem
    primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarPhase :
    PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      SoninAllPositiveApertureUnitCollarPhase :=
  primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninNondegenerateApertureUnitCollarPhase.trans
    soninAllPositiveApertureUnitCollarPhase_iff_allNondegenerateApertureUnitCollarPhase.symm

/-- The synchronized failure phase is likewise unchanged after eliminating the redundant
nondegeneracy witness. -/
theorem
    soninAllPositiveApertureUnitCollarFailurePhase_iff_allNondegenerateApertureUnitCollarFailurePhase :
    SoninAllPositiveApertureUnitCollarFailurePhase ↔
      SoninAllNondegenerateApertureUnitCollarFailurePhase := by
  constructor
  · intro h a
    have ha :
        soninCoupledNondegenerateAperture a.1 = a := by
      apply Subtype.ext
      rfl
    simpa only [ha] using h a.1
  · intro h a
    exact h (soninCoupledNondegenerateAperture a)

/-- Failure of exact prescribed Hilbert reconstruction is equivalent to collar failure at every
positive Sonin aperture. -/
theorem
    not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarFailurePhase :
    ¬PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      SoninAllPositiveApertureUnitCollarFailurePhase :=
  not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase.trans
    soninAllPositiveApertureUnitCollarFailurePhase_iff_allNondegenerateApertureUnitCollarFailurePhase.symm

end

end RHTower
