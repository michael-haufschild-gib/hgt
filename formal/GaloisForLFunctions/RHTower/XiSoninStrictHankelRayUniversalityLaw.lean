import GaloisForLFunctions.RHTower.PrimeArchExactReconstructionStrictHankelRayUniversalityLaw
import GaloisForLFunctions.RHTower.SoninCoupledRelativeDeterminantRHUniversalityLaw

/-!
# Sonin determinant collars and all strict Hankel rays

One nondegenerate coupled-Sonin relative determinant collar is already an exact RH classifier.
The prime--archimedean strict-ray theorem classifies RH by closure under every strict
`HTGeometry` Hankel moment ray.  Combining them identifies two universal families: one Sonin
aperture controls every strict spectral ray, while one strict-ray failure forces failure at every
Sonin aperture.

Exact prescribed Hilbert reconstruction is the common finite source interface between these
families.
-/

namespace RHTower

noncomputable section

/-- Simultaneous relative-determinant unit collars at every nondegenerate coupled-Sonin
aperture. -/
def SoninAllNondegenerateApertureUnitCollarPhase : Prop :=
  ∀ a : SoninCoupledNondegenerateAperture,
    UnitCollarExponentialEnvelope (fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n)

/-- Synchronized Sonin failure: the relative-determinant unit collar fails at every
nondegenerate aperture. -/
def SoninAllNondegenerateApertureUnitCollarFailurePhase : Prop :=
  ∀ a : SoninCoupledNondegenerateAperture,
    ¬UnitCollarExponentialEnvelope (fun n =>
      bernsteinCoefficientPurity
        (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n)

/-- **Single-Sonin/all-strict-ray universality law.**  At any one nondegenerate aperture, its
relative determinant collar is exactly closure under every strict `HTGeometry` Hankel ray. -/
theorem soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningPhase
    (a : SoninCoupledNondegenerateAperture) :
    UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) ↔
      PrimeArchAllStrictHankelRayAdjoiningPhase :=
  (riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar a).symm.trans
    primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis.symm

/-- **Universal Sonin/strict-ray collapse.**  Closure under every strict Hankel ray is equivalent
to simultaneous determinant collars at every nondegenerate Sonin aperture.  The reverse
direction needs only the canonical unit aperture. -/
theorem
    primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase :
    PrimeArchAllStrictHankelRayAdjoiningPhase ↔
      SoninAllNondegenerateApertureUnitCollarPhase := by
  constructor
  · intro hphase a
    exact
      (soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningPhase
        a).2 hphase
  · intro hall
    let a : SoninCoupledNondegenerateAperture :=
      soninCoupledNondegenerateAperture ⟨1, zero_lt_one⟩
    exact
      (soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningPhase
        a).1 (hall a)

/-- Every Sonin collar is equivalent to any one chosen nondegenerate collar.  Thus aperture
universality is already detected at one aperture. -/
theorem soninAllNondegenerateApertureUnitCollarPhase_iff_singleAperture
    (a : SoninCoupledNondegenerateAperture) :
    SoninAllNondegenerateApertureUnitCollarPhase ↔
      UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) :=
  primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase.symm.trans
    (soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningPhase
      a).symm

/-- **Hilbert-reconstruction/Sonin-family connector.**  Exact prescribed dual reconstruction of
all finite prime--arch source packets is equivalent to simultaneous determinant collars at every
nondegenerate Sonin aperture. -/
theorem
    primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninNondegenerateApertureUnitCollarPhase :
    PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      SoninAllNondegenerateApertureUnitCollarPhase :=
  primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningPhase.trans
    primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase

/-- Failure of one chosen Sonin determinant collar is exactly the synchronized failure of every
strict auxiliary Hankel ray. -/
theorem
    not_soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningFailurePhase
    (a : SoninCoupledNondegenerateAperture) :
    (¬UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n)) ↔
      PrimeArchAllStrictHankelRayAdjoiningFailurePhase :=
  (not_congr
    (soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningPhase
      a)).trans
        not_primeArchAllStrictHankelRayAdjoiningPhase_iff_allStrictHankelRayAdjoiningFailurePhase

/-- **Synchronized Sonin/strict-ray failure law.**  Every strict Hankel ray fails exactly when
every nondegenerate Sonin determinant collar fails. -/
theorem
    primeArchAllStrictHankelRayAdjoiningFailurePhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase :
    PrimeArchAllStrictHankelRayAdjoiningFailurePhase ↔
      SoninAllNondegenerateApertureUnitCollarFailurePhase := by
  constructor
  · intro hfailure a
    exact
      (not_soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningFailurePhase
        a).2 hfailure
  · intro hall
    let a : SoninCoupledNondegenerateAperture :=
      soninCoupledNondegenerateAperture ⟨1, zero_lt_one⟩
    exact
      (not_soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningFailurePhase
        a).1 (hall a)

/-- Synchronized Sonin failure is already equivalent to failure at any one chosen nondegenerate
aperture. -/
theorem soninAllNondegenerateApertureUnitCollarFailurePhase_iff_not_singleAperture
    (a : SoninCoupledNondegenerateAperture) :
    SoninAllNondegenerateApertureUnitCollarFailurePhase ↔
      ¬UnitCollarExponentialEnvelope (fun n =>
        bernsteinCoefficientPurity
          (soninCoupledRelativeNormalizedSpectralLogDerivativeMoment a) n) :=
  primeArchAllStrictHankelRayAdjoiningFailurePhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase.symm.trans
    (not_soninCoupledRelativeDeterminant_unitCollar_iff_allStrictHankelRayAdjoiningFailurePhase
      a).symm

/-- Exact prescribed source reconstruction fails exactly when all nondegenerate Sonin collars
fail simultaneously. -/
theorem
    not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase :
    ¬PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      SoninAllNondegenerateApertureUnitCollarFailurePhase :=
  not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningFailurePhase.trans
    primeArchAllStrictHankelRayAdjoiningFailurePhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase

/-- Failure of merely one member of the universal Sonin collar family is already synchronized
failure at every aperture. -/
theorem
    not_soninAllNondegenerateApertureUnitCollarPhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase :
    ¬SoninAllNondegenerateApertureUnitCollarPhase ↔
      SoninAllNondegenerateApertureUnitCollarFailurePhase :=
  (not_congr
    primeArchAllStrictHankelRayAdjoiningPhase_iff_allSoninNondegenerateApertureUnitCollarPhase).symm.trans
      (not_primeArchAllStrictHankelRayAdjoiningPhase_iff_allStrictHankelRayAdjoiningFailurePhase.trans
        primeArchAllStrictHankelRayAdjoiningFailurePhase_iff_allSoninNondegenerateApertureUnitCollarFailurePhase)

end

end RHTower
