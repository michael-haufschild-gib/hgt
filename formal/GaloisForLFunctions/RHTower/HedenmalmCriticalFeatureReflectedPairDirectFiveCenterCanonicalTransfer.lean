import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureReflectedPairDirectFiveCenterCharge
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalPhaseSourceDecomposition
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedSourcePlemeljCovariance

/-!
# Canonical source transfer at the reflected five-center HCF constant

The reflected five-center receiver raises the sufficient 75% ceiling to
`15872/21125 + 4/221`.  This module transports that exact constant through the already-proved
pre-divisor Plemelj replacement and through the strongest phase-preserving finite source
majorant.  No divisor-dependent trace occurs in the resulting quantitative premise.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- At the reflected five-center constant, the corrected HCF ceiling is equivalent to the literal
source-only pole--Gamma Plemelj covariance ceiling. -/
theorem canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectFiveCenter :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125 + 4 / 221) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125 + 4 / 221) :=
  criticalFeatureCanonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    tendsto_canonical_correctedBudget_sub_plemeljCovariance_div

/-- An asymptotic ceiling for the explicit regular finite source-piece majorant transfers to the
corrected HCF budget at the reflected five-center constant. -/
theorem canonical_correctedBudget_ceiling_of_regularSourcePieceMajorant_reflectedDirectFiveCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularSourcePieceMajorant
        (15872 / 21125 + 4 / 221)) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125 + 4 / 221) := by
  apply
    canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectFiveCenter.mpr
  exact
    (canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125 + 4 / 221)).mp
      (canonicalRegularLatticeSummedDisplacement_ceiling_of_sourcePieceMajorant hsource)

/-- Strongest current phase-preserving source-to-five-center connector.  It is enough to control
the explicit source majorant at `15872/21125 + 4/221`. -/
theorem
    canonical_correctedBudget_ceiling_of_regularPhaseSourcePieceMajorant_reflectedDirectFiveCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularPhaseSourcePieceMajorant
        (15872 / 21125 + 4 / 221)) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125 + 4 / 221) := by
  apply
    canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectFiveCenter.mpr
  exact
    (canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125 + 4 / 221)).mp
      (canonicalRegularLatticeSummedDisplacement_ceiling_of_phaseSourcePieceMajorant hsource)

end

end RHTower
