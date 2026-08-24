import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanIntegralNormHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanIntegralTraceHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanGradedNormHasse

/-!
# Local cohomology Hasse-family applications

Complete one-place invariants furnished by the nonarchimedean infrastructure: continuous
finite-unramified `H²`, integral norm, residue trace, and positive principal-unit graded norm.
These are local class-field-theory components; no `H²`--Brauer comparison is added.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- The finite unramified continuous `H²` torsion invariant is a complete one-place Hasse
coordinate. -/
noncomputable def NonarchimedeanFiniteUnramifiedRootLift.continuousH2HasseFamily
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  HasseFamily.ofEquivSingle D.continuousH2NTorsionInvariant.toEquiv

/-- The unramified integral norm is a complete one-place invariant modulo its kernel. -/
noncomputable def nonarchimedeanIntegralNormUnitsQuotientHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :=
  HasseFamily.ofEquivSingle
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsHasseQuotientEquiv
      K f hf g hgmonic hfg hg).toEquiv

/-- Integral trace reduction is a complete one-place invariant modulo its kernel. -/
noncomputable def nonarchimedeanIntegralTraceReductionQuotientHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :=
  HasseFamily.ofEquivSingle
    (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionHasseQuotientEquiv
      K f hf g hgmonic hfg hg).toEquiv

/-- Each positive principal-unit graded norm is a complete one-place invariant modulo its
kernel. -/
noncomputable def nonarchimedeanPrincipalUnitGradedNormQuotientHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :=
  HasseFamily.ofEquivSingle
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGradedHasseQuotientEquiv
      K f hf g hgmonic hfg hg n hn).toEquiv

end
end GaloisForLFunctions.HTGeometry.ABHN
