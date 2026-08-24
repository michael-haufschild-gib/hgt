import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanIntegralNormHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanIntegralTraceHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanGradedNormHasse
import GaloisForLFunctions.HTGeometry.ABHN.AdicTameResidueQuotientEquiv
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldMilnorResidue

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

/-- At each finite number-field place, the completed-adic tame quotient is completely detected
by its residue-field `K₁ᴹ` coordinate. -/
noncomputable def numberFieldFiniteAdicTameHasseFamily
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K) :=
  HasseFamily.ofEquivSingle
    (numberFieldFiniteAdicTameQuotientEquivGlobalResidue K v).toEquiv

/-- At each finite place of `F(t)`, the completed-adic tame quotient is completely detected by
its residue-field `K₁ᴹ` coordinate. -/
noncomputable def rationalFunctionFiniteAdicTameHasseFamily
    (F : Type u) [Field F] [Finite F]
    (v : IsDedekindDomain.HeightOneSpectrum (Polynomial F)) :=
  HasseFamily.ofEquivSingle
    (rationalFunctionFiniteAdicTameQuotientEquivGlobalResidue F v).toEquiv

/-- The local Milnor `K₂` quotient by the standard tame-residue kernel is completely detected by
residue-field `K₁ᴹ`. -/
noncomputable def nonarchimedeanLocalTameMilnorHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :=
  HasseFamily.ofEquivSingle
    (nonarchimedeanLocalFieldTameMilnorResidueQuotientKerEquiv K).toEquiv

/-- The local Milnor `K₂` quotient by the tame-symbol kernel is completely detected by the
residue-unit coordinate. -/
noncomputable def nonarchimedeanLocalTameUnitHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :=
  HasseFamily.ofEquivSingle
    (nonarchimedeanLocalFieldTameHomQuotientKerEquiv K).toEquiv

end
end GaloisForLFunctions.HTGeometry.ABHN
