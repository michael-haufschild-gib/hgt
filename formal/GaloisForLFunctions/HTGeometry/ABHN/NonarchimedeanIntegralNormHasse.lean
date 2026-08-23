import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldIntegralNorm

/-!
# Hasse quotient for unramified integral unit norms

For a finite unramified root lift of a nonarchimedean local field, the integral norm on units is
surjective.  Hence source units modulo the norm kernel are exactly base units.  This removes the
unit contribution from the unramified local norm quotient and leaves its valuation-lattice part.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- The packaged additive integral norm on units of an unramified root lift is surjective. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsAdditive_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg) := by
  intro a
  obtain ⟨b, hb⟩ := nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_surjective
    K f hf g hgmonic hfg hg a.toMul
  refine ⟨Additive.ofMul b, ?_⟩
  apply Additive.toMul.injective
  change nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul
      K f hf g hgmonic hfg hg b = a.toMul
  rw [nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul_apply]
  exact hb

/-- Source integral units modulo equal-norm classes are additively equivalent to base integral
units. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsHasseQuotientEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    Additive (AdjoinRoot f)ˣ ⧸
        (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
          K f hf g hgmonic hfg hg).ker ≃+
      Additive (ValuativeRel.valuation K).integerˣ :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg)
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsAdditive_surjective
      K f hf g hgmonic hfg hg)

/-- The unramified integral-norm quotient equivalence is induced by the norm map. -/
@[simp] theorem
    nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsHasseQuotientEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (x : Additive (AdjoinRoot f)ˣ) :
    nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsHasseQuotientEquiv
        K f hf g hgmonic hfg hg (QuotientAddGroup.mk x) =
      nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
        K f hf g hgmonic hfg hg x := by
  rfl

/-- Two source integral units have equal norm exactly when their difference lies in the norm
kernel. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (x y : Additive (AdjoinRoot f)ˣ) :
    x - y ∈ (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
        K f hf g hgmonic hfg hg).ker ↔
      nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
          K f hf g hgmonic hfg hg x =
        nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
          K f hf g hgmonic hfg hg y := by
  change nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
      K f hf g hgmonic hfg hg (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every base integral unit is an unramified integral norm, uniquely modulo the norm kernel. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_exists_unique_mod_kernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (a : Additive (ValuativeRel.valuation K).integerˣ) :
    ∃ x : Additive (AdjoinRoot f)ˣ,
      nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
          K f hf g hgmonic hfg hg x = a ∧
      ∀ y : Additive (AdjoinRoot f)ˣ,
        nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
            K f hf g hgmonic hfg hg y = a ↔
          y - x ∈ (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
            K f hf g hgmonic hfg hg).ker := by
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsAdditive_surjective
      K f hf g hgmonic hfg hg a
  refine ⟨x, hx, fun y => ?_⟩
  simpa only [hx] using
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_congr_hasse_iff
      K f hf g hgmonic hfg hg y x).symm

end GaloisForLFunctions.HTGeometry.ABHN
