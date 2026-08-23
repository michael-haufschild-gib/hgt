import GaloisForLFunctions.HTGeometry.ABHN.PrincipalUnitGradedHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldIntegralNorm

/-! # Hasse quotient for unramified norms on principal-unit gradeds -/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- The associated graded principal-unit group of an unramified root lift. -/
abbrev nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGraded
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ) :=
  (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) ⧸
    (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n)

/-- Source associated-graded units modulo equal graded norm are the base associated graded. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGradedHasseQuotientEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    let φ := nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
      K f hf g hgmonic hfg hg n hn
    nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGraded K f hf g hfg hg n ⧸
      φ.ker ≃* nonarchimedeanLocalFieldPrincipalUnitGraded K n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  exact QuotientGroup.quotientKerEquivOfSurjective
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
      K f hf g hgmonic hfg hg n hn)
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnitGraded_surjective
      K f hf g hgmonic hfg hg n hn)

@[simp] theorem nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGradedHasseQuotientEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∀ x : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGraded K f hf g hfg hg n,
      nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGradedHasseQuotientEquiv
          K f hf g hgmonic hfg hg n hn (QuotientGroup.mk x) =
        nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
          K f hf g hgmonic hfg hg n hn x := by
  intro x
  rfl

/-- Two source graded classes have equal norm exactly modulo the graded norm kernel. -/
theorem nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∀ x y : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGraded K f hf g hfg hg n,
      x * y⁻¹ ∈ (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
          K f hf g hgmonic hfg hg n hn).ker ↔
        nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
            K f hf g hgmonic hfg hg n hn x =
          nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
            K f hf g hgmonic hfg hg n hn y := by
  intro x y
  change nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
      K f hf g hgmonic hfg hg n hn (x * y⁻¹) = 1 ↔ _
  rw [map_mul, map_inv, mul_inv_eq_one]

end


end GaloisForLFunctions.HTGeometry.ABHN
