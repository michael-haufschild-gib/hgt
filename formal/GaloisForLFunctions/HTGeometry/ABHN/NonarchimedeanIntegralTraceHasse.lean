import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldIntegralNorm

/-! # Hasse quotient for reduced integral trace in an unramified lift -/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Integral trace followed by reduction to the residue field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) :
    AdjoinRoot f →+ IsLocalRing.ResidueField (ValuativeRel.valuation K).integer :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)).toAddMonoidHom.comp
    (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f)).toAddMonoidHom

@[simp] theorem nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (x : AdjoinRoot f) :
    nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f x =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x) := by
  rfl

theorem nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) :
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f) :=
  nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reduction_surjective
    K f hf g hgmonic hfg hg

noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionHasseQuotientEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) :
    AdjoinRoot f ⧸
        (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f).ker ≃+
      IsLocalRing.ResidueField (ValuativeRel.valuation K).integer :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f)
    (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom_surjective
      K f hf g hgmonic hfg hg)

@[simp] theorem
    nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionHasseQuotientEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) (x : AdjoinRoot f) :
    nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionHasseQuotientEquiv
        K f hf g hgmonic hfg hg (QuotientAddGroup.mk x) =
      nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f x := by
  rfl

theorem nonarchimedeanLocalFieldAdjoinRootIntegralTraceReduction_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (x y : AdjoinRoot f) :
    x - y ∈
        (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f).ker ↔
      nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f x =
        nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f y := by
  change nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom
      K f (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

theorem nonarchimedeanLocalFieldAdjoinRootIntegralTraceReduction_exists_unique_mod_kernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g)
    (a : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) :
    ∃ x : AdjoinRoot f,
      nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f x = a ∧
      ∀ y : AdjoinRoot f,
        nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f y = a ↔
          y - x ∈
            (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom K f).ker := by
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRootIntegralTraceReductionAddHom_surjective
      K f hf g hgmonic hfg hg a
  refine ⟨x, hx, fun y => ?_⟩
  simpa only [hx] using
    (nonarchimedeanLocalFieldAdjoinRootIntegralTraceReduction_congr_hasse_iff
      K f y x).symm

end GaloisForLFunctions.HTGeometry.ABHN
