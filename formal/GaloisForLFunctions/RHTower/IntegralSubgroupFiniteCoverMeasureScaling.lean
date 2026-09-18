import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCoverFundamentalDomain

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise Function

noncomputable section

theorem integralFiniteCoverFundamentalSet_aedisjoint (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] :
    Pairwise ((AEDisjoint realSL2Haar) on fun q : Γ ⧸ K.subgroupOf Γ =>
      MulOpposite.op (integralSL2ToReal q.out.val) • integralSubgroupFundamentalSet Γ) := by
  let qΓ : Γ ⧸ K.subgroupOf Γ → (realImage Γ).op := fun q =>
    ⟨MulOpposite.op (integralSL2ToReal q.out.val), by
      change integralSL2ToReal q.out.val ∈ realImage Γ
      exact ⟨q.out.val, q.out.property, rfl⟩⟩
  have hqΓ_injective : Function.Injective qΓ := by
    intro q₁ q₂ h
    apply Quotient.out_injective
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
    exact congrArg (fun z : (realImage Γ).op => z.val.unop) h
  change Pairwise ((AEDisjoint realSL2Haar) on fun q =>
    qΓ q • integralSubgroupFundamentalSet Γ)
  intro q₁ q₂ hne
  apply (integralSubgroupFundamentalSet_isFundamentalDomain Γ).aedisjoint
  exact fun h => hne (hqΓ_injective h)

theorem measure_integralFiniteCoverFundamentalSet (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] :
    realSL2Haar (integralFiniteCoverFundamentalSet K Γ) =
      Nat.card (Γ ⧸ K.subgroupOf Γ) •
        realSL2Haar (integralSubgroupFundamentalSet Γ) := by
  letI : Fintype (Γ ⧸ K.subgroupOf Γ) := Fintype.ofFinite _
  rw [integralFiniteCoverFundamentalSet]
  rw [measure_iUnion₀ (integralFiniteCoverFundamentalSet_aedisjoint K Γ)]
  · simp only [measure_smul, tsum_fintype, Finset.sum_const,
      Nat.card_eq_fintype_card]
    rfl
  · intro q
    exact ((integralSubgroupFundamentalSet_measurable Γ).const_smul _).nullMeasurableSet

/-- The canonical quotient measure can use the finite selector. -/
theorem integralSubgroupQuotientMeasure_eq_map_finiteCoverFundamentalSet
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    integralSubgroupQuotientMeasure K =
      (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ)).map
        QuotientGroup.mk := by
  let μK : Measure (SL2R ⧸ realImage K) :=
    (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ)).map
      QuotientGroup.mk
  letI : QuotientMeasureEqMeasurePreimage realSL2Haar μK :=
    (integralFiniteCoverFundamentalSet_isFundamentalDomain K Γ hKΓ).quotientMeasureEqMeasurePreimage_quotientMeasure
  exact QuotientMeasureEqMeasurePreimage.unique
    (G := (realImage K).op) (α := SL2R) (ν := realSL2Haar)
    (integralSubgroupQuotientMeasure K) μK

private theorem quotient_preimage_smul_eq (Γ : Subgroup SL2Z)
    (U : Set (SL2R ⧸ realImage Γ)) (g : (realImage Γ).op) :
    g • (QuotientGroup.mk ⁻¹' U) = QuotientGroup.mk ⁻¹' U := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
  have hginv : (g⁻¹).val.unop ∈ realImage Γ := (g⁻¹).property
  have heq : (QuotientGroup.mk (g⁻¹ • x) : SL2R ⧸ realImage Γ) =
      QuotientGroup.mk x := by
    change QuotientGroup.mk (x * (g⁻¹).val.unop) = QuotientGroup.mk x
    exact QuotientGroup.mk_mul_of_mem x hginv
  rw [heq]

private theorem measure_quotient_preimage_inter_translated_fundamentalSet
    (Γ : Subgroup SL2Z) (U : Set (SL2R ⧸ realImage Γ))
    (q : (realImage Γ).op) :
    realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ q • integralSubgroupFundamentalSet Γ) =
      realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ integralSubgroupFundamentalSet Γ) := by
  calc
    realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ q • integralSubgroupFundamentalSet Γ) =
        realSL2Haar (q • (QuotientGroup.mk ⁻¹' U ∩ integralSubgroupFundamentalSet Γ)) := by
      rw [Set.smul_set_inter, quotient_preimage_smul_eq]
    _ = realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ integralSubgroupFundamentalSet Γ) :=
      measure_smul realSL2Haar q _

theorem map_restrict_integralFiniteCoverFundamentalSet (K Γ : Subgroup SL2Z)
    [K.IsFiniteRelIndex Γ] :
    Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ realImage Γ)
      (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ)) =
      Nat.card (Γ ⧸ K.subgroupOf Γ) •
        Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ realImage Γ)
          (realSL2Haar.restrict (integralSubgroupFundamentalSet Γ)) := by
  letI : Fintype (Γ ⧸ K.subgroupOf Γ) := Fintype.ofFinite _
  ext U hU
  have hP : MeasurableSet (QuotientGroup.mk ⁻¹' U : Set SL2R) :=
    (QuotientGroup.measurable_coe :
      Measurable (QuotientGroup.mk : SL2R → SL2R ⧸ realImage Γ)) hU
  rw [Measure.map_apply QuotientGroup.measurable_coe hU, Measure.restrict_apply hP]
  change realSL2Haar (QuotientGroup.mk ⁻¹' U ∩
      integralFiniteCoverFundamentalSet K Γ) =
    Nat.card (Γ ⧸ K.subgroupOf Γ) •
      (Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ realImage Γ)
        (realSL2Haar.restrict (integralSubgroupFundamentalSet Γ))) U
  rw [Measure.map_apply QuotientGroup.measurable_coe hU, Measure.restrict_apply hP]
  rw [integralFiniteCoverFundamentalSet, inter_iUnion]
  rw [measure_iUnion₀]
  · let qΓ : Γ ⧸ K.subgroupOf Γ → (realImage Γ).op := fun q =>
      ⟨MulOpposite.op (integralSL2ToReal q.out.val), by
        change integralSL2ToReal q.out.val ∈ realImage Γ
        exact ⟨q.out.val, q.out.property, rfl⟩⟩
    have hterm : ∀ q : Γ ⧸ K.subgroupOf Γ,
        realSL2Haar (QuotientGroup.mk ⁻¹' U ∩
          MulOpposite.op (integralSL2ToReal q.out.val) • integralSubgroupFundamentalSet Γ) =
          realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ integralSubgroupFundamentalSet Γ) := by
      intro q
      simpa [qΓ] using
        (measure_quotient_preimage_inter_translated_fundamentalSet Γ U (qΓ q))
    simp_rw [hterm]
    simp only [tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    rfl
  · intro q₁ q₂ hne
    exact (integralFiniteCoverFundamentalSet_aedisjoint K Γ hne).mono
      inter_subset_right inter_subset_right
  · intro q
    exact (hP.inter ((integralSubgroupFundamentalSet_measurable Γ).const_smul _)).nullMeasurableSet

/-- The quotient projection scales its canonical measure by the finite deck degree. -/
theorem map_subgroupQuotientProjection_integralSubgroupQuotientMeasure
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Measure.map
      (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ))
      (integralSubgroupQuotientMeasure K) =
      Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ := by
  let hreal : realImage K ≤ realImage Γ := Subgroup.map_mono hKΓ
  let p := subgroupQuotientProjection (realImage K) (realImage Γ) hreal
  let πK : SL2R → SL2R ⧸ realImage K := QuotientGroup.mk
  let πΓ : SL2R → SL2R ⧸ realImage Γ := QuotientGroup.mk
  have hp : Measurable p := subgroupQuotientProjection_measurable _ _ hreal
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hcomp : p ∘ πK = πΓ := by
    funext x
    exact subgroupQuotientProjection_mk _ _ hreal x
  change Measure.map p (integralSubgroupQuotientMeasure K) = _
  rw [integralSubgroupQuotientMeasure_eq_map_finiteCoverFundamentalSet K Γ hKΓ]
  calc
    Measure.map p (Measure.map πK
        (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ))) =
        Measure.map (p ∘ πK)
          (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ)) :=
      Measure.map_map hp hπK
    _ = Measure.map πΓ
          (realSL2Haar.restrict (integralFiniteCoverFundamentalSet K Γ)) := by rw [hcomp]
    _ = Nat.card (Γ ⧸ K.subgroupOf Γ) •
          Measure.map πΓ (realSL2Haar.restrict (integralSubgroupFundamentalSet Γ)) :=
      map_restrict_integralFiniteCoverFundamentalSet K Γ
    _ = Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ := by rfl

/-- Pullback across a finite subgroup cover has the exact scaled `Lᵖ` seminorm. -/
theorem eLpNorm_comp_subgroupQuotientProjection
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ)
    (f : (SL2R ⧸ realImage Γ) → E) (p : ENNReal)
    (hf : AEStronglyMeasurable f
      (Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ)) :
    eLpNorm
      (f ∘ subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ))
      p (integralSubgroupQuotientMeasure K) =
      eLpNorm f p
        (Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ) := by
  let hreal : realImage K ≤ realImage Γ := Subgroup.map_mono hKΓ
  let proj := subgroupQuotientProjection (realImage K) (realImage Γ) hreal
  have hproj : Measurable proj := subgroupQuotientProjection_measurable _ _ hreal
  have hmap : Measure.map proj (integralSubgroupQuotientMeasure K) =
      Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ :=
    map_subgroupQuotientProjection_integralSubgroupQuotientMeasure K Γ hKΓ
  have hfmap : AEStronglyMeasurable f
      (Measure.map proj (integralSubgroupQuotientMeasure K)) := by
    rw [hmap]
    exact hf
  exact (eLpNorm_map_measure hfmap hproj.aemeasurable).symm.trans (by rw [hmap])

/-- Finite-cover pullback preserves `Lᵖ` admission after the exact degree rescaling. -/
theorem memLp_comp_subgroupQuotientProjection
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ)
    (f : (SL2R ⧸ realImage Γ) → E) (p : ENNReal)
    (hf : MemLp f p (integralSubgroupQuotientMeasure Γ)) :
    MemLp
      (f ∘ subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ))
      p (integralSubgroupQuotientMeasure K) := by
  let hreal : realImage K ≤ realImage Γ := Subgroup.map_mono hKΓ
  let proj := subgroupQuotientProjection (realImage K) (realImage Γ) hreal
  have hproj : Measurable proj := subgroupQuotientProjection_measurable _ _ hreal
  have hmap : Measure.map proj (integralSubgroupQuotientMeasure K) =
      Nat.card (Γ ⧸ K.subgroupOf Γ) • integralSubgroupQuotientMeasure Γ :=
    map_subgroupQuotientProjection_integralSubgroupQuotientMeasure K Γ hKΓ
  apply MemLp.comp_of_map (hf := hproj.aemeasurable)
  rw [hmap]
  simpa only [Nat.cast_smul_eq_nsmul] using
    hf.smul_measure (c := (Nat.card (Γ ⧸ K.subgroupOf Γ) : ENNReal)) (by simp)

end

end GaloisForLFunctions.RHTower
