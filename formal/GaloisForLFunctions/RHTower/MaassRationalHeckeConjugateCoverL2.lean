import GaloisForLFunctions.RHTower.RationalConjugateSL2QuotientMeasure

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise Function

noncomputable section

abbrev rationalHeckeCommonCoverReal (N : ℕ) (g : GL (Fin 2) ℚ) : Subgroup SL2R :=
  realImage (rationalHeckeIntegralIntersection N g)

instance rationalHeckeCommonCoverReal_isFiniteRelIndex_conjugate
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalHeckeCommonCoverReal N g).IsFiniteRelIndex (rationalConjugateSL2Group N g) :=
  realImage_rationalHeckeIntegralIntersection_isFiniteRelIndex_conjugate N g

/-- Finite-selector candidate for the common cover over the rational-conjugate source. -/
def rationalConjugateFiniteCoverFundamentalSet (N : ℕ) (g : GL (Fin 2) ℚ) : Set SL2R :=
  ⋃ q : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
    MulOpposite.op q.out.val • rationalConjugateSL2FundamentalSet N g

theorem rationalConjugateFiniteCoverFundamentalSet_measurable (N : ℕ) (g : GL (Fin 2) ℚ) :
    MeasurableSet (rationalConjugateFiniteCoverFundamentalSet N g) := by
  letI : Fintype ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :=
    Fintype.ofFinite _
  apply MeasurableSet.iUnion
  intro q
  exact (rationalConjugateSL2FundamentalSet_measurable N g).const_smul _

theorem rationalConjugateFiniteCoverFundamentalSet_unique (N : ℕ) (g : GL (Fin 2) ℚ)
    (x : SL2R) :
    ∃! k : (rationalHeckeCommonCoverReal N g).op,
      k • x ∈ rationalConjugateFiniteCoverFundamentalSet N g := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  letI : K.IsFiniteRelIndex R :=
    realImage_rationalHeckeIntegralIntersection_isFiniteRelIndex_conjugate N g
  have hKR : K ≤ R := realImage_rationalHeckeIntegralIntersection_le_conjugate N g
  obtain ⟨γ, hγ, hγuniq⟩ := rationalConjugateSL2FundamentalSet_unique N g x
  let A : R := ⟨γ.val.unop, γ.property⟩
  obtain ⟨k, q, hA⟩ := subgroup_exists_left_coset_decomposition K R hKR A
  let kR : K.op := ⟨MulOpposite.op k.val, by
    change k.val ∈ K
    exact k.property⟩
  refine ⟨kR, ?_, ?_⟩
  · refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    refine Set.mem_smul_set.mpr ⟨γ • x, hγ, ?_⟩
    change (γ • x) * q.out.val = x * k.val
    change (x * γ.val.unop) * q.out.val = x * k.val
    have hAreal : γ.val.unop = k.val * q.out.val⁻¹ := by
      simpa [A] using congrArg Subtype.val hA
    rw [hAreal]
    group
  · intro k' hk'
    rcases Set.mem_iUnion.mp hk' with ⟨q', hq'⟩
    rcases Set.mem_smul_set.mp hq' with ⟨y, hy, hEq⟩
    let k'' : K := ⟨k'.val.unop, k'.property⟩
    let δ : R.op := ⟨MulOpposite.op (k''.val * q'.out.val⁻¹), by
      change k''.val * q'.out.val⁻¹ ∈ R
      exact R.mul_mem (hKR k''.property) (R.inv_mem q'.out.property)⟩
    have hδ : δ • x = y := by
      change y * q'.out.val = x * k'.val.unop at hEq
      change x * (k''.val * q'.out.val⁻¹) = y
      calc
        x * (k''.val * q'.out.val⁻¹) =
            (x * k''.val) * q'.out.val⁻¹ := by group
        _ = (y * q'.out.val) * q'.out.val⁻¹ := by rw [← hEq]
        _ = y := by group
    let δ' : (rationalConjugateSL2Group N g).op := ⟨δ.val, by
      change δ.val ∈ R.op
      exact δ.property⟩
    have hδ' : δ' • x = y := by
      change δ • x = y
      exact hδ
    have hδmem : δ' • x ∈ rationalConjugateSL2FundamentalSet N g := by
      rw [hδ']
      exact hy
    have hδeq : δ' = γ := hγuniq δ' hδmem
    have hRealEq : k''.val * q'.out.val⁻¹ = k.val * q.out.val⁻¹ := by
      calc
        k''.val * q'.out.val⁻¹ = δ'.val.unop := rfl
        _ = γ.val.unop := congrArg (fun z : (rationalConjugateSL2Group N g).op => z.val.unop) hδeq
        _ = k.val * q.out.val⁻¹ := by
          simpa [A] using congrArg Subtype.val hA
    have hdecomp : Subgroup.inclusion hKR k'' * q'.out⁻¹ =
        Subgroup.inclusion hKR k * q.out⁻¹ := by
      apply Subtype.ext
      exact hRealEq
    have hqq : q' = q :=
      subgroup_rightCoset_eq_of_left_decomposition K R hKR k'' k q' q hdecomp
    subst q'
    have hk'k : k'' = k := by
      apply Subgroup.inclusion_injective hKR
      exact mul_right_cancel hdecomp
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val hk'k

theorem rationalConjugateFiniteCoverFundamentalSet_isFundamentalDomain
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    IsFundamentalDomain (rationalHeckeCommonCoverReal N g).op
      (rationalConjugateFiniteCoverFundamentalSet N g) realSL2Haar :=
  IsFundamentalDomain.mk'
    (rationalConjugateFiniteCoverFundamentalSet_measurable N g).nullMeasurableSet
    (rationalConjugateFiniteCoverFundamentalSet_unique N g)

theorem rationalConjugateFiniteCoverFundamentalSet_aedisjoint (N : ℕ) (g : GL (Fin 2) ℚ) :
    Pairwise ((AEDisjoint realSL2Haar) on fun q : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g) =>
      MulOpposite.op q.out.val • rationalConjugateSL2FundamentalSet N g) := by
  let qR : (rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g) →
      (rationalConjugateSL2Group N g).op := fun q =>
    ⟨MulOpposite.op q.out.val, q.out.property⟩
  have hqR_injective : Function.Injective qR := by
    intro q₁ q₂ h
    apply Quotient.out_injective
    apply Subtype.ext
    exact congrArg (fun z : (rationalConjugateSL2Group N g).op => z.val.unop) h
  change Pairwise ((AEDisjoint realSL2Haar) on fun q =>
    qR q • rationalConjugateSL2FundamentalSet N g)
  intro q₁ q₂ hne
  apply (rationalConjugateSL2FundamentalSet_isFundamentalDomain N g).aedisjoint
  exact fun h => hne (hqR_injective h)

theorem measure_rationalConjugateFiniteCoverFundamentalSet (N : ℕ) (g : GL (Fin 2) ℚ) :
    realSL2Haar (rationalConjugateFiniteCoverFundamentalSet N g) =
      Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        realSL2Haar (rationalConjugateSL2FundamentalSet N g) := by
  letI : Fintype ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :=
    Fintype.ofFinite _
  rw [rationalConjugateFiniteCoverFundamentalSet]
  rw [measure_iUnion₀ (rationalConjugateFiniteCoverFundamentalSet_aedisjoint N g)]
  · simp only [measure_smul, tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    rfl
  · intro q
    exact ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul _).nullMeasurableSet

/-- The common-cover quotient measure can be represented by its rational finite selector. -/
theorem integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g) =
      (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g)).map
        QuotientGroup.mk := by
  let μK : Measure (SL2R ⧸ rationalHeckeCommonCoverReal N g) :=
    (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g)).map
      QuotientGroup.mk
  letI : QuotientMeasureEqMeasurePreimage realSL2Haar μK :=
    (rationalConjugateFiniteCoverFundamentalSet_isFundamentalDomain N g).quotientMeasureEqMeasurePreimage_quotientMeasure
  exact QuotientMeasureEqMeasurePreimage.unique
    (G := (rationalHeckeCommonCoverReal N g).op) (α := SL2R) (ν := realSL2Haar)
    (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) μK

private theorem rationalConjugate_quotient_preimage_smul_eq (N : ℕ) (g : GL (Fin 2) ℚ)
    (U : Set (SL2R ⧸ rationalConjugateSL2Group N g))
    (h : (rationalConjugateSL2Group N g).op) :
    h • (QuotientGroup.mk ⁻¹' U) = QuotientGroup.mk ⁻¹' U := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
  have hhinv : (h⁻¹).val.unop ∈ rationalConjugateSL2Group N g := (h⁻¹).property
  have heq : (QuotientGroup.mk (h⁻¹ • x) : SL2R ⧸ rationalConjugateSL2Group N g) =
      QuotientGroup.mk x := by
    change QuotientGroup.mk (x * (h⁻¹).val.unop) = QuotientGroup.mk x
    exact QuotientGroup.mk_mul_of_mem x hhinv
  rw [heq]

private theorem measure_rationalConjugate_quotient_preimage_inter_translated_fundamentalSet
    (N : ℕ) (g : GL (Fin 2) ℚ) (U : Set (SL2R ⧸ rationalConjugateSL2Group N g))
    (q : (rationalConjugateSL2Group N g).op) :
    realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ q • rationalConjugateSL2FundamentalSet N g) =
      realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ rationalConjugateSL2FundamentalSet N g) := by
  calc
    realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ q • rationalConjugateSL2FundamentalSet N g) =
        realSL2Haar (q • (QuotientGroup.mk ⁻¹' U ∩ rationalConjugateSL2FundamentalSet N g)) := by
      rw [Set.smul_set_inter, rationalConjugate_quotient_preimage_smul_eq]
    _ = realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ rationalConjugateSL2FundamentalSet N g) :=
      measure_smul realSL2Haar q _

theorem map_restrict_rationalConjugateFiniteCoverFundamentalSet (N : ℕ) (g : GL (Fin 2) ℚ) :
    Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ rationalConjugateSL2Group N g)
      (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g)) =
      Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ rationalConjugateSL2Group N g)
          (realSL2Haar.restrict (rationalConjugateSL2FundamentalSet N g)) := by
  letI : Fintype ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) :=
    Fintype.ofFinite _
  ext U hU
  have hP : MeasurableSet (QuotientGroup.mk ⁻¹' U : Set SL2R) :=
    (QuotientGroup.measurable_coe :
      Measurable (QuotientGroup.mk : SL2R → SL2R ⧸ rationalConjugateSL2Group N g)) hU
  rw [Measure.map_apply QuotientGroup.measurable_coe hU, Measure.restrict_apply hP]
  change realSL2Haar (QuotientGroup.mk ⁻¹' U ∩
      rationalConjugateFiniteCoverFundamentalSet N g) =
    Nat.card ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
      (Measure.map (QuotientGroup.mk : SL2R → SL2R ⧸ rationalConjugateSL2Group N g)
        (realSL2Haar.restrict (rationalConjugateSL2FundamentalSet N g))) U
  rw [Measure.map_apply QuotientGroup.measurable_coe hU, Measure.restrict_apply hP]
  rw [rationalConjugateFiniteCoverFundamentalSet, inter_iUnion]
  rw [measure_iUnion₀]
  · let qR : (rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g) →
        (rationalConjugateSL2Group N g).op := fun q =>
      ⟨MulOpposite.op q.out.val, q.out.property⟩
    have hterm : ∀ q : (rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g),
        realSL2Haar (QuotientGroup.mk ⁻¹' U ∩
          MulOpposite.op q.out.val • rationalConjugateSL2FundamentalSet N g) =
          realSL2Haar (QuotientGroup.mk ⁻¹' U ∩ rationalConjugateSL2FundamentalSet N g) := by
      intro q
      have hqR : (qR q).val = MulOpposite.op q.out.val := rfl
      rw [← hqR]
      exact measure_rationalConjugate_quotient_preimage_inter_translated_fundamentalSet
        N g U (qR q)
    simp_rw [hterm]
    simp only [tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    rfl
  · intro q₁ q₂ hne
    exact (rationalConjugateFiniteCoverFundamentalSet_aedisjoint N g hne).mono
      inter_subset_right inter_subset_right
  · intro q
    exact (hP.inter ((rationalConjugateSL2FundamentalSet_measurable N g).const_smul _)).nullMeasurableSet

/-- Projection from the integral common-cover quotient to the rational-conjugate quotient. -/
def rationalHeckeConjugateCoverProjection (N : ℕ) (g : GL (Fin 2) ℚ) :
    SL2R ⧸ rationalHeckeCommonCoverReal N g → SL2R ⧸ rationalConjugateSL2Group N g :=
  subgroupQuotientProjection _ _ (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)

theorem map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    Measure.map (rationalHeckeConjugateCoverProjection N g)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) =
      Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        rationalConjugateSL2QuotientMeasure N g := by
  let hKR : rationalHeckeCommonCoverReal N g ≤ rationalConjugateSL2Group N g :=
    realImage_rationalHeckeIntegralIntersection_le_conjugate N g
  let p := rationalHeckeConjugateCoverProjection N g
  let πK : SL2R → SL2R ⧸ rationalHeckeCommonCoverReal N g := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ rationalConjugateSL2Group N g := QuotientGroup.mk
  have hp : Measurable p := subgroupQuotientProjection_measurable _ _ hKR
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hcomp : p ∘ πK = πR := by
    funext x
    exact subgroupQuotientProjection_mk _ _ hKR x
  change Measure.map p
    (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) = _
  rw [integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g]
  calc
    Measure.map p (Measure.map πK
        (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g))) =
        Measure.map (p ∘ πK)
          (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g)) :=
      Measure.map_map hp hπK
    _ = Measure.map πR
          (realSL2Haar.restrict (rationalConjugateFiniteCoverFundamentalSet N g)) := by rw [hcomp]
    _ = Nat.card ((rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
          Measure.map πR (realSL2Haar.restrict (rationalConjugateSL2FundamentalSet N g)) :=
      map_restrict_rationalConjugateFiniteCoverFundamentalSet N g
    _ = Nat.card ((rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
          rationalConjugateSL2QuotientMeasure N g := by rfl

theorem eLpNorm_comp_rationalHeckeConjugateCoverProjection
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (N : ℕ) (g : GL (Fin 2) ℚ) (f : (SL2R ⧸ rationalConjugateSL2Group N g) → E)
    (p : ENNReal)
    (hf : AEStronglyMeasurable f
      (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        rationalConjugateSL2QuotientMeasure N g)) :
    eLpNorm (f ∘ rationalHeckeConjugateCoverProjection N g) p
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) =
      eLpNorm f p
        (Nat.card ((rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
          rationalConjugateSL2QuotientMeasure N g) := by
  let proj := rationalHeckeConjugateCoverProjection N g
  have hproj : Measurable proj := subgroupQuotientProjection_measurable _ _
    (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)
  have hmap : Measure.map proj
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) =
      Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        rationalConjugateSL2QuotientMeasure N g :=
    map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g
  have hfmap : AEStronglyMeasurable f (Measure.map proj
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) := by
    rw [hmap]
    exact hf
  exact (eLpNorm_map_measure hfmap hproj.aemeasurable).symm.trans (by rw [hmap])

theorem memLp_comp_rationalHeckeConjugateCoverProjection
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (N : ℕ) (g : GL (Fin 2) ℚ) (f : (SL2R ⧸ rationalConjugateSL2Group N g) → E)
    (p : ENNReal)
    (hf : MemLp f p (rationalConjugateSL2QuotientMeasure N g)) :
    MemLp (f ∘ rationalHeckeConjugateCoverProjection N g) p
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
  let proj := rationalHeckeConjugateCoverProjection N g
  have hproj : Measurable proj := subgroupQuotientProjection_measurable _ _
    (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)
  have hmap : Measure.map proj
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) =
      Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) •
        rationalConjugateSL2QuotientMeasure N g :=
    map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g
  apply MemLp.comp_of_map (hf := hproj.aemeasurable)
  rw [hmap]
  simpa only [Nat.cast_smul_eq_nsmul] using
    hf.smul_measure (c := (Nat.card ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)) : ENNReal))
      (by simp)

end

end GaloisForLFunctions.RHTower
