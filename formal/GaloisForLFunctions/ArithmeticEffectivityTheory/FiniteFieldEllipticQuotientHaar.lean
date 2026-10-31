import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdditiveDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The normalized additive quotient of the elliptic adeles

The affine simple-pole gap gives a compact open additive domain. It and the
full integral product each have three cosets of the same open subgroup, so
the quotient inherits Haar probability with the actual adelic normalization.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory Set
open scoped WithZero WithZeroMulInt
noncomputable section

/-- The common subgroup below the constant and simple-pole residue layers. -/
def ellipticSmallDomain : AddSubgroup Adeles := finiteIntegral.prod infinitySmall

/-- The actual diagonal function field as an additive subgroup. -/
def diagonalAdeles : AddSubgroup Adeles := adeleEmbedding.toAddMonoidHom.range

/-- The additive adelic quotient of the elliptic function field. -/
abbrev AdditiveQuotient := Adeles ⧸ diagonalAdeles

/-- Constant or simple-pole translation at the infinity coordinate. -/
def infinityAdele (f : Constants →+ InfinityCompletion) : Constants →+ Adeles where
  toFun c := (0, f c)
  map_zero' := by simp only [map_zero]; rfl
  map_add' c d := by
    change (0, f (c + d)) = (0 + 0, f c + f d)
    rw [zero_add, map_add]

private theorem infinityGap_eq_iUnion_preimage :
    (infinityGap : Set InfinityCompletion) =
      ⋃ c : Constants, (fun z => z - infinitySimplePole c) ⁻¹' (infinitySmall : Set _) := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_preimage]
  rfl

private theorem infinityGap_eq_iUnion_image :
    (infinityGap : Set InfinityCompletion) =
      ⋃ c : Constants, (fun z => infinitySimplePole c + z) '' (infinitySmall : Set _) := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, z - infinitySimplePole c, hc, by abel⟩
  · rintro ⟨c, w, hw, rfl⟩
    refine ⟨c, ?_⟩
    change infinitySimplePole c + w - infinitySimplePole c ∈ (infinitySmall : Set _)
    rw [add_sub_cancel_left]
    exact hw

private theorem ellipticAdditiveDomain_eq_iUnion :
    (ellipticAdditiveDomain : Set Adeles) =
      ⋃ c : Constants,
        (fun a => a - infinityAdele infinitySimplePole c) ⁻¹' (ellipticSmallDomain : Set _) := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_preimage]
  change (a.1 ∈ finiteIntegral ∧ ∃ c, a.2 - infinitySimplePole c ∈ infinitySmall) ↔
    ∃ c, a.1 - 0 ∈ finiteIntegral ∧ a.2 - infinitySimplePole c ∈ infinitySmall
  simp only [sub_zero]
  constructor
  · rintro ⟨ha, c, hc⟩
    exact ⟨c, ha, hc⟩
  · rintro ⟨c, ha, hc⟩
    exact ⟨ha, c, hc⟩

private theorem integralAdeles_eq_iUnion :
    integralAdeles = ⋃ c : Constants,
      (fun a => a - infinityAdele infinityConstant c) ⁻¹' (ellipticSmallDomain : Set _) := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_preimage]
  change (a.1 ∈ finiteIntegral ∧ Valued.v a.2 ≤ 1) ↔
    ∃ c, a.1 - 0 ∈ finiteIntegral ∧ Valued.v (a.2 - infinityConstant c) < 1
  rw [sub_zero]
  constructor
  · rintro ⟨ha, hz⟩
    obtain ⟨c, hc⟩ := completedInfinity_sub_constant a.2 hz
    exact ⟨c, ha, hc⟩
  · rintro ⟨c, ha, hc⟩
    refine ⟨ha, ?_⟩
    have hv : Valued.v (infinityConstant c) ≤ 1 := by
      by_cases hcz : c = 0
      · simp only [hcz, map_zero]; exact zero_le_one
      · exact (completedInfinity_constant_valuation c hcz).le
    calc
      Valued.v a.2 = Valued.v ((a.2 - infinityConstant c) + infinityConstant c) := by
        rw [sub_add_cancel]
      _ ≤ max (Valued.v (a.2 - infinityConstant c)) (Valued.v (infinityConstant c)) :=
        Valued.v.map_add _ _
      _ ≤ 1 := max_le hc.le hv

theorem infinitySmall_isOpen : IsOpen (infinitySmall : Set InfinityCompletion) := by
  change IsOpen {z : InfinityCompletion | Valued.v z < (1 : ℤᵐ⁰)}
  simpa only [Valuation.restrict_lt_one_iff] using Valued.isOpen_ball InfinityCompletion 1

theorem infinitySmall_isClosed : IsClosed (infinitySmall : Set InfinityCompletion) := by
  change IsClosed {z : InfinityCompletion | Valued.v z < (1 : ℤᵐ⁰)}
  simpa only [Valuation.restrict_lt_one_iff] using Valued.isClosed_ball InfinityCompletion 1

theorem infinitySmall_isCompact : IsCompact (infinitySmall : Set InfinityCompletion) := by
  have hi : IsCompact
      ((Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer : Set InfinityCompletion) :=
    isCompact_iff_compactSpace.mpr
      (HTGeometry.DiscreteValuedCompletion.completedIntegerCompact (WithVal infinityValuation))
  exact hi.of_isClosed_subset infinitySmall_isClosed fun z hz =>
    show Valued.v z ≤ 1 from (show Valued.v z < 1 from hz).le

theorem infinityGap_isOpen : IsOpen (infinityGap : Set InfinityCompletion) := by
  rw [infinityGap_eq_iUnion_preimage]
  exact isOpen_iUnion fun c =>
    infinitySmall_isOpen.preimage (continuous_id.sub continuous_const)

theorem infinityGap_isCompact : IsCompact (infinityGap : Set InfinityCompletion) := by
  rw [infinityGap_eq_iUnion_image]
  exact isCompact_iUnion fun c =>
    infinitySmall_isCompact.image (continuous_const.add continuous_id)

theorem ellipticAdditiveDomain_isOpen : IsOpen (ellipticAdditiveDomain : Set Adeles) :=
  integralFiniteAdeles_isOpen.prod infinityGap_isOpen

theorem ellipticAdditiveDomain_isCompact : IsCompact (ellipticAdditiveDomain : Set Adeles) :=
  integralFiniteAdeles_isCompact.prod infinityGap_isCompact

theorem ellipticSmallDomain_isOpen : IsOpen (ellipticSmallDomain : Set Adeles) :=
  integralFiniteAdeles_isOpen.prod infinitySmall_isOpen

private theorem infinityConstant_mem_small_eq_zero {c : Constants}
    (hc : infinityConstant c ∈ infinitySmall) : c = 0 := by
  by_contra hcz
  change Valued.v (infinityConstant c) < 1 at hc
  rw [show Valued.v (infinityConstant c) = 1 from
    completedInfinity_constant_valuation c hcz] at hc
  exact (lt_irrefl _ hc).elim

private theorem infinitySimplePole_mem_small_eq_zero {c : Constants}
    (hc : infinitySimplePole c ∈ infinitySmall) : c = 0 := by
  by_contra hcz
  change Valued.v (infinitySimplePole c) < 1 at hc
  rw [infinitySimplePole_valuation hcz] at hc
  have hh : WithZero.exp (1 : ℤ) < WithZero.exp (0 : ℤ) := hc
  have := WithZero.exp_lt_exp.mp hh
  omega

private theorem infinityAdele_cosets_pairwise
    (f : Constants →+ InfinityCompletion)
    (hf : ∀ c, f c ∈ infinitySmall → c = 0) :
    Pairwise (fun c d : Constants => Disjoint
      ((fun a => a - infinityAdele f c) ⁻¹' (ellipticSmallDomain : Set Adeles))
      ((fun a => a - infinityAdele f d) ⁻¹' (ellipticSmallDomain : Set Adeles))) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro a hac had
  have hdiff : (a.2 - f d) - (a.2 - f c) ∈ infinitySmall :=
    infinitySmall.sub_mem had.2 hac.2
  have heq : (a.2 - f d) - (a.2 - f c) = f (c - d) := by rw [map_sub]; abel
  rw [heq] at hdiff
  exact hcd (sub_eq_zero.mp (hf _ hdiff))

local instance : MeasurableAdd Adeles := ContinuousAdd.measurableAdd

private theorem adeleHaar_infinityAdele_coset
    (f : Constants →+ InfinityCompletion) (c : Constants) :
    adeleHaar ((fun a => a - infinityAdele f c) ⁻¹' (ellipticSmallDomain : Set Adeles)) =
      adeleHaar (ellipticSmallDomain : Set Adeles) := by
  simpa only [sub_eq_add_neg, add_comm] using
    measure_preimage_add adeleHaar (-(infinityAdele f c)) (ellipticSmallDomain : Set Adeles)

/-- The simple-pole domain has the same volume as the full local integer product. -/
theorem adeleHaar_ellipticAdditiveDomain :
    adeleHaar (ellipticAdditiveDomain : Set Adeles) = 1 := by
  have hm (f : Constants →+ InfinityCompletion) (c : Constants) :
      MeasurableSet ((fun a => a - infinityAdele f c) ⁻¹'
        (ellipticSmallDomain : Set Adeles)) :=
    (ellipticSmallDomain_isOpen.preimage (continuous_id.sub continuous_const)).measurableSet
  have hgap := measure_iUnion (μ := adeleHaar)
    (infinityAdele_cosets_pairwise infinitySimplePole
      (fun _ => infinitySimplePole_mem_small_eq_zero)) (hm infinitySimplePole)
  have hint := measure_iUnion (μ := adeleHaar)
    (infinityAdele_cosets_pairwise infinityConstant
      (fun _ => infinityConstant_mem_small_eq_zero)) (hm infinityConstant)
  rw [← ellipticAdditiveDomain_eq_iUnion] at hgap
  rw [← integralAdeles_eq_iUnion, adeleHaar_integralAdeles] at hint
  simp only [adeleHaar_infinityAdele_coset] at hgap hint
  exact hgap.trans hint.symm

/-- The quotient map restricted to the explicit additive domain. -/
def domainToAdditiveQuotient : ellipticAdditiveDomain →+ AdditiveQuotient :=
  (QuotientAddGroup.mk' diagonalAdeles).comp ellipticAdditiveDomain.subtype

theorem domainToAdditiveQuotient_injective : Function.Injective domainToAdditiveQuotient := by
  intro d e h
  change ((d : Adeles) : AdditiveQuotient) = ((e : Adeles) : AdditiveQuotient) at h
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.mp h
  change adeleEmbedding z = -(d : Adeles) + (e : Adeles) at hz
  have hzD : adeleEmbedding z ∈ ellipticAdditiveDomain := by
    rw [hz]
    exact ellipticAdditiveDomain.add_mem (ellipticAdditiveDomain.neg_mem d.property) e.property
  have hz0 := adeleEmbedding_mem_gap_eq_zero hzD
  have heq : -(d : Adeles) + (e : Adeles) = 0 := by
    rw [← hz, hz0, map_zero]
  apply Subtype.ext
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, add_comm] using heq)).symm

theorem domainToAdditiveQuotient_surjective : Function.Surjective domainToAdditiveQuotient := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨z, hz⟩ := adele_exists_gap_representative a
  refine ⟨⟨a - adeleEmbedding z, hz⟩, ?_⟩
  apply QuotientAddGroup.eq.mpr
  exact ⟨z, by change adeleEmbedding z = -(a - adeleEmbedding z) + a; abel⟩

theorem continuous_domainToAdditiveQuotient : Continuous domainToAdditiveQuotient :=
  QuotientAddGroup.continuous_mk.comp continuous_subtype_val

theorem isOpenMap_domainToAdditiveQuotient : IsOpenMap domainToAdditiveQuotient :=
  QuotientAddGroup.isOpenMap_coe.comp ellipticAdditiveDomain_isOpen.isOpenMap_subtype_val

/-- The actual gap domain is additively isomorphic to the full adelic quotient. -/
def additiveQuotientEquiv : ellipticAdditiveDomain ≃+ AdditiveQuotient :=
  AddEquiv.ofBijective domainToAdditiveQuotient
    ⟨domainToAdditiveQuotient_injective, domainToAdditiveQuotient_surjective⟩

/-- The additive quotient is precisely the compact open gap domain topologically. -/
def additiveQuotientHomeomorph : ellipticAdditiveDomain ≃ₜ AdditiveQuotient :=
  additiveQuotientEquiv.toEquiv.toHomeomorphOfContinuousOpen
    continuous_domainToAdditiveQuotient isOpenMap_domainToAdditiveQuotient

instance ellipticAdditiveDomain_compact : CompactSpace ellipticAdditiveDomain :=
  isCompact_iff_compactSpace.mp ellipticAdditiveDomain_isCompact

instance additiveQuotient_compact : CompactSpace AdditiveQuotient :=
  additiveQuotientHomeomorph.compactSpace

instance additiveQuotient_t2 : T2Space AdditiveQuotient := additiveQuotientHomeomorph.t2Space
instance additiveQuotient_measurableSpace : MeasurableSpace AdditiveQuotient := borel _
instance additiveQuotient_borelSpace : BorelSpace AdditiveQuotient := ⟨rfl⟩

/-- Ambient Haar measure on the actual compact open domain. -/
def ellipticDomainHaar : Measure ellipticAdditiveDomain :=
  adeleHaar.comap ellipticAdditiveDomain.subtype

instance ellipticDomainHaar_isAddHaar : ellipticDomainHaar.IsAddHaarMeasure := by
  unfold ellipticDomainHaar
  exact Measure.IsAddHaarMeasure.comap (mH := inferInstance) adeleHaar
    ellipticAdditiveDomain_isOpen.isOpenEmbedding_subtypeVal

theorem ellipticDomainHaar_univ : ellipticDomainHaar Set.univ = 1 := by
  have hm := ellipticAdditiveDomain_isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  change (Measure.comap (Subtype.val : ellipticAdditiveDomain → Adeles) adeleHaar) Set.univ = 1
  have heq : (Subtype.val : ellipticAdditiveDomain → Adeles) '' Set.univ =
      (ellipticAdditiveDomain : Set Adeles) := by
    ext a
    constructor
    · rintro ⟨b, _, rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a, ha⟩, Set.mem_univ _, rfl⟩
  calc
    _ = adeleHaar ((Subtype.val : ellipticAdditiveDomain → Adeles) '' Set.univ) :=
      Measure.comap_apply (Subtype.val : ellipticAdditiveDomain → Adeles)
        Subtype.coe_injective (fun s hs => hm.measurableSet_image.mpr hs)
        adeleHaar MeasurableSet.univ
    _ = 1 := by rw [heq, adeleHaar_ellipticAdditiveDomain]

instance ellipticDomainHaar_isProbability : IsProbabilityMeasure ellipticDomainHaar :=
  ⟨ellipticDomainHaar_univ⟩

/-- Haar probability on the actual additive quotient, with ambient covolume one. -/
def additiveQuotientHaar : Measure AdditiveQuotient :=
  Measure.map domainToAdditiveQuotient ellipticDomainHaar

instance additiveQuotientHaar_isAddHaar : additiveQuotientHaar.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_map_of_isFiniteMeasure ellipticDomainHaar
    domainToAdditiveQuotient continuous_domainToAdditiveQuotient domainToAdditiveQuotient_surjective

instance additiveQuotientHaar_isProbability : IsProbabilityMeasure additiveQuotientHaar := by
  constructor
  rw [additiveQuotientHaar, Measure.map_apply continuous_domainToAdditiveQuotient.measurable
    MeasurableSet.univ, Set.preimage_univ, ellipticDomainHaar_univ]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleHaar_ellipticAdditiveDomain
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.additiveQuotientHomeomorph
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.additiveQuotientHaar_isAddHaar
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.additiveQuotientHaar_isProbability
