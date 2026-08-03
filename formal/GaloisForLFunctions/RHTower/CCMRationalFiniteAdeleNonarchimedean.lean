import GaloisForLFunctions.RHTower.CompactlySupportedLocallyConstantTranslationStabilizer
import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatReal

/-!
# Nonarchimedean topology of rational finite adeles

This file supplies the missing typeclass bridge needed to apply the global
translation-stabilizer law to the rational finite-adele Bruhat space.  The
construction is deliberately structural: valuation balls give open additive
subgroups in each completion, the property passes to valuation subrings and
arbitrary products, and the open integral-section embedding transfers it to
the restricted product.
-/

noncomputable section

open Filter Set Topology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GaloisForLFunctions
namespace RHTower

/-- A valued ring with its canonical topology is nonarchimedean.  This is
stated as a theorem rather than a global instance to avoid a topology diamond. -/
theorem nonarchimedeanRing_of_valued
    (R Γ₀ : Type*) [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued R Γ₀] : NonarchimedeanRing R := by
  refine { is_nonarchimedean := fun U hU => ?_ }
  obtain ⟨γ, -, hγ⟩ :=
    (Valued.hasBasis_nhds_zero R Γ₀).mem_iff.mp hU
  let v : Valuation R Γ₀ := Valued.v
  let H : AddSubgroup R :=
    v.ltAddSubgroup <|
      Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (.ofClass v))) γ
  have hEq : (H : Set R) = {x | v.restrict x < γ.1} := by
    ext x
    simp [H, Valuation.coe_ltAddSubgroup,
      Valuation.restrict_lt_iff_lt_embedding]
  have hH : (H : Set R) ∈ nhds (0 : R) := by
    apply (Valued.hasBasis_nhds_zero R Γ₀).mem_iff.mpr
    refine ⟨γ, trivial, ?_⟩
    rw [hEq]
  let V : OpenAddSubgroup R :=
    { toAddSubgroup := H
      isOpen' := H.isOpen_of_mem_nhds hH }
  exact ⟨V, hEq.trans_subset hγ⟩

/-- Arbitrary products of nonarchimedean additive groups are
nonarchimedean. -/
theorem nonarchimedeanAddGroup_pi
    {I : Type*} (G : I → Type*) [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, NonarchimedeanAddGroup (G i)] :
    NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨s, hs, n, hn, hsub⟩ := hU
    choose V hV using fun i =>
      NonarchimedeanAddGroup.is_nonarchimedean (n i) (hn i)
    let W : OpenAddSubgroup (∀ i, G i) :=
      { toAddSubgroup := AddSubgroup.pi s fun i => (V i).toAddSubgroup
        isOpen' := by
          change IsOpen (s.pi fun i => (V i : Set (G i)))
          exact isOpen_set_pi hs fun i _ => (V i).isOpen }
    refine ⟨W, fun x hx => hsub ?_⟩
    intro i hi
    exact hV i (hx i hi)

/-- Additive subgroups of nonarchimedean additive groups, with the subtype
topology, remain nonarchimedean. -/
theorem nonarchimedeanAddGroup_addSubgroup
    {G : Type*} [AddGroup G] [TopologicalSpace G]
    [NonarchimedeanAddGroup G] (H : AddSubgroup G) :
    NonarchimedeanAddGroup H where
  is_nonarchimedean U hU := by
    rw [Topology.IsInducing.subtypeVal.nhds_eq_comap,
      Filter.mem_comap] at hU
    obtain ⟨V, hV, hsub⟩ := hU
    obtain ⟨W, hW⟩ :=
      NonarchimedeanAddGroup.is_nonarchimedean V hV
    refine ⟨W.comap H.subtype continuous_subtype_val, fun x hx => ?_⟩
    exact hsub (hW hx)

/-- The additive topology of the rational finite-adele ring is
nonarchimedean. -/
theorem ccmRationalFiniteAdele_nonarchimedeanAddGroup :
    NonarchimedeanAddGroup CCMRationalFiniteAdele := by
  letI (v : HeightOneSpectrum ℤ) :
      NonarchimedeanRing (v.adicCompletion ℚ) :=
    nonarchimedeanRing_of_valued _ _
  letI (v : HeightOneSpectrum ℤ) :
      NonarchimedeanAddGroup (v.adicCompletionIntegers ℚ) :=
    nonarchimedeanAddGroup_addSubgroup
      (v.adicCompletionIntegers ℚ).toAddSubgroup
  letI : NonarchimedeanAddGroup
      (∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ) :=
    nonarchimedeanAddGroup_pi _
  let e :
      (∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ) →+
        CCMRationalFiniteAdele :=
    { toFun := RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
        (fun v : HeightOneSpectrum ℤ =>
          (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
        Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb
    e
    (RestrictedProduct.isOpenEmbedding_structureMap
      (fun v : HeightOneSpectrum ℤ =>
        Valued.isOpen_valuationSubring (v.adicCompletion ℚ)))

/-- Local instance used by finite-adele Bruhat arguments. -/
local instance : NonarchimedeanAddGroup CCMRationalFiniteAdele :=
  ccmRationalFiniteAdele_nonarchimedeanAddGroup

/-- Every rational finite-adele Bruhat function has a single global open
additive translation stabilizer. -/
theorem ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer
    (f : CCMRationalFiniteBruhatSchwartz) :
    ∃ V : OpenAddSubgroup CCMRationalFiniteAdele,
      ∀ x (v : V), f.1 (x + v.1) = f.1 x :=
  compactlySupportedLocallyConstant_exists_openAddSubgroup_stabilizer
    CCMRationalFiniteAdele ℂ f.1 f.1.isLocallyConstant f.2

end RHTower
end GaloisForLFunctions
