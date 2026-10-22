import GaloisForLFunctions.RHTower.Deninger.DeningerFinestSubspaceNuclear

/-!
# The complex valued locally constant test space

The same construction as for real valued test functions, with complex scalars: locally constant
compactly supported complex functions form a space spanned by the indicators of the compact open
sets, which are countably many, so the space has countable rank and is nuclear for its finest
locally convex topology, as is every subspace of it.

Complex scalars are what a tensor product with a space of complex valued smooth functions needs.

* `DeningerTestSpaceC` : the complex valued test space.
* `deningerTestIndicatorsC_span` : the indicators of compact opens span it.
* `deningerTestSpaceC_isNuclearSpace`, `deningerTestSubspaceC_isNuclearSpace` : **it and all its
  subspaces are nuclear.**
-/

namespace RHTower

section ComplexTestSpace

variable {Y : Type*} [TopologicalSpace Y]

/-- **The complex valued locally constant test space.** -/
def DeningerTestSpaceC (Y : Type*) [TopologicalSpace Y] : Submodule ℂ (Y → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ IsCompact (Function.support f)}
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    refine ⟨hf.add hg, ?_⟩
    have hclosed : IsClosed (Function.support (f + g)) := by
      have hset : Function.support (f + g) = ((f + g) ⁻¹' {0})ᶜ := by
        ext x
        simp [Function.mem_support]
      rw [hset, isClosed_compl_iff]
      exact (hf.add hg) {0}
    exact (hfc.union hgc).of_isClosed_subset hclosed (Function.support_add f g)
  zero_mem' := by
    refine ⟨IsLocallyConstant.const 0, ?_⟩
    simp
  smul_mem' := by
    rintro c f ⟨hf, hfc⟩
    have hsmul : IsLocallyConstant (c • f) := hf.comp fun y => c • y
    have hclosed : IsClosed (Function.support (c • f)) := by
      have hset : Function.support (c • f) = ((c • f) ⁻¹' {0})ᶜ := by
        ext x
        simp [Function.mem_support]
      rw [hset, isClosed_compl_iff]
      exact hsmul {0}
    exact ⟨hsmul, hfc.of_isClosed_subset hclosed (Function.support_const_smul_subset c f)⟩

theorem deningerIndicatorC_mem [T2Space Y] {U : Set Y} (hU : U ∈ deningerCompactOpens Y) :
    Set.indicator U (1 : Y → ℂ) ∈ DeningerTestSpaceC Y := by
  refine ⟨?_, ?_⟩
  · intro s
    have hUc : IsClosed U := hU.2.isClosed
    by_cases h1 : (1 : ℂ) ∈ s
    · by_cases h0 : (0 : ℂ) ∈ s
      · have hset : Set.indicator U (1 : Y → ℂ) ⁻¹' s = Set.univ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h0, h1]
        rw [hset]
        exact isOpen_univ
      · have hset : Set.indicator U (1 : Y → ℂ) ⁻¹' s = U := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h0, h1]
        rw [hset]
        exact hU.1
    · by_cases h0 : (0 : ℂ) ∈ s
      · have hset : Set.indicator U (1 : Y → ℂ) ⁻¹' s = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h0, h1]
        rw [hset]
        exact hUc.isOpen_compl
      · have hset : Set.indicator U (1 : Y → ℂ) ⁻¹' s = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h0, h1]
        rw [hset]
        exact isOpen_empty
  · have hsupp : Function.support (Set.indicator U (1 : Y → ℂ)) = U := by
      ext x
      by_cases hx : x ∈ U <;> simp [hx]
    rw [hsupp]
    exact hU.2

/-- The indicators of compact open sets, as complex test functions. -/
def deningerTestIndicatorsC (Y : Type*) [TopologicalSpace Y] : Set (DeningerTestSpaceC Y) :=
  {g | ∃ U ∈ deningerCompactOpens Y, (g : Y → ℂ) = Set.indicator U 1}

theorem deningerTestIndicatorsC_countable [SecondCountableTopology Y] :
    (deningerTestIndicatorsC Y).Countable := by
  have h1 : ((fun U => Set.indicator U (1 : Y → ℂ)) '' deningerCompactOpens Y).Countable :=
    deningerCompactOpens_countable.image _
  refine Set.Countable.mono ?_ (h1.preimage Subtype.val_injective)
  rintro g ⟨U, hU, hg⟩
  exact ⟨U, hU, hg.symm⟩

/-- **The indicators of compact open sets span the complex test space.** -/
theorem deningerTestIndicatorsC_span [T2Space Y] :
    Submodule.span ℂ (deningerTestIndicatorsC Y) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun g => ?_
  obtain ⟨hf, hK⟩ := g.2
  set f : Y → ℂ := (g : Y → ℂ) with hfdef
  have hrange : (Set.range f).Finite := by
    haveI : CompactSpace (Function.support f) := isCompact_iff_compactSpace.mp hK
    have hres : IsLocallyConstant fun x : Function.support f => f x :=
      hf.comp_continuous continuous_subtype_val
    have hsub : Set.range f ⊆ insert 0 (Set.range fun x : Function.support f => f x) := by
      rintro c ⟨x, rfl⟩
      by_cases hx : f x = 0
      · exact Set.mem_insert_iff.mpr (Or.inl hx)
      · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    exact Set.Finite.subset (hres.range_finite.insert 0) hsub
  set V : Finset ℂ := hrange.toFinset.erase 0 with hV
  have hlevel : ∀ c ∈ V, f ⁻¹' {c} ∈ deningerCompactOpens Y := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    refine ⟨hf {c}, ?_⟩
    refine hK.of_isClosed_subset ?_ ?_
    · have hcompl : (f ⁻¹' {c})ᶜ = f ⁻¹' {c}ᶜ := by
        ext x
        simp
      rw [← isOpen_compl_iff, hcompl]
      exact hf _
    · intro x hx
      have hfx : f x = c := hx
      exact fun hzero => hc0 (by rw [← hfx, hzero])
  have hmem : ∀ c ∈ V, Set.indicator (f ⁻¹' {c}) (1 : Y → ℂ) ∈ DeningerTestSpaceC Y :=
    fun c hc => deningerIndicatorC_mem (hlevel c hc)
  have hsum : f = ∑ c ∈ V, c • Set.indicator (f ⁻¹' {c}) (1 : Y → ℂ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · have hzero : ∀ c ∈ V, (c • Set.indicator (f ⁻¹' {c}) (1 : Y → ℂ)) x = 0 := by
        intro c hc
        have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
        have hxc : x ∉ f ⁻¹' {c} := fun hmem' => hc0 (by rw [← (hmem' : f x = c), hx])
        simp [hxc]
      rw [Finset.sum_eq_zero hzero]
      exact hx
    · have hxV : f x ∈ V := by
        refine Finset.mem_erase.mpr ⟨hx, ?_⟩
        exact hrange.mem_toFinset.mpr ⟨x, rfl⟩
      rw [Finset.sum_eq_single (f x)]
      · have hxmem : x ∈ f ⁻¹' {f x} := rfl
        simp [hxmem]
      · intro c _ hcne
        have hxc : x ∉ f ⁻¹' {c} := fun hmem' => hcne (by rw [← (hmem' : f x = c)])
        simp [hxc]
      · intro hxV'
        exact absurd hxV hxV'
  set E : ℂ → DeningerTestSpaceC Y := fun c =>
    if h : Set.indicator (f ⁻¹' {c}) (1 : Y → ℂ) ∈ DeningerTestSpaceC Y then ⟨_, h⟩ else 0
    with hEdef
  have hEcoe : ∀ c ∈ V, (E c : Y → ℂ) = Set.indicator (f ⁻¹' {c}) 1 := by
    intro c hc
    rw [hEdef]
    simp only [dif_pos (hmem c hc)]
  have hEmem : ∀ c ∈ V, E c ∈ deningerTestIndicatorsC Y := by
    intro c hc
    exact ⟨f ⁻¹' {c}, hlevel c hc, hEcoe c hc⟩
  have hgsum : g = ∑ c ∈ V, c • E c := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum, ← hfdef]
    refine hsum.trans (Finset.sum_congr rfl fun c hc => ?_)
    rw [Submodule.coe_smul, hEcoe c hc]
  rw [hgsum]
  refine Submodule.sum_mem _ fun c hc => ?_
  exact Submodule.smul_mem _ c (Submodule.subset_span (hEmem c hc))

variable [T2Space Y] [SecondCountableTopology Y]

theorem deningerTestSpaceC_rank_le : Module.rank ℂ (DeningerTestSpaceC Y) ≤ Cardinal.aleph0 := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ (deningerTestIndicatorsC Y)
  haveI : Countable b := (deningerTestIndicatorsC_countable.mono hbS).to_subtype
  have hbasis : Module.Basis b ℂ (DeningerTestSpaceC Y) := by
    refine Module.Basis.mk hli ?_
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, deningerTestIndicatorsC_span]
  rw [← hbasis.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0_iff.mpr ‹Countable b›

/-- **The complex test space is nuclear.** -/
theorem deningerTestSpaceC_isNuclearSpace :
    DeningerIsNuclearSpace (fun p : Seminorm ℂ (DeningerTestSpaceC Y) => p) := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ (deningerTestIndicatorsC Y)
  haveI : Countable b := (deningerTestIndicatorsC_countable.mono hbS).to_subtype
  refine deningerIsNuclearSpace_finest_of_countable (Module.Basis.mk hli ?_)
  rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, deningerTestIndicatorsC_span]

/-- **Every subspace of the complex test space is nuclear.** -/
theorem deningerTestSubspaceC_isNuclearSpace (F : Submodule ℂ (DeningerTestSpaceC Y)) :
    DeningerIsNuclearSpace
      (fun p : Seminorm ℂ (DeningerTestSpaceC Y) => deningerRestrictSeminorm F p) :=
  deningerIsNuclearSpace_finest_subspace deningerTestSpaceC_rank_le F

end ComplexTestSpace

end RHTower
