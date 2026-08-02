import GaloisForLFunctions.RHTower.DeningerFinestNuclear
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The locally constant test space of a second countable space is nuclear

Locally constant real functions with compact support form a subspace of all functions: the support
of a locally constant function is clopen, so the support of a sum is a closed subset of the union
of two compacts.

Such a function takes finitely many values on its support, and each nonzero level set is a compact
open set, so the function is a finite combination of indicators of compact open sets.  In a second
countable space every compact open set is a finite union of basic open sets, so the compact open
sets — and with them the indicators spanning the test space — form a countable family.  Extracting
a basis from that spanning family exhibits the test space as countable-dimensional, hence nuclear
for its finest locally convex topology, as is every subspace of it.

* `deningerCompactOpens_countable` : a second countable space has countably many compact opens.
* `DeningerTestSpace` : the locally constant compactly supported functions.
* `deningerTestIndicators_span` : the indicators of compact opens span it.
* `deningerTestSpace_isNuclearSpace` : **the test space is nuclear.**
* `deningerTestSubspace_isNuclearSpaceC` : so is every subspace of it, a closed subspace in
  particular.
-/

namespace RHTower

open TopologicalSpace

section CompactOpens

variable {Y : Type*} [TopologicalSpace Y]

/-- The compact open subsets of a space. -/
def deningerCompactOpens (Y : Type*) [TopologicalSpace Y] : Set (Set Y) :=
  {U | IsOpen U ∧ IsCompact U}

/-- **A second countable space has countably many compact open sets**, each being a finite union
of basic open sets. -/
theorem deningerCompactOpens_countable [SecondCountableTopology Y] :
    (deningerCompactOpens Y).Countable := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis Y
  have hfin : {t : Set (Set Y) | t.Finite ∧ t ⊆ B}.Countable :=
    Set.countable_setOf_finite_subset hBc
  refine Set.Countable.mono ?_ (hfin.image Set.sUnion)
  rintro U ⟨hUo, hUc⟩
  have hcover : U ⊆ ⋃ V ∈ {V ∈ B | V ⊆ U}, V := by
    intro x hx
    have hx' : x ∈ ⋃₀ {V ∈ B | V ⊆ U} := by
      rw [← hB.open_eq_sUnion' hUo]
      exact hx
    obtain ⟨V, hV, hxV⟩ := hx'
    exact Set.mem_biUnion hV hxV
  obtain ⟨t, hts, htfin, htcover⟩ :=
    hUc.elim_finite_subcover_image (fun V hV => hB.isOpen hV.1) hcover
  refine ⟨t, ⟨htfin, fun V hV => (hts hV).1⟩, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨V, hV, hxV⟩
    exact (hts hV).2 hxV
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (htcover hx)
    exact ⟨V, hV, hxV⟩

end CompactOpens

section TestSpace

variable {Y : Type*} [TopologicalSpace Y]

/-- **The support of a locally constant function is closed**, being the complement of the
preimage of zero. -/
theorem deningerSupport_isClosed {f : Y → ℝ} (hf : IsLocallyConstant f) :
    IsClosed (Function.support f) := by
  have hset : Function.support f = (f ⁻¹' {0})ᶜ := by
    ext x
    simp [Function.mem_support]
  rw [hset, isClosed_compl_iff]
  exact hf {0}

/-- **The locally constant test space**: real valued locally constant functions with compact
support. -/
def DeningerTestSpace (Y : Type*) [TopologicalSpace Y] : Submodule ℝ (Y → ℝ) where
  carrier := {f | IsLocallyConstant f ∧ IsCompact (Function.support f)}
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    refine ⟨hf.add hg, ?_⟩
    exact (hfc.union hgc).of_isClosed_subset (deningerSupport_isClosed (hf.add hg))
      (Function.support_add f g)
  zero_mem' := by
    refine ⟨IsLocallyConstant.const 0, ?_⟩
    simp
  smul_mem' := by
    rintro c f ⟨hf, hfc⟩
    have hsmul : IsLocallyConstant (c • f) := hf.comp fun y => c • y
    refine ⟨hsmul, ?_⟩
    exact hfc.of_isClosed_subset (deningerSupport_isClosed hsmul)
      (Function.support_const_smul_subset c f)

theorem deningerTestSpace_mem {f : Y → ℝ} :
    f ∈ DeningerTestSpace Y ↔ IsLocallyConstant f ∧ IsCompact (Function.support f) := Iff.rfl

/-- **The indicator of a clopen set is locally constant**: every preimage is one of the four
clopen sets `∅`, `U`, `Uᶜ`, `univ`. -/
theorem deningerIndicator_isLocallyConstant {U : Set Y} (hUo : IsOpen U) (hUc : IsClosed U) :
    IsLocallyConstant (Set.indicator U (1 : Y → ℝ)) := by
  intro s
  by_cases h1 : (1 : ℝ) ∈ s
  · by_cases h0 : (0 : ℝ) ∈ s
    · have : Set.indicator U (1 : Y → ℝ) ⁻¹' s = Set.univ := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, h0, h1]
      rw [this]
      exact isOpen_univ
    · have : Set.indicator U (1 : Y → ℝ) ⁻¹' s = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, h0, h1]
      rw [this]
      exact hUo
  · by_cases h0 : (0 : ℝ) ∈ s
    · have : Set.indicator U (1 : Y → ℝ) ⁻¹' s = Uᶜ := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, h0, h1]
      rw [this]
      exact hUc.isOpen_compl
    · have : Set.indicator U (1 : Y → ℝ) ⁻¹' s = ∅ := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, h0, h1]
      rw [this]
      exact isOpen_empty

omit [TopologicalSpace Y] in
theorem deningerIndicator_support (U : Set Y) :
    Function.support (Set.indicator U (1 : Y → ℝ)) = U := by
  ext x
  by_cases hx : x ∈ U <;> simp [hx]

theorem deningerIndicator_mem [T2Space Y] {U : Set Y} (hU : U ∈ deningerCompactOpens Y) :
    Set.indicator U (1 : Y → ℝ) ∈ DeningerTestSpace Y := by
  refine ⟨deningerIndicator_isLocallyConstant hU.1 hU.2.isClosed, ?_⟩
  rw [deningerIndicator_support]
  exact hU.2

/-- The indicators of compact open sets, as elements of the test space. -/
def deningerTestIndicators (Y : Type*) [TopologicalSpace Y] : Set (DeningerTestSpace Y) :=
  {g | ∃ U ∈ deningerCompactOpens Y, (g : Y → ℝ) = Set.indicator U 1}

theorem deningerTestIndicators_countable [SecondCountableTopology Y] :
    (deningerTestIndicators Y).Countable := by
  have h1 : ((fun U => Set.indicator U (1 : Y → ℝ)) '' deningerCompactOpens Y).Countable :=
    deningerCompactOpens_countable.image _
  refine Set.Countable.mono ?_ (h1.preimage Subtype.val_injective)
  rintro g ⟨U, hU, hg⟩
  exact ⟨U, hU, hg.symm⟩

/-- **A locally constant function with compact support takes finitely many values.** -/
theorem deningerTestSpace_range_finite {f : Y → ℝ} (hf : IsLocallyConstant f)
    (hK : IsCompact (Function.support f)) : (Set.range f).Finite := by
  haveI : CompactSpace (Function.support f) := isCompact_iff_compactSpace.mp hK
  have hres : IsLocallyConstant fun x : Function.support f => f x :=
    hf.comp_continuous continuous_subtype_val
  have hsub : Set.range f ⊆ insert 0 (Set.range fun x : Function.support f => f x) := by
    rintro c ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Set.mem_insert_iff.mpr (Or.inl hx)
    · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  exact Set.Finite.subset (hres.range_finite.insert 0) hsub

/-- **The indicators of compact open sets span the test space.**  A test function is the sum over
its finitely many nonzero values of that value times the indicator of the corresponding level set,
which is compact and open. -/
theorem deningerTestIndicators_span [T2Space Y] :
    Submodule.span ℝ (deningerTestIndicators Y) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun g => ?_
  obtain ⟨hf, hK⟩ := g.2
  set f : Y → ℝ := (g : Y → ℝ) with hfdef
  have hrange := deningerTestSpace_range_finite hf hK
  set V : Finset ℝ := hrange.toFinset.erase 0 with hV
  have hlevel : ∀ c ∈ V, f ⁻¹' {c} ∈ deningerCompactOpens Y := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    refine ⟨hf {c}, ?_⟩
    refine hK.of_isClosed_subset ?_ ?_
    · have : IsClosed (f ⁻¹' {c}) := by
        have hcompl : (f ⁻¹' {c})ᶜ = f ⁻¹' {c}ᶜ := by
          ext x
          simp
        rw [← isOpen_compl_iff, hcompl]
        exact hf _
      exact this
    · intro x hx
      have hfx : f x = c := hx
      exact fun hzero => hc0 (by rw [← hfx, hzero])
  have hmem : ∀ c ∈ V, Set.indicator (f ⁻¹' {c}) (1 : Y → ℝ) ∈ DeningerTestSpace Y :=
    fun c hc => deningerIndicator_mem (hlevel c hc)
  have hsum : f = ∑ c ∈ V, c • Set.indicator (f ⁻¹' {c}) (1 : Y → ℝ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · have hzero : ∀ c ∈ V, (c • Set.indicator (f ⁻¹' {c}) (1 : Y → ℝ)) x = 0 := by
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
  set E : ℝ → DeningerTestSpace Y := fun c =>
    if h : Set.indicator (f ⁻¹' {c}) (1 : Y → ℝ) ∈ DeningerTestSpace Y then ⟨_, h⟩ else 0
    with hEdef
  have hEcoe : ∀ c ∈ V, (E c : Y → ℝ) = Set.indicator (f ⁻¹' {c}) 1 := by
    intro c hc
    rw [hEdef]
    simp only [dif_pos (hmem c hc)]
  have hEmem : ∀ c ∈ V, E c ∈ deningerTestIndicators Y := by
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

/-- **The locally constant test space is nuclear** for its finest locally convex topology: the
countably many indicators of compact open sets span it, and a basis extracted from them is
countable. -/
theorem deningerTestSpace_isNuclearSpace [T2Space Y] [SecondCountableTopology Y] :
    DeningerIsNuclearSpace (fun p : Seminorm ℝ (DeningerTestSpace Y) => p) := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (deningerTestIndicators Y)
  haveI : Countable b := (deningerTestIndicators_countable.mono hbS).to_subtype
  refine deningerIsNuclearSpace_finest_of_countable (Module.Basis.mk hli ?_)
  rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, deningerTestIndicators_span]

/-- **Every subspace of the locally constant test space is nuclear**, a closed subspace such as
the closure of a distinguished family of test functions in particular. -/
theorem deningerTestSubspace_isNuclearSpaceC [T2Space Y] [SecondCountableTopology Y]
    (F : Submodule ℝ (DeningerTestSpace Y)) :
    DeningerIsNuclearSpaceC
      (fun p : Seminorm ℝ (DeningerTestSpace Y) => deningerRestrictSeminorm F p) :=
  deningerIsNuclearSpaceC_subspace _ F deningerTestSpace_isNuclearSpace

end TestSpace

end RHTower
