import GaloisForLFunctions.RHTower.Deninger.DeningerPadicTestSpace

/-!
# The test space of a disjoint union of compact components

A space decomposed into countably many compact open components — the shape of an adelic space
decomposed into its place components — has a test space assembled from the test spaces of the
components: a locally constant compactly supported function restricts to each component, only
finitely many restrictions are nonzero because the support is compact, the restrictions determine
the function, and any finitely supported family of test functions on the components assembles into
one on the union.

* `deningerTestRestrict` : restriction of a test function to a component.
* `deningerTestSigma_support_finite` : only finitely many restrictions are nonzero.
* `deningerTestSigma_injective` : the restrictions determine the function.
* `deningerTestSigma_assemble` : a finitely supported family assembles.
-/

namespace RHTower

section Sigma

variable {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]

/-- The restriction of a locally constant function to a component is locally constant. -/
theorem deningerSigmaRestrict_isLocallyConstant {f : (Σ i, Y i) → ℝ} (hf : IsLocallyConstant f)
    (i : ι) : IsLocallyConstant fun y : Y i => f ⟨i, y⟩ :=
  hf.comp_continuous continuous_sigmaMk

variable [∀ i, CompactSpace (Y i)]

/-- The restriction of a test function to a component is a test function. -/
theorem deningerSigmaRestrict_mem {f : (Σ i, Y i) → ℝ} (hf : f ∈ DeningerTestSpace (Σ i, Y i))
    (i : ι) : (fun y : Y i => f ⟨i, y⟩) ∈ DeningerTestSpace (Y i) := by
  refine ⟨deningerSigmaRestrict_isLocallyConstant hf.1 i, ?_⟩
  exact isCompact_univ.of_isClosed_subset
    (deningerSupport_isClosed (deningerSigmaRestrict_isLocallyConstant hf.1 i))
    (Set.subset_univ _)

/-- **The restriction of a test function to a component.** -/
noncomputable def deningerTestRestrict (i : ι) :
    DeningerTestSpace (Σ i, Y i) →ₗ[ℝ] DeningerTestSpace (Y i) where
  toFun g := ⟨fun y => (g : (Σ i, Y i) → ℝ) ⟨i, y⟩, deningerSigmaRestrict_mem g.2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem deningerTestRestrict_apply (i : ι) (g : DeningerTestSpace (Σ i, Y i)) (y : Y i) :
    ((deningerTestRestrict i g : DeningerTestSpace (Y i)) : Y i → ℝ) y
      = (g : (Σ i, Y i) → ℝ) ⟨i, y⟩ := rfl

/-- **A test function on a disjoint union has only finitely many nonzero restrictions**, its
support being compact and the components an open cover. -/
theorem deningerTestSigma_support_finite (g : DeningerTestSpace (Σ i, Y i)) :
    {i : ι | deningerTestRestrict i g ≠ 0}.Finite := by
  classical
  set f : (Σ i, Y i) → ℝ := (g : (Σ i, Y i) → ℝ) with hf
  have hK : IsCompact (Function.support f) := g.2.2
  have hcover : Function.support f ⊆ ⋃ i : ι, Sigma.mk i '' Set.univ := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x.1, ⟨x.2, Set.mem_univ _, rfl⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : ι => Sigma.mk i '' Set.univ)
    (fun i => isOpenMap_sigmaMk _ isOpen_univ) hcover
  refine Set.Finite.subset t.finite_toSet fun i hi => ?_
  by_contra hit
  refine hi ?_
  refine Subtype.ext (funext fun y => ?_)
  show f ⟨i, y⟩ = 0
  by_contra hne
  obtain ⟨j, hj, hmem⟩ := Set.mem_iUnion₂.mp (ht hne)
  obtain ⟨z, -, hz⟩ := hmem
  have : j = i := congrArg Sigma.fst hz
  exact hit (this ▸ hj)

/-- **The restrictions determine the function.** -/
theorem deningerTestSigma_injective {g h : DeningerTestSpace (Σ i, Y i)}
    (hgh : ∀ i, deningerTestRestrict i g = deningerTestRestrict i h) : g = h := by
  refine Subtype.ext (funext fun x => ?_)
  have := congrArg (fun w : DeningerTestSpace (Y x.1) => (w : Y x.1 → ℝ) x.2) (hgh x.1)
  simpa using this

/-- **A finitely supported family of test functions on the components assembles into a test
function on the disjoint union**, with the given restrictions. -/
theorem deningerTestSigma_assemble (F : ∀ i, DeningerTestSpace (Y i)) (s : Finset ι)
    (hs : ∀ i ∉ s, F i = 0) :
    ∃ g : DeningerTestSpace (Σ i, Y i), ∀ i, deningerTestRestrict i g = F i := by
  classical
  set f : (Σ i, Y i) → ℝ := fun x => (F x.1 : Y x.1 → ℝ) x.2 with hfdef
  have hlc : IsLocallyConstant f := by
    intro u
    rw [isOpen_sigma_iff]
    intro i
    have hpre : (fun y : Y i => f ⟨i, y⟩) ⁻¹' u = (F i : Y i → ℝ) ⁻¹' u := rfl
    rw [show Sigma.mk i ⁻¹' (f ⁻¹' u) = (fun y : Y i => f ⟨i, y⟩) ⁻¹' u from rfl, hpre]
    exact (F i).2.1 u
  have hsupp : Function.support f ⊆ ⋃ i ∈ s, Sigma.mk i '' Set.univ := by
    intro x hx
    have hne : (F x.1 : Y x.1 → ℝ) x.2 ≠ 0 := hx
    have hxs : x.1 ∈ s := by
      by_contra hns
      have : F x.1 = 0 := hs x.1 hns
      rw [this] at hne
      exact hne rfl
    exact Set.mem_biUnion hxs ⟨x.2, Set.mem_univ _, rfl⟩
  have hcompact : IsCompact (Function.support f) := by
    have hbig : IsCompact (⋃ i ∈ s, Sigma.mk i '' (Set.univ : Set (Y i))) :=
      s.finite_toSet.isCompact_biUnion fun i _ => isCompact_univ.image continuous_sigmaMk
    exact hbig.of_isClosed_subset (deningerSupport_isClosed hlc) hsupp
  exact ⟨⟨f, hlc, hcompact⟩, fun i => rfl⟩

end Sigma

end RHTower
