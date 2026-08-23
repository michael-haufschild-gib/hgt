import GaloisForLFunctions.RHTower.DeningerTestSigma

/-!
# Hasse assembly for test functions on disjoint local components

A compactly supported locally constant function on a disjoint union is determined by all component
restrictions.  Conversely, every finitely supported local profile glues to one unique global test
function.
-/

namespace RHTower

noncomputable section

universe u v

/-- Simultaneous restriction of a test function to every disjoint component. -/
def deningerTestSigmaRestrictionMap
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)] :
    DeningerTestSpace (Σ i, Y i) →ₗ[ℝ] (∀ i, DeningerTestSpace (Y i)) :=
  LinearMap.pi fun i => deningerTestRestrict i

/-- Simultaneous restriction to all disjoint components is faithful. -/
theorem deningerTestSigmaRestrictionMap_injective
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)] :
    Function.Injective (deningerTestSigmaRestrictionMap (Y := Y)) := by
  intro g h hgh
  apply deningerTestSigma_injective
  intro i
  exact congrFun hgh i

/-- Global test functions are linearly equivalent to the component-restriction profiles they
actually realize. -/
noncomputable def deningerTestSigmaRestrictionHasseEquivRange
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)] :
    DeningerTestSpace (Σ i, Y i) ≃ₗ[ℝ]
      LinearMap.range (deningerTestSigmaRestrictionMap (Y := Y)) :=
  LinearEquiv.ofBijective
    (LinearMap.rangeRestrict (deningerTestSigmaRestrictionMap (Y := Y)))
    ⟨fun _ _ h => deningerTestSigmaRestrictionMap_injective
        (Y := Y) (congrArg Subtype.val h),
      fun y => by
        obtain ⟨_, x, rfl⟩ := y
        exact ⟨x, rfl⟩⟩

/-- The realized-profile equivalence evaluates by simultaneous component restriction. -/
@[simp] theorem deningerTestSigmaRestrictionHasseEquivRange_apply
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    (g : DeningerTestSpace (Σ i, Y i)) :
    (deningerTestSigmaRestrictionHasseEquivRange (Y := Y) g).1 =
      deningerTestSigmaRestrictionMap (Y := Y) g := by
  rfl

/-- Two global test functions agree exactly when every component restriction agrees. -/
theorem deningerTestSigma_congr_hasse_iff
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    (g h : DeningerTestSpace (Σ i, Y i)) :
    (∀ i, deningerTestRestrict i g = deningerTestRestrict i h) ↔ g = h := by
  constructor
  · exact deningerTestSigma_injective
  · rintro rfl i
    rfl

/-- Local test-function profiles with finite nonzero support. -/
abbrev DeningerTestSigmaFiniteProfile
    {ι : Type u} (Y : ι → Type v)
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)] :=
  {F : ∀ i, DeningerTestSpace (Y i) // {i | F i ≠ 0}.Finite}

/-- Every finitely supported family of component test functions glues to one unique global test
function on the disjoint union. -/
theorem deningerTestSigma_existsUnique_hasse
    {ι : Type u} {Y : ι → Type v}
    [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    (F : DeningerTestSigmaFiniteProfile Y) :
    ∃! g : DeningerTestSpace (Σ i, Y i),
      ∀ i, deningerTestRestrict i g = F.1 i := by
  classical
  have hs : ∀ i ∉ F.2.toFinset, F.1 i = 0 := by
    intro i hi
    by_contra hne
    exact hi (F.2.mem_toFinset.mpr hne)
  obtain ⟨g, hg⟩ := deningerTestSigma_assemble F.1 F.2.toFinset hs
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply deningerTestSigma_injective
  intro i
  exact (hh i).trans (hg i).symm

end


end RHTower
