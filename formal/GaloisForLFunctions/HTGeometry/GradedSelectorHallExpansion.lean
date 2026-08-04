import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DFinsupp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped DirectSum

/-- Collision-free graded injective selectors cannot shrink a resolved
subspace. Each source grade may choose a different operator from the family;
injectivity of the target-grade selector makes all chosen images assemble
without cancellation. -/
theorem gradedInjectiveSelector_subspace_finrank
    {K X G J : Type*}
    [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [Fintype G]
    (A : J → X →ₗ[K] X)
    (grades source : G → Submodule K X)
    (U : Submodule K X)
    (selector : G → J) (target : G → G)
    (hgrades : iSupIndep grades)
    (hsourceU : ∀ g, source g ≤ U)
    (hUrank : Module.finrank K U = ∑ g, Module.finrank K (source g))
    (htarget : Function.Injective target)
    (hmap : ∀ g, (source g).map (A (selector g)) ≤ grades (target g))
    (hinjective : ∀ g,
      Function.Injective ((A (selector g)).domRestrict (source g))) :
    Module.finrank K U ≤ Module.finrank K (linearFamilyShadow A U) := by
  classical
  let imageGrade : G → Submodule K X := fun g =>
    (source g).map (A (selector g))
  have himageIndep : iSupIndep imageGrade := by
    apply (hgrades.comp htarget).mono
    intro g
    exact hmap g
  have himageShadow : ∀ g, imageGrade g ≤ linearFamilyShadow A U := by
    intro g
    exact (Submodule.map_mono (hsourceU g)).trans
      (le_iSup (fun j => U.map (A j)) (selector g))
  let assemble : (⨁ g, ↥(imageGrade g)) →ₗ[K] X :=
    DFinsupp.lsum ℕ fun g => (imageGrade g).subtype
  have hassemble : Function.Injective assemble := by
    exact himageIndep.dfinsupp_lsum_injective
  have hassembleRange : LinearMap.range assemble ≤ linearFamilyShadow A U := by
    change LinearMap.range
      (DFinsupp.lsum ℕ fun g => (imageGrade g).subtype) ≤ _
    rw [← Submodule.iSup_eq_range_dfinsupp_lsum]
    exact iSup_le himageShadow
  let resolvedAssembly : (⨁ g, ↥(imageGrade g)) →ₗ[K]
    linearFamilyShadow A U :=
    assemble.codRestrict (linearFamilyShadow A U) fun x =>
      hassembleRange (LinearMap.mem_range_self assemble x)
  have hresolved : Function.Injective resolvedAssembly := by
    intro x y hxy
    apply hassemble
    exact congrArg Subtype.val hxy
  have hdim := resolvedAssembly.finrank_le_finrank_of_injective hresolved
  rw [Module.finrank_directSum] at hdim
  have himageRank : ∀ g,
      Module.finrank K (imageGrade g) = Module.finrank K (source g) := by
    intro g
    let F := (A (selector g)).domRestrict (source g)
    have hF : Function.Injective F := hinjective g
    have heq := LinearEquiv.finrank_eq (LinearEquiv.ofInjective F hF)
    dsimp [F] at heq
    rw [LinearMap.range_domRestrict] at heq
    exact heq.symm
  rw [show (∑ g, Module.finrank K (imageGrade g)) =
      ∑ g, Module.finrank K (source g) by
        apply Finset.sum_congr rfl
        intro g _hg
        exact himageRank g] at hdim
  rw [← hUrank] at hdim
  exact hdim

end

end GaloisForLFunctions.HTGeometry
