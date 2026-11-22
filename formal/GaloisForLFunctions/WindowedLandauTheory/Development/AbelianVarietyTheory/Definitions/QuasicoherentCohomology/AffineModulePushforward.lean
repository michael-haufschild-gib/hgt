import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Direct image under an affine morphism preserves quasi-coherence.
For closed immersions it also preserves finite generation on affine opens. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : Y.Modules)

private theorem pushforward_localization [IsAffineHom f] [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    HasBasicOpenLocalization ((Scheme.Modules.pushforward f).obj M) U a := by
  let i := homOfLE (X.basicOpen_le a)
  let j := (Opens.map f.base).map i
  let b := f.app U a
  have hpre : f ⁻¹ᵁ X.basicOpen a = Y.basicOpen b := f.preimage_basicOpen a
  have loc {V : Y.Opens} (j' : V ⟶ f ⁻¹ᵁ U) (e : V = Y.basicOpen b) :
      (∀ y : Γ(M, V), ∃ (n : ℕ) (x : Γ(M, f ⁻¹ᵁ U)),
        (Y.presheaf.map j'.op b) ^ n • y = M.presheaf.map j'.op x) ∧
      (∀ x : Γ(M, f ⁻¹ᵁ U), M.presheaf.map j'.op x = 0 → ∃ n : ℕ, b ^ n • x = 0) := by
    subst V
    have hj : j' = homOfLE (Y.basicOpen_le b) := Subsingleton.elim _ _
    subst j'
    exact hasBasicOpenLocalization_of_isQuasicoherent M (hU.preimage f) b
  obtain ⟨hs, hk⟩ := loc j hpre
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨n, x, hx⟩ := hs y
    refine ⟨n, x, ?_⟩
    change f.app (X.basicOpen a) ((X.presheaf.map i.op a) ^ n) •
      (show Γ(M, f ⁻¹ᵁ X.basicOpen a) from y) = M.presheaf.map j.op x
    have hn : f.app (X.basicOpen a) (X.presheaf.map i.op a) = Y.presheaf.map j.op b :=
      ConcreteCategory.congr_hom (f.naturality i.op) a
    rw [map_pow, hn]
    exact hx
  · intro x hx
    obtain ⟨n, hn⟩ := hk x hx
    refine ⟨n, ?_⟩
    change f.app U (a ^ n) • (show Γ(M, f ⁻¹ᵁ U) from x) = 0
    rwa [map_pow]

/-- Affine direct image preserves localization on the basic opens of an affine cover. -/
theorem pushforward_isQuasicoherent [IsAffineHom f] [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let U : {V : X.Opens // IsAffineOpen V} → X.Opens := Subtype.val
  have hcov : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  exact isQuasicoherent_of_affineCover_localization ((Scheme.Modules.pushforward f).obj M) U hcov
    (fun i => i.property) (fun i a => pushforward_localization f M i.property a)

/-- A closed immersion gives a quotient on affine section rings, so sections finite
over the source ring also form a finite module over the target ring. -/
theorem pushforward_sections_finite [IsClosedImmersion f] {U : X.Opens}
    (hU : IsAffineOpen U) [Module.Finite Γ(Y, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U)] :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pushforward f).obj M, U) := by
  letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  haveI : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    Module.Finite.of_surjective (Algebra.linearMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U)) (f.app_surjective U hU)
  letI : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U)
      Γ((Scheme.Modules.pushforward f).obj M, U) :=
    .of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans (Γ(Y, f ⁻¹ᵁ U)) Γ((Scheme.Modules.pushforward f).obj M, U)

end GlobalTheory.SchemeCohomology
