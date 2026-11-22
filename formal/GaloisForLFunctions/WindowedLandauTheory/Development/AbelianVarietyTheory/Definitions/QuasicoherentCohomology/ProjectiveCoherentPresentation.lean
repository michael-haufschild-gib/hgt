import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveSectionExtension
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! A quasi-coherent module with finite coordinate sections is a quotient of
a finite sum of negative twists. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

universe u

private theorem epi_of_surjective_on_affineCover {X : Scheme.{u}} {G F : X.Modules}
    [F.IsQuasicoherent] (φ : G ⟶ F) {ι : Type*} (U : ι → X.Opens)
    (hcov : ⨆ i, U i = ⊤) (haff : ∀ i, IsAffineOpen (U i))
    (hsurj : ∀ i, Function.Surjective (φ.app (U i))) : Epi φ := by
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  haveI : Sheaf.IsLocallySurjective (A.map φ) := by
    constructor
    intro W m
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hxU : x ∈ ⨆ i, U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨r, hr, hxr⟩ := (haff i).exists_basicOpen_le (V := W ⊓ U i) ⟨x, hx, hi⟩ hi
    let D := X.basicOpen r
    let ιW : D ⟶ W := homOfLE (hr.trans inf_le_left)
    let ιU : D ⟶ U i := homOfLE (X.basicOpen_le r)
    let t : Γ(F, D) := F.presheaf.map ιW.op m
    obtain ⟨n, y, hy⟩ := (hasBasicOpenLocalization_of_isQuasicoherent F (haff i) r).1 t
    obtain ⟨s, hs⟩ := hsurj i y
    obtain ⟨a, ha⟩ : IsUnit ((X.presheaf.map ιU.op r) ^ n) :=
      (X.toRingedSpace.isUnit_res_basicOpen r).pow n
    let z : Γ(G, D) := ((a⁻¹ : (Γ(X, D))ˣ) : Γ(X, D)) • G.presheaf.map ιU.op s
    refine ⟨D, ιW, ⟨z, ?_⟩, hxr⟩
    change φ.app D z = t
    have hn := NatTrans.naturality_apply φ.mapPresheaf ιU.op s
    change φ.app D (G.presheaf.map ιU.op s) = F.presheaf.map ιU.op (φ.app (U i) s) at hn
    change ((X.presheaf.map ιU.op r) ^ n) • t = F.presheaf.map ιU.op y at hy
    change (a : Γ(X, D)) = (X.presheaf.map ιU.op r) ^ n at ha
    dsimp only [z]
    rw [Scheme.Modules.Hom.app_smul, hn, hs, ← hy, ← ha, ← mul_smul, Units.inv_mul, one_smul]
  haveI : Epi (A.map φ) := inferInstance
  refine ⟨fun g h eq => A.map_injective ((cancel_epi (A.map φ)).mp ?_)⟩
  have e := congrArg A.map eq
  exact (A.map_comp φ g).symm.trans (e.trans (A.map_comp φ h))

open ProjTwist in
/-- Choose lifts of finitely many generators of the modules on the coordinate charts. -/
theorem exists_epi_twistCoproduct
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type u} [Fintype ι]
    {v : ι → A} (hv : ∀ i, v i ∈ 𝒜 1)
    (hcov : ⨆ i, Proj.basicOpen 𝒜 (v i) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent]
    (hfin : ∀ i, Module.Finite Γ(Proj 𝒜, Proj.basicOpen 𝒜 (v i)) Γ(F, Proj.basicOpen 𝒜 (v i))) :
    ∃ (I : Type u) (_ : Fintype I) (m : I → ℕ)
      (φ : (∐ fun a : I => twistingSheaf 𝒜 (-(m a : ℤ))) ⟶ F), Epi φ := by
  classical
  let U (i : ι) := Proj.basicOpen 𝒜 (v i)
  have hfg (i : ι) : ∃ S : Finset Γ(F, U i),
      Submodule.span Γ(Proj 𝒜, U i) (S : Set Γ(F, U i)) = ⊤ := by
    letI := hfin i
    exact Module.Finite.fg_top
  choose S hS using hfg
  let I := (i : ι) × {s : Γ(F, U i) // s ∈ S i}
  haveI : Fintype I := inferInstanceAs (Fintype ((i : ι) × {s : Γ(F, U i) // s ∈ S i}))
  have hlift (a : I) : ∃ (m : ℕ) (f : twistingSheaf 𝒜 (-(m : ℤ)) ⟶ F),
      f.app (U a.1) (coordinatePower (hv a.1) (-(m : ℤ))) = a.2.val :=
    exists_twist_hom_lifting_section hv F hcov a.1 a.2.1
  choose m f hf using hlift
  let π := Sigma.desc f
  refine ⟨I, inferInstance, m, π, epi_of_surjective_on_affineCover π U hcov
    (fun i => Proj.isAffineOpen_basicOpen 𝒜 _ (hv i) Nat.one_pos) (fun i => ?_)⟩
  let L : _ →ₗ[Γ(Proj 𝒜, U i)] Γ(F, U i) := (π.val.app (op (U i))).hom
  have hL : (S i : Set Γ(F, U i)) ⊆ LinearMap.range L := by
    intro s hs
    let a : I := ⟨i, ⟨s, hs⟩⟩
    let z := coordinatePower (hv i) (-(m a : ℤ))
    let in_a := Sigma.ι (fun a : I => twistingSheaf 𝒜 (-(m a : ℤ))) a
    refine ⟨in_a.app (U i) z, ?_⟩
    change π.app (U i) (in_a.app (U i) z) = s
    have h := congrArg (fun η => η.app (U i) z) (Sigma.ι_desc f a)
    exact h.trans (hf a)
  have htop : LinearMap.range L = ⊤ := by
    apply top_unique
    rw [← hS i]
    exact Submodule.span_le.mpr hL
  intro y
  have hy : y ∈ LinearMap.range L := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

end GlobalTheory.SchemeCohomology
