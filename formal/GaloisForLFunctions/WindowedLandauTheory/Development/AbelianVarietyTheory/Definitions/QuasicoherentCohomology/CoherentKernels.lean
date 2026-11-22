import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! Kernels of maps between quasi-coherent modules are quasi-coherent. Over a locally
Noetherian scheme their affine sections are finite when the source has finite sections. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G)

local instance : (Scheme.Modules.toPresheaf X).PreservesZeroMorphisms :=
  ⟨fun _ _ => by ext; rfl⟩

local instance (U : X.Opens) :
    (Scheme.Modules.toPresheaf X ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op U)).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

private def kernelForkAppIsLimit (U : X.Opens) :
    IsLimit ((KernelFork.ofι (kernel.ι φ) (kernel.condition φ)).map
      (Scheme.Modules.toPresheaf X ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op U))) := by
  haveI : PreservesLimit (parallelPair φ 0) (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimit (parallelPair φ 0 ⋙ Scheme.Modules.toPresheaf X)
      ((evaluation _ AddCommGrpCat.{u}).obj (op U)) :=
    evaluation_preservesLimit (parallelPair φ 0 ⋙ Scheme.Modules.toPresheaf X) (op U)
  exact KernelFork.mapIsLimit _ (kernelIsKernel φ) _

/-- The inclusion of a kernel is injective on sections over every open. -/
theorem kernel_ι_app_injective (U : X.Opens) : Function.Injective ((kernel.ι φ).app U) :=
  (AddCommGrpCat.mono_iff_injective _).mp (Fork.IsLimit.mono (kernelForkAppIsLimit φ U))

/-- A section annihilated by a module map has a section in the sheaf kernel. -/
theorem kernel_ι_app_exact (U : X.Opens) (m : Γ(F, U)) (hm : φ.app U m = 0) :
    ∃ k : Γ(kernel φ, U), (kernel.ι φ).app U k = m := by
  let ψ : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ Γ(F, U) :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ m).comp AddEquiv.ulift.toAddMonoidHom)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (kernelForkAppIsLimit φ U) ψ (by
    ext x
    change φ.app U (x.down • m) = 0
    rw [map_zsmul, hm, smul_zero])
  refine ⟨l.hom ⟨1⟩, ?_⟩
  have e := congrArg (fun g => g.hom (⟨1⟩ : ULift.{u} ℤ)) hl
  change (kernel.ι φ).app U (l.hom ⟨1⟩) = (1 : ℤ) • m at e
  simpa only [one_smul] using e

private theorem kernel_basicOpenLocalization [F.IsQuasicoherent] [G.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    HasBasicOpenLocalization (kernel φ) U f := by
  let W := X.basicOpen f
  let i := homOfLE (X.basicOpen_le f)
  have hnat {M N : X.Modules} (g : M ⟶ N) (m : Γ(M, U)) :
      g.app W (M.presheaf.map i.op m) = N.presheaf.map i.op (g.app U m) :=
    NatTrans.naturality_apply g.mapPresheaf i.op m
  have hzero (k : Γ(kernel φ, W)) : φ.app W ((kernel.ι φ).app W k) = 0 :=
    (congrArg (fun g => g.app W k) (kernel.condition φ)).trans rfl
  obtain ⟨hFclear, hFkill⟩ := hasBasicOpenLocalization_of_isQuasicoherent F hU f
  obtain ⟨_, hGkill⟩ := hasBasicOpenLocalization_of_isQuasicoherent G hU f
  constructor
  · intro k
    obtain ⟨e, m, hm⟩ := hFclear ((kernel.ι φ).app W k)
    have hz : G.presheaf.map i.op (φ.app U m) = 0 := by
      rw [← hnat φ, ← hm, Scheme.Modules.Hom.app_smul, hzero, smul_zero]
    obtain ⟨e', he'⟩ := hGkill (φ.app U m) hz
    rw [← Scheme.Modules.Hom.app_smul] at he'
    obtain ⟨k', hk'⟩ := kernel_ι_app_exact φ U (f ^ e' • m) he'
    refine ⟨e' + e, k', kernel_ι_app_injective φ W ?_⟩
    rw [Scheme.Modules.Hom.app_smul, hnat, hk', F.map_smul, map_pow,
      ← hm, smul_smul, ← pow_add]
  · intro k hk
    have hz : F.presheaf.map i.op ((kernel.ι φ).app U k) = 0 := by
      rw [← hnat, hk, map_zero]
    obtain ⟨e, he⟩ := hFkill ((kernel.ι φ).app U k) hz
    refine ⟨e, kernel_ι_app_injective φ U ?_⟩
    rw [Scheme.Modules.Hom.app_smul, he, map_zero]

/-- Clearing denominators in the source and then in the target localizes the kernel. -/
theorem kernel_isQuasicoherent [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (kernel φ).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover_localization _ (fun U : X.affineOpens => (U : X.Opens))
    ?_ (fun U => U.2) (fun U f => kernel_basicOpenLocalization φ U.2 f)
  exact IsOpenCover.mk (iSup_affineOpens_eq_top X)

theorem kernel_sections_finite [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)] : Module.Finite Γ(X, U) Γ(kernel φ, U) := by
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let ι : Γ(kernel φ, U) →ₗ[Γ(X, U)] Γ(F, U) :=
    { toFun := (kernel.ι φ).app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_injective ι (kernel_ι_app_injective φ U)

end GlobalTheory.SchemeCohomology

end
