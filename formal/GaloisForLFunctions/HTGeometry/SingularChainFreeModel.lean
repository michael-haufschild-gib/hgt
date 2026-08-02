import Mathlib.AlgebraicTopology.SingularHomology.Basic
import GaloisForLFunctions.HTGeometry.FreeModuleCoproduct

/-!
# The simplicial chain complex in the free module model

With coefficients in the base field, the chain space of a simplicial chain complex in degree `n` is
the coproduct of one copy of the field for each `n`-simplex, hence the free module on the
`n`-simplices; the differential is the alternating sum of the maps induced by the face maps.  So the
chain complex is the free chain complex on the simplices, and the boundedness of the differential
for the free locally convex seminorms applies to it verbatim.

* `sSetFreeChain`, `sSetChainSpaceIso` : **the chain space is the free module on the simplices.**
* `sSetChain_d_comp`, `sSetChain_d_conj` : **the differential is the alternating face differential
  of the free model.**
* `sSetChain_freeSeminorm_d_le` : **the differential is bounded** for the free locally convex
  seminorms.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial Opposite

noncomputable section

namespace GaloisForLFunctions

variable (𝕜 : Type) [NormedField 𝕜]

/-- The simplicial chain complex with coefficients in the base field. -/
abbrev sSetFreeChain (S : SSet.{0}) : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  ((SSet.chainComplexFunctor (ModuleCat.{0} 𝕜)).obj (ModuleCat.of 𝕜 𝕜)).obj S

/-- The chain space of the simplicial chain complex, presented as the coproduct of one copy of the
base field for each simplex. -/
abbrev sSetFreeChainSpace (S : SSet.{0}) (n : ℕ) : ModuleCat.{0} 𝕜 :=
  ∐ fun _ : S.obj (op ⦋n⦌) => ModuleCat.of 𝕜 𝕜

/-- The differential of the simplicial chain complex, read on that presentation. -/
def sSetFreeChainD (S : SSet.{0}) (n : ℕ) :
    sSetFreeChainSpace 𝕜 S (n + 1) ⟶ sSetFreeChainSpace 𝕜 S n :=
  (sSetFreeChain 𝕜 S).d (n + 1) n

theorem sSetFreeChainD_eq (S : SSet.{0}) (n : ℕ) :
    sSetFreeChainD 𝕜 S n = (sSetFreeChain 𝕜 S).d (n + 1) n := rfl

/-- **The chain space of a simplicial chain complex with coefficients in the base field is the free
module on the simplices of that degree.** -/
def sSetChainSpaceIso (S : SSet.{0}) (n : ℕ) :
    sSetFreeChainSpace 𝕜 S n ≅ ModuleCat.of 𝕜 (S.obj (op ⦋n⦌) →₀ 𝕜) :=
  freeCoprodIso 𝕜 _

theorem ι_sSetChainSpaceIso_hom (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n⦌)) :
    Sigma.ι (fun _ : S.obj (op ⦋n⦌) => ModuleCat.of 𝕜 𝕜) σ ≫ (sSetChainSpaceIso 𝕜 S n).hom
      = ModuleCat.ofHom (Finsupp.lsingle (R := 𝕜) (M := 𝕜) σ) :=
  ι_freeCoprodIso_hom 𝕜 σ

theorem sSetChain_d (S : SSet.{0}) (n : ℕ) :
    sSetFreeChainD 𝕜 S n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Sigma.map' (S.δ i) fun _ => 𝟙 (ModuleCat.of 𝕜 𝕜)) := by
  rw [sSetFreeChainD]
  show ((alternatingFaceMapComplex (ModuleCat.{0} 𝕜)).obj
      (S ⋙ sigmaConst.obj (ModuleCat.of 𝕜 𝕜))).d (n + 1) n = _
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  rfl

theorem sSetChain_ofHom_freeBoundary (S : SSet.{0}) (n : ℕ) :
    (ModuleCat.ofHom (freeBoundary (𝕜 := 𝕜) (n := n) fun i => S.δ i) :
        ModuleCat.of 𝕜 (S.obj (op ⦋n + 1⦌) →₀ 𝕜) ⟶ ModuleCat.of 𝕜 (S.obj (op ⦋n⦌) →₀ 𝕜))
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ModuleCat.ofHom (Finsupp.lmapDomain 𝕜 𝕜 (S.δ i)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  rw [freeBoundary_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul 𝕜]
  congr 1
  push_cast
  ring

/-- The differential composed with a summand inclusion is the alternating sum of the inclusions of
the faces. -/
theorem ι_comp_sSetChain_d (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ : S.obj (op ⦋n + 1⦌) => ModuleCat.of 𝕜 𝕜) σ ≫ sSetFreeChainD 𝕜 S n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          Sigma.ι (fun _ : S.obj (op ⦋n⦌) => ModuleCat.of 𝕜 𝕜) (S.δ i σ) := by
  rw [sSetChain_d, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul]
  congr 1
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- **The differential of the simplicial chain complex is the alternating face differential of the
free model.** -/
theorem sSetChain_d_comp (S : SSet.{0}) (n : ℕ) :
    sSetFreeChainD 𝕜 S n ≫ (sSetChainSpaceIso 𝕜 S n).hom
      = (sSetChainSpaceIso 𝕜 S (n + 1)).hom
        ≫ ModuleCat.ofHom (freeBoundary (𝕜 := 𝕜) (n := n) fun i => S.δ i) := by
  refine Sigma.hom_ext _ _ fun σ => ?_
  rw [← Category.assoc, ι_comp_sSetChain_d, Preadditive.sum_comp, ← Category.assoc]
  rw [ι_sSetChainSpaceIso_hom]
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  have key : ∀ τ : S.obj (op ⦋n⦌),
      (sSetChainSpaceIso 𝕜 S n).hom.hom
        ((Sigma.ι (fun _ : S.obj (op ⦋n⦌) => ModuleCat.of 𝕜 𝕜) τ).hom c)
        = Finsupp.single τ c := by
    intro τ
    have h := congrArg
      (fun m : ModuleCat.of 𝕜 𝕜 ⟶ ModuleCat.of 𝕜 (S.obj (op ⦋n⦌) →₀ 𝕜) => m.hom c)
      (ι_sSetChainSpaceIso_hom 𝕜 S n τ)
    simpa [Finsupp.lsingle_apply] using h
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.sum_apply]
  rw [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, freeBoundary_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, map_zsmul, key,
    Finsupp.mapDomain_single, ← Int.cast_smul_eq_zsmul 𝕜]
  congr 1
  push_cast
  ring

theorem sSetChain_d_conj (S : SSet.{0}) (n : ℕ) :
    (sSetChainSpaceIso 𝕜 S (n + 1)).inv ≫ sSetFreeChainD 𝕜 S n
        ≫ (sSetChainSpaceIso 𝕜 S n).hom
      = ModuleCat.ofHom (freeBoundary (𝕜 := 𝕜) (n := n) fun i => S.δ i) := by
  rw [sSetChain_d_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The differential of the simplicial chain complex is bounded** for the free locally convex
seminorms: read in the free model it is the alternating face differential. -/
theorem sSetChain_freeSeminorm_d_le (S : SSet.{0}) (n : ℕ) (w : S.obj (op ⦋n⦌) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (f : S.obj (op ⦋n + 1⦌) →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw
        (((sSetChainSpaceIso 𝕜 S (n + 1)).inv ≫ sSetFreeChainD 𝕜 S n
          ≫ (sSetChainSpaceIso 𝕜 S n).hom).hom f)
      ≤ ∑ i : Fin (n + 2),
          freeSeminorm (𝕜 := 𝕜) (fun a => w (S.δ i a)) (fun a => hw (S.δ i a)) f := by
  rw [sSetChain_d_conj, ModuleCat.hom_ofHom]
  exact freeSeminorm_freeBoundary_le (𝕜 := 𝕜) (fun i => S.δ i) w hw f

end GaloisForLFunctions

end
