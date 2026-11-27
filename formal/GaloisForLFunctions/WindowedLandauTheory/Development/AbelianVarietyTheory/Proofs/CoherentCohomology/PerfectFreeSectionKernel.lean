import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FirstTwoDegreesOfQuasiIso
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGlobalLineBundleSections
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The first differential of a given free Čech model represents sections
after scalar change, with coordinates determined by its degree-zero map. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi TensorProduct
open scoped ChangeOfRings

namespace GlobalTheory.LineBundleSections

private def tensorBasisVector {R S P : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P] {a : ℕ} (p : Module.Basis (Fin a) R P) :
    (Fin a → S) ≃ₗ[S] S ⊗[R] P :=
  (Algebra.TensorProduct.basis S p).equivFun.symm

private theorem tensorBasisVector_apply {R S P : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P] {a : ℕ} (p : Module.Basis (Fin a) R P)
    (v : Fin a → S) : tensorBasisVector (S := S) p v = ∑ k, v k ⊗ₜ[R] p k := by
  simp [tensorBasisVector, TensorProduct.smul_tmul']

private theorem tensorBasisVector_mulVec {R S P Q : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {a b : ℕ}
    (p : Module.Basis (Fin a) R P) (q : Module.Basis (Fin b) R Q) (d : P →ₗ[R] Q)
    (v : Fin a → S) :
    tensorBasisVector q (((LinearMap.toMatrix p q d).map (algebraMap R S)).mulVec v) =
      d.baseChange S (tensorBasisVector p v) := by
  rw [tensorBasisVector, LinearEquiv.symm_apply_eq, ← LinearMap.toMatrix_baseChange,
    Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis S p)]
  congr 1
  exact ((Algebra.TensorProduct.basis S p).equivFun.apply_symm_apply v).symm

/-- The matrix of the first differential, in the specified bases, computes
the section kernel on every affine base change on which the model is valid. -/
theorem exists_free_kernel_section_equiv {R S : Type} [CommRing R] [CommRing S]
    {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of S)} {π : Y ⟶ X}
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))
    {C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : C ⟶ cech f (toMod L) U)
    {a b : ℕ} (p : Module.Basis (Fin a) R (C.X 0)) (q : Module.Basis (Fin b) R (C.X 1))
    (α : R →+* S) (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    (hφ : QuasiIso (((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) :
    letI := sectionBaseModule g (toMod (L.pull π)) ⊤
    let D := LinearMap.toMatrix p q (C.d 0 1).hom
    ∃ e : LinearMap.ker (D.map α).mulVecLin ≃ₗ[S] Γ(toMod (L.pull π), ⊤),
      ∀ v (i : κ × L.ι),
        let W := coverInter ⊤ U {i.1} ⊓ L.U i.2
        letI := sectionAlgebra g (π ⁻¹ᵁ W)
        resG Y (le_inf le_top ((π.preimage_mono (show W ≤ L.U i.2 from inf_le_right)).trans
          (pull_chart L π i.2).ge)) (coord (e v) (fun _ => i.2)) =
          ∑ k, algebraMap S Γ(Y, π ⁻¹ᵁ W) (v.1 k) *
            π.app W (coord (((φ.f 0).hom (p k)).1 {i.1}) i.2) := by
  letI : Algebra R S := α.toAlgebra
  let G := toMod (L.pull π)
  letI := sectionBaseModule g G ⊤
  let D := LinearMap.toMatrix p q (C.d 0 1).hom
  let T := (ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℕ)
  let V (i : κ) := π ⁻¹ᵁ U i
  let E := cechBaseChangeIso L U hL α H hU
  let ψ : T.obj C ⟶ cech g G V := T.map φ ≫ E.hom
  letI : QuasiIso (T.map φ) := hφ
  letI : QuasiIso ψ := inferInstanceAs (QuasiIso (T.map φ ≫ E.hom))
  have hV : ⊤ ≤ ⨆ i, V i := (π.iSup_preimage_eq_top hcov).ge
  let vec := tensorBasisVector (S := S) p
  have hv (v : Fin a → S) : v ∈ LinearMap.ker (D.map α).mulVecLin ↔
      vec v ∈ LinearMap.ker ((T.obj C).d 0 1).hom := by
    change (D.map α).mulVec v = 0 ↔ (C.d 0 1).hom.baseChange S (vec v) = 0
    rw [← tensorBasisVector_mulVec p q _ v, LinearEquiv.map_eq_zero_iff]
    rfl
  let B := ((ψ.f 0).hom).comp vec.toLinearMap
  have hB : Set.BijOn B (LinearMap.ker (D.map α).mulVecLin)
      (LinearMap.ker ((cech g G V).d 0 1).hom) :=
    (GlobalTheory.bijOn_ker_and_exact_of_quasiIso ψ).1.comp
      ⟨fun v h => (hv v).mp h, vec.injective.injOn, fun y hy => by
        obtain ⟨v, rfl⟩ := vec.surjective y
        exact ⟨v, (hv v).mpr hy, rfl⟩⟩
  let j : LinearMap.ker (D.map α).mulVecLin →ₗ[S] LinearMap.ker ((cech g G V).d 0 1).hom :=
    { toFun := fun v => ⟨B v.1, hB.mapsTo v.2⟩
      map_add' := fun v w => Subtype.ext (map_add B v.1 w.1)
      map_smul' := fun r v => Subtype.ext (map_smul B r v.1) }
  let A := globalSectionsLinearEquivKernel g G V hV
  let e := (LinearEquiv.ofBijective j (hB.equiv _).bijective).trans A.symm
  refine ⟨e, fun v i => ?_⟩
  let t : (L.pull π).ι := fun _ => i.2
  let s : Finset κ := {i.1}
  let J := coverInter ⊤ V s
  let J₀ := coverInter ⊤ U s
  have hJ : J = π ⁻¹ᵁ J₀ := coverInter_pull (π := π) U s
  let W := J₀ ⊓ L.U i.2
  let w := π ⁻¹ᵁ W
  have h₁ : w ≤ J := (π.preimage_mono inf_le_left).trans hJ.ge
  have h₂ : w ≤ (L.pull π).U t := (π.preimage_mono inf_le_right).trans (pull_chart L π i.2).ge
  letI := sectionAlgebra g w
  letI := sectionAlgebra g J
  let det : (cech g G V).X 0 →+ Γ(Y, w) :=
    { toFun := fun x => resG Y (le_inf h₁ h₂) (coord (x.1 s) t)
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have he : (A (e v)).1.1 s = ((ψ.f 0).hom (vec v.1)).1 s :=
    congrArg (fun z : LinearMap.ker ((cech g G V).d 0 1).hom => z.1.1 s)
      (A.apply_symm_apply (j v))
  have hdet : resG Y (le_inf le_top h₂) (coord (e v) t) = det ((ψ.f 0).hom (vec v.1)) := by
    change _ = resG Y (le_inf h₁ h₂) (coord (((ψ.f 0).hom _).1 s) t)
    rw [← he]
    change _ = resG Y (le_inf h₁ h₂)
      (coord ((globalSectionsEquivKernel g G V hV (e v)).1.1 {i.1}) t)
    rw [globalSectionsEquivKernel_singleton, coord_map, resG_resG]
  have hterm (k : Fin a) :
      det ((ψ.f 0).hom (v.1 k ⊗ₜ[R] p k)) =
        algebraMap S Γ(Y, w) (v.1 k) * π.app W (coord (((φ.f 0).hom (p k)).1 s) i.2) := by
    let x := (φ.f 0).hom (p k)
    have hp : ((ψ.f 0).hom (v.1 k ⊗ₜ[R] p k)).1 s =
        algebraMap S Γ(Y, J) (v.1 k) • pullSection (ChartPull.pull L π) hJ.le (x.1 s) := by
      change ((E.hom.f 0) ((ModuleCat.extendScalars α).map (φ.f 0)
        (v.1 k ⊗ₜ[R,α] p k))).1 s = _
      rw [ModuleCat.ExtendScalars.map_tmul]
      exact cechBaseChangeIso_hom_f_tmul L U hL α H hU 0 (v.1 k) x s
    change resG Y (le_inf h₁ h₂) (coord (((ψ.f 0).hom (_ ⊗ₜ[R] _)).1 s) t) = _
    rw [hp, coord_smul, map_mul, resG_resG, coord_pullSection, resG_appLE]
    rw [show resG Y h₁ (algebraMap S Γ(Y, J) (v.1 k)) = algebraMap S Γ(Y, w) (v.1 k) from
      (sectionRes g (homOfLE h₁)).commutes (v.1 k), Scheme.Hom.app_eq_appLE]
    rfl
  change resG Y (le_inf le_top h₂) (coord (e v) t) = _
  let value := det.comp (ψ.f 0).hom.toAddMonoidHom
  calc
    _ = value (vec v.1) := hdet
    _ = value (∑ k, v.1 k ⊗ₜ[R] p k) := congrArg value (tensorBasisVector_apply p v.1)
    _ = ∑ k, value (v.1 k ⊗ₜ[R] p k) := map_sum value _ _
    _ = _ := Finset.sum_congr rfl fun k _ => hterm k

end GlobalTheory.LineBundleSections
