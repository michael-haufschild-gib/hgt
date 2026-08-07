import GaloisForLFunctions.HTGeometry.CDGATensorConst
import GaloisForLFunctions.HTGeometry.CDGAShiftQuasiIso
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Free coefficients preserve quasi-isomorphisms

Tensoring degreewise with a free module of finite rank is a finite product of copies of the module,
so it preserves quasi-isomorphisms.  This is the statement that discharges the coefficient half of a
free cell.

* `HTGeometry.tensorConstPiHom` : tensoring with `ι → R` is the product over `ι`.
* `HTGeometry.tensorConstMap_isQuasiIsoFull` : free coefficients preserve full quasi-isomorphisms.
* `HTGeometry.freeCellFunctor_isQuasiIsoFull` : and so does shifting them, which is the free cell.
-/

universe v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- **Tensoring with a free module of finite rank is the product of copies of the module.** -/
def tensorConstPiHom (P : CDGAModuleStructure A M) (ι : Type w) [Fintype ι] [DecidableEq ι] :
    CDGAModuleHom (tensorConstModule P (ι → R)) (CDGAModuleStructure.pi (fun _ : ι => P)) where
  toFun n z := TensorProduct.piScalarRight R R (M n) ι z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act := by
    intro a b n h x z
    show TensorProduct.piScalarRight R R (M n) ι
        (TensorProduct.map (P.actₗ h x) LinearMap.id z)
      = fun j => P.act h x (TensorProduct.piScalarRight R R (M b) ι z j)
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
        exact funext fun _ => ((P.actₗ h x).map_zero).symm
    | tmul m f =>
        rw [TensorProduct.map_tmul]
        simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
        exact funext fun j => (P.act_smul_right h (f j) x m).symm
    | add z z' hz hz' =>
        simp only [map_add]
        rw [hz, hz']
        exact funext fun _ => (P.act_add_right h x _ _).symm
  map_d := by
    intro n z
    show TensorProduct.piScalarRight R R (M (n + 1)) ι
        (TensorProduct.map (P.dₗ n) LinearMap.id z)
      = fun j => P.d n (TensorProduct.piScalarRight R R (M n) ι z j)
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
        exact funext fun _ => ((P.dₗ n).map_zero).symm
    | tmul m f =>
        rw [TensorProduct.map_tmul]
        simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
        exact funext fun j => (P.d_smul n (f j) m).symm
    | add z z' hz hz' =>
        simp only [map_add]
        rw [hz, hz']
        exact funext fun _ => (P.d_add n _ _).symm

theorem tensorConstPiHom_bijective (P : CDGAModuleStructure A M) (ι : Type w) [Fintype ι]
    [DecidableEq ι] (n : ℕ) : Function.Bijective ((tensorConstPiHom P ι).toFun n) :=
  (TensorProduct.piScalarRight R R (M n) ι).bijective

theorem tensorConstPiHom_isQuasiIsoFull (P : CDGAModuleStructure A M) (ι : Type w) [Fintype ι]
    [DecidableEq ι] : (tensorConstPiHom P ι).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective (tensorConstPiHom_bijective P ι)

section Invariance

variable {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- Tensoring with a free module is natural. -/
theorem tensorConstPiHom_naturality (φ : CDGAModuleHom P P') (ι : Type w) [Fintype ι]
    [DecidableEq ι] :
    (tensorConstPiHom P' ι).comp (tensorConstMap φ (ι → R))
      = (CDGAModuleHom.piMap (fun _ : ι => φ)).comp (tensorConstPiHom P ι) := by
  refine CDGAModuleHom.hom_ext fun n z => ?_
  show TensorProduct.piScalarRight R R (M' n) ι
      (TensorProduct.map (φ.mapₗ n) LinearMap.id z)
    = fun j => φ.toFun n (TensorProduct.piScalarRight R R (M n) ι z j)
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
      exact funext fun _ => ((φ.mapₗ n).map_zero).symm
  | tmul m f =>
      rw [TensorProduct.map_tmul]
      simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      exact funext fun j => (φ.map_smul n (f j) m).symm
  | add z z' hz hz' =>
      simp only [map_add]
      rw [hz, hz']
      exact funext fun _ => (φ.map_add n _ _).symm

/-- **Tensoring with a free module of finite rank preserves full quasi-isomorphisms.** -/
theorem tensorConstMap_pi_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    (ι : Type w) [Fintype ι] [DecidableEq ι] :
    (tensorConstMap φ (ι → R)).IsQuasiIsoFull := by
  have h1 : ((CDGAModuleHom.piMap (fun _ : ι => φ)).comp (tensorConstPiHom P ι)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.comp
      (CDGAModuleHom.IsQuasiIsoFull.piMap fun _ => hφ) (tensorConstPiHom_isQuasiIsoFull P ι)
  rw [← tensorConstPiHom_naturality φ ι] at h1
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 (tensorConstPiHom_isQuasiIsoFull P' ι)

/-- Changing the coefficient module along a linear isomorphism is natural. -/
theorem tensorConstVMap_naturality (φ : CDGAModuleHom P P') {V W : Type w} [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (ψ : V →ₗ[R] W) :
    (tensorConstMap φ W).comp (tensorConstVMap P ψ)
      = (tensorConstVMap P' ψ).comp (tensorConstMap φ V) := by
  refine CDGAModuleHom.hom_ext fun n z => ?_
  show TensorProduct.map (φ.mapₗ n) LinearMap.id (TensorProduct.map LinearMap.id ψ z)
    = TensorProduct.map LinearMap.id ψ (TensorProduct.map (φ.mapₗ n) LinearMap.id z)
  have hcomm : (TensorProduct.map (φ.mapₗ n) (LinearMap.id : W →ₗ[R] W)).comp
        (TensorProduct.map (LinearMap.id : M n →ₗ[R] M n) ψ)
      = (TensorProduct.map (LinearMap.id : M' n →ₗ[R] M' n) ψ).comp
        (TensorProduct.map (φ.mapₗ n) (LinearMap.id : V →ₗ[R] V)) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
  exact congrArg (fun L => L z) hcomm

/-- **Free coefficients preserve full quasi-isomorphisms.**  A basis identifies the coefficient
module with a finite product of copies of the ground ring, and the comparison is natural. -/
theorem tensorConstMap_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    {V : Type w} [AddCommGroup V] [Module R V] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V) : (tensorConstMap φ V).IsQuasiIsoFull := by
  have heP : (tensorConstVMap P (b.equivFun : V →ₗ[R] (ι → R))).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (tensorConstVMap_bijective P b.equivFun)
  have heP' : (tensorConstVMap P' (b.equivFun : V →ₗ[R] (ι → R))).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (tensorConstVMap_bijective P' b.equivFun)
  have h1 : ((tensorConstVMap P' (b.equivFun : V →ₗ[R] (ι → R))).comp
      (tensorConstMap φ V)).IsQuasiIsoFull := by
    rw [← tensorConstVMap_naturality φ (b.equivFun : V →ₗ[R] (ι → R))]
    exact CDGAModuleHom.IsQuasiIsoFull.comp (tensorConstMap_pi_isQuasiIsoFull φ hφ ι) heP
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 heP'

/-- **The free cell functor preserves full quasi-isomorphisms.**  A free cell is a shift of a free
coefficient module, and each of the two operations preserves them: the coefficients because a basis
turns them into a finite product, the shift because `IsQuasiIsoFull` is stable under moving
degree-zero cocycle data into ordinary cohomology. -/
theorem freeCellFunctor_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    {V : Type w} [AddCommGroup V] [Module R V] {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V) (k : ℕ) :
    (shiftMap (tensorConstMap φ V) k).IsQuasiIsoFull :=
  shiftMap_isQuasiIsoFull _ (tensorConstMap_isQuasiIsoFull φ hφ b) k

end Invariance

end GaloisForLFunctions.HTGeometry
