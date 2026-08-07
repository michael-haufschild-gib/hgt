import GaloisForLFunctions.HTGeometry.CDGAModuleFinsupp
import GaloisForLFunctions.HTGeometry.CDGAFreeCoefficients
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Free coefficients of arbitrary rank

Tensoring with a free module identifies it with the direct sum of copies of the module indexed by a
basis, and a direct sum of full quasi-isomorphisms is one.  This removes the finiteness of the basis
from the free-coefficient and free-cell invariance theorems.

* `HTGeometry.tensorConstFinsuppHom` : `M ⊗ (κ →₀ R) ≅ ⊕_κ M`.
* `HTGeometry.tensorConstMap_isQuasiIsoFull_of_basis` : free coefficients of arbitrary rank.
* `HTGeometry.freeCellFunctor_isQuasiIsoFull_of_basis` : free cells of arbitrary rank.
-/

universe v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- The exchange intertwines a map of the module factor. -/
theorem finsuppScalarRight_map {Y Z : Type w} [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (κ : Type w) [DecidableEq κ] (L : Y →ₗ[R] Z)
    (z : TensorProduct R Y (κ →₀ R)) (i : κ) :
    TensorProduct.finsuppScalarRight R R Z κ (TensorProduct.map L LinearMap.id z) i
      = L (TensorProduct.finsuppScalarRight R R Y κ z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u p =>
      rw [TensorProduct.map_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply,
        TensorProduct.finsuppScalarRight_apply_tmul_apply, L.map_smul]
      rfl
  | add z z' hz hz' => simp [hz, hz']

section Exchange

variable (P : CDGAModuleStructure A M) (κ : Type w) [DecidableEq κ]

/-- **Tensoring with a free module is the direct sum of copies of the module.** -/
noncomputable def tensorConstFinsuppHom :
    CDGAModuleHom (tensorConstModule P (κ →₀ R)) (finsuppModule P κ) where
  toFun n z := TensorProduct.finsuppScalarRight R R (M n) κ z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act h x z := by
    refine Finsupp.ext fun i => ?_
    exact finsuppScalarRight_map κ (P.actₗ h x) z i
  map_d n z := by
    refine Finsupp.ext fun i => ?_
    exact finsuppScalarRight_map κ (P.dₗ n) z i

theorem tensorConstFinsuppHom_isQuasiIsoFull : (tensorConstFinsuppHom P κ).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n =>
    (TensorProduct.finsuppScalarRight R R (M n) κ).bijective

end Exchange

section Invariance

variable {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The exchange is natural in the module. -/
theorem tensorConstFinsuppHom_naturality (φ : CDGAModuleHom P P') (κ : Type w) [DecidableEq κ] :
    (finsuppMap φ κ).comp (tensorConstFinsuppHom P κ)
      = (tensorConstFinsuppHom P' κ).comp (tensorConstMap φ (κ →₀ R)) := by
  refine CDGAModuleHom.hom_ext fun n z => ?_
  refine Finsupp.ext fun i => ?_
  show φ.toFun n (TensorProduct.finsuppScalarRight R R (M n) κ z i)
    = TensorProduct.finsuppScalarRight R R (M' n) κ
      (TensorProduct.map (φ.mapₗ n) LinearMap.id z) i
  rw [finsuppScalarRight_map κ (φ.mapₗ n) z i]
  rfl

/-- **Tensoring with a free module of arbitrary rank preserves full quasi-isomorphisms.** -/
theorem tensorConstMap_finsupp_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    (κ : Type w) [DecidableEq κ] : (tensorConstMap φ (κ →₀ R)).IsQuasiIsoFull := by
  have h1 : ((finsuppMap φ κ).comp (tensorConstFinsuppHom P κ)).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.comp (finsuppMap_isQuasiIsoFull φ κ hφ)
      (tensorConstFinsuppHom_isQuasiIsoFull P κ)
  rw [tensorConstFinsuppHom_naturality φ κ] at h1
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 (tensorConstFinsuppHom_isQuasiIsoFull P' κ)

/-- **Free coefficients of arbitrary rank preserve full quasi-isomorphisms.** -/
theorem tensorConstMap_isQuasiIsoFull_of_basis (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    {V : Type w} [AddCommGroup V] [Module R V] {κ : Type w} [DecidableEq κ]
    (b : Module.Basis κ R V) : (tensorConstMap φ V).IsQuasiIsoFull := by
  have heP : (tensorConstVMap P (b.repr : V →ₗ[R] (κ →₀ R))).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (tensorConstVMap_bijective P b.repr)
  have heP' : (tensorConstVMap P' (b.repr : V →ₗ[R] (κ →₀ R))).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (tensorConstVMap_bijective P' b.repr)
  have h1 : ((tensorConstVMap P' (b.repr : V →ₗ[R] (κ →₀ R))).comp
      (tensorConstMap φ V)).IsQuasiIsoFull := by
    rw [← tensorConstVMap_naturality φ (b.repr : V →ₗ[R] (κ →₀ R))]
    exact CDGAModuleHom.IsQuasiIsoFull.comp
      (tensorConstMap_finsupp_isQuasiIsoFull φ hφ κ) heP
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 heP'

/-- **The free cell functor of arbitrary rank preserves full quasi-isomorphisms.** -/
theorem freeCellFunctor_isQuasiIsoFull_of_basis (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    {V : Type w} [AddCommGroup V] [Module R V] {κ : Type w} [DecidableEq κ]
    (b : Module.Basis κ R V) (k : ℕ) : (shiftMap (tensorConstMap φ V) k).IsQuasiIsoFull :=
  shiftMap_isQuasiIsoFull _ (tensorConstMap_isQuasiIsoFull_of_basis φ hφ b) k

end Invariance

end GaloisForLFunctions.HTGeometry
