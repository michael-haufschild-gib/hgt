import GaloisForLFunctions.RHTower.SquareZeroUnitCyclicBoundary
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Augmentation derivations and Hochschild degree one

For commutative complex algebras the degree-one boundary is zero, so Hochschild
degree one is the quotient of full tensor chains by degree-two boundaries.
Vector-valued augmentation derivations descend to this quotient and certify
linear tangent embeddings. Square-zero unit cycles represent these tangent classes.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {A V : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup V] [Module ℂ V]

/-- In a commutative algebra every degree-one Hochschild chain is a cycle. -/
theorem boundaryOne_eq_zero :
    cyclicBarFace (R := ℂ) (A := A) (0 : Fin 2) -
      cyclicBarFace (R := ℂ) (A := A) (1 : Fin 2) = 0 := by
  apply PiTensorProduct.ext
  ext x
  change cyclicBarFace (R := ℂ) (0 : Fin 2) (PiTensorProduct.tprod ℂ x) -
    cyclicBarFace (R := ℂ) (1 : Fin 2) (PiTensorProduct.tprod ℂ x) = 0
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  exact sub_eq_zero.mpr (pair_is_cycle _ _ (mul_comm _ _))

/-- Hochschild degree one: all degree-one chains modulo degree-two boundaries.
Commutativity makes the degree-one boundary zero. -/
abbrev HochschildOne (A : Type*) [CommRing A] [Algebra ℂ A] :=
  CyclicBarTensor ℂ A 1 ⧸ LinearMap.range (boundaryTwo (A := A))

/-- The linear chain `v ↦ 1 ⊗ v`. -/
def tangentChain : A →ₗ[ℂ] CyclicBarTensor ℂ A 1 where
  toFun := pair 1
  map_add' a b := by
    have h (z : A) : Function.update ![1,a] 1 z = ![1,z] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_add ![1,a] 1 a b
  map_smul' c a := by
    change pair 1 (c • a) = c • pair 1 a
    have h (z : A) : Function.update ![1,a] 1 z = ![1,z] := by
      ext i; fin_cases i <;> simp
    simpa only [pair, h] using
      (PiTensorProduct.tprod ℂ (s := fun _ : Fin 2 => A)).map_update_smul ![1,a] 1 c a

/-- A vector-valued augmentation derivation detects the entire tangent space. -/
def tangentDetector (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V) :
    CyclicBarTensor ℂ A 1 →ₗ[ℂ] V :=
  PiTensorProduct.lift (MultilinearMap.mk'
    (fun x : Fin 2 → A => ε (x 0) • δ (x 1))
    (by intro x j a b; fin_cases j <;> simp [Function.update, add_smul, smul_add])
    (by intro x j c a; fin_cases j <;> simp [Function.update, smul_smul, mul_comm]))

@[simp] theorem tangentDetector_pair (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V) (a b : A) :
    tangentDetector ε δ (pair a b) = ε a • δ b := by
  simp [tangentDetector, pair]

theorem tangentDetector_boundaryTwo (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a) :
    (tangentDetector ε δ).comp boundaryTwo = 0 := by
  apply PiTensorProduct.ext
  ext x
  change tangentDetector ε δ (boundaryTwo (PiTensorProduct.tprod ℂ x)) = 0
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]
  change tangentDetector ε δ (boundaryTwo (triple _ _ _)) = 0
  rw [boundaryTwo_triple]
  simp only [map_add, map_sub, tangentDetector_pair, map_mul, hδ, smul_add, mul_smul]
  rw [smul_comm (ε (x 2)) (ε (x 0))]
  abel

/-- The vector detector descends to the actual Hochschild quotient. -/
def hochschildDetector (ε : A →ₐ[ℂ] ℂ) (δ : A →ₗ[ℂ] V)
    (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a) :
    HochschildOne A →ₗ[ℂ] V :=
  (LinearMap.range (boundaryTwo (A := A))).liftQ (tangentDetector ε δ) (by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun (tangentDetector_boundaryTwo ε δ hδ) x)

/-- The class of `1 ⊗ v`. -/
def tangentClass : A →ₗ[ℂ] HochschildOne A :=
  (LinearMap.range (boundaryTwo (A := A))).mkQ.comp (tangentChain (A := A))

@[simp] theorem hochschildDetector_tangentClass (ε : A →ₐ[ℂ] ℂ)
    (δ : A →ₗ[ℂ] V) (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a) (v : A) :
    hochschildDetector ε δ hδ (tangentClass (A := A) v) = δ v := by
  change tangentDetector ε δ (pair 1 v) = δ v
  rw [tangentDetector_pair, map_one, one_smul]

/-- A linear section of a tangent derivation embeds its target in Hochschild degree one. -/
theorem tangentClass_section_injective (ε : A →ₐ[ℂ] ℂ)
    (δ : A →ₗ[ℂ] V) (hδ : ∀ a b, δ (a*b) = ε a • δ b + ε b • δ a)
    (s : V →ₗ[ℂ] A) (hs : ∀ v, δ (s v) = v) :
    Function.Injective ((tangentClass (A := A)).comp s) := by
  intro v w h
  have := congrArg (hochschildDetector ε δ hδ) h
  simpa only [LinearMap.comp_apply, hochschildDetector_tangentClass, hs] using this

/-- A square-zero unit represents its linear tangent class. -/
theorem squareZeroUnit_class (v : A) (hv : v*v=0) :
    (LinearMap.range (boundaryTwo (A := A))).mkQ (pair (1-v) (1+v)) = tangentClass (A := A) v := by
  rw [unit_hochschild_decomposition v hv, map_add]
  have hz : (LinearMap.range (boundaryTwo (A := A))).mkQ
      (boundaryTwo (triple 1 1 1 - triple v 1 1 - (1/2 : ℂ) • triple 1 v v)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [hz, add_zero]
  rfl

#print axioms tangentClass_section_injective
#print axioms squareZeroUnit_class
end GaloisForLFunctions.RHTower.SquareZeroCyclic
