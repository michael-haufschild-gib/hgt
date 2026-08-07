import GaloisForLFunctions.HTGeometry.CDGAGround
import GaloisForLFunctions.HTGeometry.CDGAUnital

/-!
# Cochain complexes as differential graded modules

A family of modules with a differential squaring to zero is a differential graded module over any
algebra once the action is taken to be zero: every action axiom is an identity between zero
elements, and the Leibniz rule reads `0 = 0 + ±0`.  The tensor product of two such modules is the
tensor product of the underlying complexes, with the Koszul sign, so every construction stated for
modules over an algebra applies to plain cochain complexes.

* `HTGeometry.zeroComplexModule` : a cochain complex as a module with zero action.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- **A cochain complex is a differential graded module with zero action.** -/
def zeroComplexModule (A : CDGAStructure R X) (d : ∀ n : ℕ, M n →ₗ[R] M (n + 1))
    (hdd : ∀ (n : ℕ) (m : M n), d (n + 1) (d n m) = 0) : CDGAModuleStructure A M where
  act _ _ _ := 0
  d n m := d n m
  act_add_left _ _ _ _ := (add_zero (0 : M _)).symm
  act_add_right _ _ _ _ := (add_zero (0 : M _)).symm
  act_smul_left _ _ _ _ := (smul_zero _).symm
  act_smul_right _ _ _ _ := (smul_zero _).symm
  act_assoc _ _ _ _ _ _ _ := rfl
  d_add n m m' := (d n).map_add m m'
  d_smul n c m := (d n).map_smul c m
  d_d n m := hdd n m
  d_act _ _ _ := by
    show (d _) 0 = (0 : M _) + ((-1 : R)) ^ _ • (0 : M _)
    rw [map_zero, smul_zero, add_zero]

@[simp] theorem zeroComplexModule_act (A : CDGAStructure R X) (d : ∀ n : ℕ, M n →ₗ[R] M (n + 1))
    (hdd : ∀ (n : ℕ) (m : M n), d (n + 1) (d n m) = 0) {a b n : ℕ} (h : a + b = n) (x : X a)
    (m : M b) : (zeroComplexModule A d hdd).act h x m = 0 := rfl

@[simp] theorem zeroComplexModule_d (A : CDGAStructure R X) (d : ∀ n : ℕ, M n →ₗ[R] M (n + 1))
    (hdd : ∀ (n : ℕ) (m : M n), d (n + 1) (d n m) = 0) (n : ℕ) (m : M n) :
    (zeroComplexModule A d hdd).d n m = d n m := rfl

end GaloisForLFunctions.HTGeometry
