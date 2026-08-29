import GaloisForLFunctions.HTGeometry.DifferenceTensorTorsor

/-!
# The cocycle identity for the torsor comparison matrix

Inside the triple tensor product the three copies of an invertible fundamental solution matrix are
compared pairwise by the comparison matrix, and the three comparisons satisfy

```
    Z₁₃ = Z₁₂ · Z₂₃ ,
```

because `Y₁ Z₁₂ = Y₂`, `Y₂ Z₂₃ = Y₃` and `Y₁ Z₁₃ = Y₃`, and `Y₁` is invertible.  This is the group
law of the difference Galois group: it is what makes the functor of points of the comparison matrix
a monoid over *every* base algebra, not only over the field of constants.

* `tensor12`, `tensor23`, `tensor13` — the three inclusions of the tensor square;
* `torsor_cocycle` — **the identity.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]

/-- The inclusion of the tensor square into the first two factors of the triple tensor product. -/
def tensor12 : (R ⊗[K] R) →ₐ[K] ((R ⊗[K] R) ⊗[K] R) :=
  Algebra.TensorProduct.includeLeft

/-- The inclusion of the tensor square into the last two factors of the triple tensor product. -/
def tensor23 : (R ⊗[K] R) →ₐ[K] ((R ⊗[K] R) ⊗[K] R) :=
  Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : R →ₐ[K] R ⊗[K] R)
    (AlgHom.id K R)

/-- The inclusion of the tensor square into the outer two factors of the triple tensor product. -/
def tensor13 : (R ⊗[K] R) →ₐ[K] ((R ⊗[K] R) ⊗[K] R) :=
  Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R)
    (AlgHom.id K R)

variable {K R}

@[simp] theorem tensor12_tmul (a b : R) :
    tensor12 K R (a ⊗ₜ[K] b) = (a ⊗ₜ[K] b) ⊗ₜ[K] (1 : R) := rfl

@[simp] theorem tensor23_tmul (a b : R) :
    tensor23 K R (a ⊗ₜ[K] b) = ((1 : R) ⊗ₜ[K] a) ⊗ₜ[K] b := rfl

@[simp] theorem tensor13_tmul (a b : R) :
    tensor13 K R (a ⊗ₜ[K] b) = (a ⊗ₜ[K] (1 : R)) ⊗ₜ[K] b := rfl

variable {n : ℕ}

/-- The three copies of the fundamental matrix inside the triple tensor product. -/
def tripleFundamental₁ (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) ((R ⊗[K] R) ⊗[K] R) :=
  Y.map fun a => (a ⊗ₜ[K] (1 : R)) ⊗ₜ[K] (1 : R)

def tripleFundamental₂ (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) ((R ⊗[K] R) ⊗[K] R) :=
  Y.map fun a => ((1 : R) ⊗ₜ[K] a) ⊗ₜ[K] (1 : R)

def tripleFundamental₃ (Y : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) ((R ⊗[K] R) ⊗[K] R) :=
  Y.map fun a => ((1 : R) ⊗ₜ[K] (1 : R)) ⊗ₜ[K] a

theorem map_leftFundamental_tensor12 (Y : Matrix (Fin n) (Fin n) R) :
    (leftFundamental K Y).map (tensor12 K R) = tripleFundamental₁ (K := K) Y := rfl

theorem map_rightFundamental_tensor12 (Y : Matrix (Fin n) (Fin n) R) :
    (rightFundamental K Y).map (tensor12 K R) = tripleFundamental₂ (K := K) Y := rfl

theorem map_leftFundamental_tensor23 (Y : Matrix (Fin n) (Fin n) R) :
    (leftFundamental K Y).map (tensor23 K R) = tripleFundamental₂ (K := K) Y := rfl

theorem map_rightFundamental_tensor23 (Y : Matrix (Fin n) (Fin n) R) :
    (rightFundamental K Y).map (tensor23 K R) = tripleFundamental₃ (K := K) Y := rfl

theorem map_leftFundamental_tensor13 (Y : Matrix (Fin n) (Fin n) R) :
    (leftFundamental K Y).map (tensor13 K R) = tripleFundamental₁ (K := K) Y := rfl

theorem map_rightFundamental_tensor13 (Y : Matrix (Fin n) (Fin n) R) :
    (rightFundamental K Y).map (tensor13 K R) = tripleFundamental₃ (K := K) Y := rfl

/-- **The cocycle identity.**  Inside the triple tensor product the comparison matrix satisfies the
group law `Z₁₃ = Z₁₂ · Z₂₃`. -/
theorem torsor_cocycle (Y : Matrix (Fin n) (Fin n) R) (hY : IsUnit Y.det)
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R))
    (hZ : leftFundamental K Y * Z = rightFundamental K Y) :
    Z.map (tensor13 K R) = Z.map (tensor12 K R) * Z.map (tensor23 K R) := by
  have h12 : tripleFundamental₁ (K := K) Y * Z.map (tensor12 K R)
      = tripleFundamental₂ (K := K) Y := by
    rw [← map_leftFundamental_tensor12, ← map_rightFundamental_tensor12, ← Matrix.map_mul, hZ]
  have h23 : tripleFundamental₂ (K := K) Y * Z.map (tensor23 K R)
      = tripleFundamental₃ (K := K) Y := by
    rw [← map_leftFundamental_tensor23, ← map_rightFundamental_tensor23, ← Matrix.map_mul, hZ]
  have h13 : tripleFundamental₁ (K := K) Y * Z.map (tensor13 K R)
      = tripleFundamental₃ (K := K) Y := by
    rw [← map_leftFundamental_tensor13, ← map_rightFundamental_tensor13, ← Matrix.map_mul, hZ]
  set φ : R →ₐ[K] ((R ⊗[K] R) ⊗[K] R) :=
    (Algebra.TensorProduct.includeLeft : (R ⊗[K] R) →ₐ[K] ((R ⊗[K] R) ⊗[K] R)).comp
      (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R) with hφ
  have hY1 : IsUnit (tripleFundamental₁ (K := K) Y).det := by
    have hmap : (tripleFundamental₁ (K := K) Y).det = φ Y.det :=
      (RingHom.map_det (φ : R →+* ((R ⊗[K] R) ⊗[K] R)) Y).symm
    rw [hmap]
    exact hY.map φ
  have hchain : tripleFundamental₁ (K := K) Y * (Z.map (tensor12 K R) * Z.map (tensor23 K R))
      = tripleFundamental₁ (K := K) Y * Z.map (tensor13 K R) := by
    rw [← Matrix.mul_assoc, h12, h23, h13]
  haveI : Invertible (tripleFundamental₁ (K := K) Y) :=
    Matrix.invertibleOfIsUnitDet _ hY1
  have hcancel := congrArg
    (fun X : Matrix (Fin n) (Fin n) ((R ⊗[K] R) ⊗[K] R) =>
      ⅟(tripleFundamental₁ (K := K) Y) * X) hchain
  simp only [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul] at hcancel
  exact hcancel.symm

end

end GaloisForLFunctions.HTGeometry
