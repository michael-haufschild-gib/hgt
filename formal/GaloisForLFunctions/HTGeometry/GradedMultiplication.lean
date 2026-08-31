import GaloisForLFunctions.HTGeometry.GradedComplement

/-!
# Multiplication between graded pieces

```text
mulDegreeHom      multiplication by a homogeneous polynomial, as a map of graded pieces
quotDegreePart    the quotient of a graded piece by the corresponding piece of a subspace
```

These are the objects the Hilbert-function criterion is about: in each degree, multiplication by a
linear form is a map from one graded piece of the quotient ring to the next, its cokernel is the
corresponding piece of the ring modulo the form, and the form is a nonzerodivisor exactly when every
one of these maps is injective.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- Multiplication by a homogeneous polynomial, as a map of graded pieces. -/
noncomputable def mulDegreeHom {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (e : ℕ) :
    (homogeneousSubmodule σ K e) →ₗ[K] (homogeneousSubmodule σ K (d + e)) where
  toFun x := ⟨l * (x : MvPolynomial σ K), hl.mul x.2⟩
  map_add' x y := by
    refine Subtype.ext ?_
    show l * ((x : MvPolynomial σ K) + y) = l * x + l * y
    ring
  map_smul' c x := by
    refine Subtype.ext ?_
    show l * (c • (x : MvPolynomial σ K)) = c • (l * (x : MvPolynomial σ K))
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
    ring

theorem mulDegreeHom_apply {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (e : ℕ)
    (x : homogeneousSubmodule σ K e) :
    ((mulDegreeHom hl e x : homogeneousSubmodule σ K (d + e)) : MvPolynomial σ K)
      = l * (x : MvPolynomial σ K) := rfl

/-- The quotient of a graded piece by the corresponding piece of a subspace. -/
noncomputable abbrev quotDegreePart (a : Submodule K (MvPolynomial σ K)) (e : ℕ) :=
  (homogeneousSubmodule σ K e) ⧸ (degreePart a e)

end GaloisForLFunctions.HTGeometry
