import GaloisForLFunctions.HTGeometry.FormWedge

/-!
# The graded multiplication of exterior powers

The exterior powers of a module sit inside its exterior algebra, so multiplying them multiplies the
degrees.  The resulting product is bilinear and associative, and a factor of degree one moves past a
factor of degree `p` at the cost of the sign `(-1)^p`, because the generators anticommute.  These are
the algebraic identities behind the Leibniz rule for the exterior derivative.

* `exteriorMulOf` : the product of exterior powers, in the degree prescribed by an equation.
* `exteriorMulOf_assoc` : associativity.
* `exteriorPower_mul_ι` : a degree-one factor moves past a factor of degree `p` with the sign
  `(-1)^p`.
* `mulOf_consMul_right` : the resulting commutation of the wedge with a one-form.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open exteriorPower

section GradedMul

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p q n : ℕ}

/-- A vector as an element of the first exterior power. -/
def exteriorι (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    ⋀[R]^1 M :=
  ⟨ExteriorAlgebra.ι R x, ι_mem_exteriorPower_one x⟩

@[simp]
theorem exteriorι_coe (x : M) :
    (exteriorι R x : ExteriorAlgebra R M) = ExteriorAlgebra.ι R x := rfl

/-- **The product of exterior powers**, landing in the degree prescribed by an equation. -/
def exteriorMulOf (h : p + q = n) (y : ⋀[R]^p M) (z : ⋀[R]^q M) : ⋀[R]^n M :=
  ⟨(y : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M), by
    rw [← h]
    exact SetLike.mul_mem_graded y.2 z.2⟩

@[simp]
theorem exteriorMulOf_coe (h : p + q = n) (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    (exteriorMulOf h y z : ExteriorAlgebra R M) =
      (y : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M) := rfl

theorem exteriorMulOf_add_left (h : p + q = n) (y y' : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorMulOf h (y + y') z = exteriorMulOf h y z + exteriorMulOf h y' z := by
  refine Subtype.ext ?_
  show ((y : ExteriorAlgebra R M) + y') * z =
    (exteriorMulOf h y z : ExteriorAlgebra R M) + (exteriorMulOf h y' z : ExteriorAlgebra R M)
  rw [exteriorMulOf_coe, exteriorMulOf_coe, add_mul]

theorem exteriorMulOf_add_right (h : p + q = n) (y : ⋀[R]^p M) (z z' : ⋀[R]^q M) :
    exteriorMulOf h y (z + z') = exteriorMulOf h y z + exteriorMulOf h y z' := by
  refine Subtype.ext ?_
  show (y : ExteriorAlgebra R M) * ((z : ExteriorAlgebra R M) + z') =
    (exteriorMulOf h y z : ExteriorAlgebra R M) + (exteriorMulOf h y z' : ExteriorAlgebra R M)
  rw [exteriorMulOf_coe, exteriorMulOf_coe, mul_add]

theorem exteriorMulOf_smul_left (h : p + q = n) (c : R) (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorMulOf h (c • y) z = c • exteriorMulOf h y z := by
  refine Subtype.ext ?_
  show (c • (y : ExteriorAlgebra R M)) * z = c • (exteriorMulOf h y z : ExteriorAlgebra R M)
  rw [exteriorMulOf_coe, smul_mul_assoc]

theorem exteriorMulOf_smul_right (h : p + q = n) (c : R) (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorMulOf h y (c • z) = c • exteriorMulOf h y z := by
  refine Subtype.ext ?_
  show (y : ExteriorAlgebra R M) * (c • (z : ExteriorAlgebra R M)) =
    c • (exteriorMulOf h y z : ExteriorAlgebra R M)
  rw [exteriorMulOf_coe, mul_smul_comm]

theorem exteriorMulOf_assoc {m k : ℕ} (h₁ : p + q = m) (h₂ : m + k = n) (h₃ : q + k = m')
    (h₄ : p + m' = n) (y : ⋀[R]^p M) (z : ⋀[R]^q M) (w : ⋀[R]^k M) :
    exteriorMulOf h₂ (exteriorMulOf h₁ y z) w = exteriorMulOf h₄ y (exteriorMulOf h₃ z w) := by
  refine Subtype.ext ?_
  show ((y : ExteriorAlgebra R M) * z) * w = (y : ExteriorAlgebra R M) * ((z : _) * w)
  rw [mul_assoc]

/-- Multiplication by a vector on the left is the product with its class in degree one. -/
theorem exteriorConsMul_eq_mulOf (x : M) (y : ⋀[R]^q M) :
    exteriorConsMul x y = exteriorMulOf (Nat.add_comm 1 q) (exteriorι R x) y := rfl

theorem exteriorConsMul_add_left (x x' : M) (y : ⋀[R]^q M) :
    exteriorConsMul (x + x') y = exteriorConsMul x y + exteriorConsMul x' y := by
  refine Subtype.ext ?_
  rw [exteriorConsMul_coe, map_add]
  show (ExteriorAlgebra.ι R x + ExteriorAlgebra.ι R x') * (y : ExteriorAlgebra R M) =
    (exteriorConsMul x y : ExteriorAlgebra R M) + (exteriorConsMul x' y : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, exteriorConsMul_coe, add_mul]

theorem exteriorConsMul_smul_left (c : R) (x : M) (y : ⋀[R]^q M) :
    exteriorConsMul (c • x) y = c • exteriorConsMul x y := by
  refine Subtype.ext ?_
  rw [exteriorConsMul_coe, map_smul]
  show (c • ExteriorAlgebra.ι R x) * (y : ExteriorAlgebra R M) =
    c • (exteriorConsMul x y : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, smul_mul_assoc]

/-- Wedging with a one-form on the left commutes with multiplication on the right. -/
theorem exteriorConsMul_mulOf (h : p + q = n) (h' : p + 1 + q = n + 1) (x : M)
    (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorMulOf h' (exteriorConsMul x y) z = exteriorConsMul x (exteriorMulOf h y z) := by
  refine Subtype.ext ?_
  show ((exteriorConsMul x y : ExteriorAlgebra R M)) * z =
    (exteriorConsMul x (exteriorMulOf h y z) : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, exteriorConsMul_coe, exteriorMulOf_coe, mul_assoc]

end GradedMul

section GradedCommutation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p q n : ℕ}

/-- The generators of the exterior algebra anticommute. -/
theorem ι_mul_ι_neg (x y : M) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y =
      -(ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R x) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x y)

/-- A product of `p` generators moves past one more generator with the sign `(-1)^p`. -/
theorem ιMulti_mul_ι : ∀ (m : ℕ) (ψ : Fin m → M) (x : M),
    ExteriorAlgebra.ιMulti R m ψ * ExteriorAlgebra.ι R x =
      ((-1 : R)) ^ m • (ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R m ψ) := by
  intro m
  induction m with
  | zero =>
      intro ψ x
      rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul, mul_one, pow_zero, one_smul]
  | succ k ih =>
      intro ψ x
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, ih (Matrix.vecTail ψ) x,
        mul_smul_comm, ← mul_assoc, ι_mul_ι_neg, neg_mul, mul_assoc, smul_neg, ← neg_smul,
        ← ExteriorAlgebra.ιMulti_succ_apply]
      congr 1
      rw [pow_succ]
      ring

/-- **A factor of degree `p` moves past a factor of degree one** at the cost of the sign
`(-1)^p`. -/
theorem exteriorPower_mul_ι (y : ⋀[R]^p M) (x : M) :
    (y : ExteriorAlgebra R M) * ExteriorAlgebra.ι R x =
      ((-1 : R)) ^ p • (ExteriorAlgebra.ι R x * (y : ExteriorAlgebra R M)) := by
  set F : ⋀[R]^p M →ₗ[R] ExteriorAlgebra R M :=
    (LinearMap.mulRight R (ExteriorAlgebra.ι R x)).comp (⋀[R]^p M).subtype with hF
  set G : ⋀[R]^p M →ₗ[R] ExteriorAlgebra R M :=
    ((-1 : R)) ^ p • ((LinearMap.mulLeft R (ExteriorAlgebra.ι R x)).comp
      (⋀[R]^p M).subtype) with hG
  have hgen : ∀ z ∈ Set.range (exteriorPower.ιMulti R p (M := M)), F z = G z := by
    rintro z ⟨ψ, rfl⟩
    show (exteriorPower.ιMulti R p ψ : ExteriorAlgebra R M) * ExteriorAlgebra.ι R x =
      ((-1 : R)) ^ p • (ExteriorAlgebra.ι R x * (exteriorPower.ιMulti R p ψ : _))
    rw [exteriorPower.ιMulti_apply_coe]
    exact ιMulti_mul_ι p ψ x
  have hFG : F = G := LinearMap.ext_on (exteriorPower.ιMulti_span R p M) hgen
  exact LinearMap.congr_fun hFG y

/-- **Wedging with a one-form on the right** is wedging on the left with the sign `(-1)^p`. -/
theorem mulOf_consMul_right (h : p + q = n) (h' : p + (q + 1) = n + 1) (x : M)
    (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorMulOf h' y (exteriorConsMul x z) =
      ((-1 : R)) ^ p • exteriorConsMul x (exteriorMulOf h y z) := by
  refine Subtype.ext ?_
  show (y : ExteriorAlgebra R M) * (exteriorConsMul x z : ExteriorAlgebra R M) =
    ((-1 : R)) ^ p • (exteriorConsMul x (exteriorMulOf h y z) : ExteriorAlgebra R M)
  rw [exteriorConsMul_coe, exteriorConsMul_coe, exteriorMulOf_coe, ← mul_assoc,
    exteriorPower_mul_ι, smul_mul_assoc, mul_assoc]

end GradedCommutation

end GaloisForLFunctions.HTGeometry
