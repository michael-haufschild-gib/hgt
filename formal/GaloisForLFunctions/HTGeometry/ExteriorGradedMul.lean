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

/-- A degree-one factor moves past a factor of degree `q` on the left. -/
theorem ι_mul_exteriorPower (x : M) (z : ⋀[R]^q M) :
    ExteriorAlgebra.ι R x * (z : ExteriorAlgebra R M) =
      ((-1 : R)) ^ q • ((z : ExteriorAlgebra R M) * ExteriorAlgebra.ι R x) := by
  rw [exteriorPower_mul_ι, smul_smul, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- A product of `p` generators commutes with a factor of degree `q` up to the sign `(-1)^{pq}`. -/
theorem ιMulti_mul_comm : ∀ (m : ℕ) (ψ : Fin m → M) {q : ℕ} (z : ⋀[R]^q M),
    ExteriorAlgebra.ιMulti R m ψ * (z : ExteriorAlgebra R M) =
      ((-1 : R)) ^ (m * q) • ((z : ExteriorAlgebra R M) * ExteriorAlgebra.ιMulti R m ψ) := by
  intro m
  induction m with
  | zero =>
      intro ψ q z
      rw [ExteriorAlgebra.ιMulti_zero_apply, one_mul, mul_one, Nat.zero_mul, pow_zero, one_smul]
  | succ k ih =>
      intro ψ q z
      rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, ih (Matrix.vecTail ψ) z, mul_smul_comm,
        ← mul_assoc, ι_mul_exteriorPower, smul_mul_assoc, mul_assoc, smul_smul, ← pow_add,
        ← ExteriorAlgebra.ιMulti_succ_apply]
      congr 1
      congr 1
      ring

/-- **The exterior algebra is graded commutative**: a factor of degree `p` commutes with a factor of
degree `q` up to the sign `(-1)^{pq}`. -/
theorem exteriorPower_mul_comm (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    (y : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M) =
      ((-1 : R)) ^ (p * q) • ((z : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M)) := by
  set F : ⋀[R]^p M →ₗ[R] ExteriorAlgebra R M :=
    (LinearMap.mulRight R (z : ExteriorAlgebra R M)).comp (⋀[R]^p M).subtype with hF
  set G : ⋀[R]^p M →ₗ[R] ExteriorAlgebra R M :=
    ((-1 : R)) ^ (p * q) • ((LinearMap.mulLeft R (z : ExteriorAlgebra R M)).comp
      (⋀[R]^p M).subtype) with hG
  have hgen : ∀ y' ∈ Set.range (exteriorPower.ιMulti R p (M := M)), F y' = G y' := by
    rintro y' ⟨ψ, rfl⟩
    show (exteriorPower.ιMulti R p ψ : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M) =
      ((-1 : R)) ^ (p * q) • ((z : ExteriorAlgebra R M) * (exteriorPower.ιMulti R p ψ : _))
    rw [exteriorPower.ιMulti_apply_coe]
    exact ιMulti_mul_comm p ψ z
  have hFG : F = G := LinearMap.ext_on (exteriorPower.ιMulti_span R p M) hgen
  exact LinearMap.congr_fun hFG y

/-- **The product of exterior powers is graded commutative.** -/
theorem exteriorMulOf_comm {n : ℕ} (h : p + q = n) (h' : q + p = n) (y : ⋀[R]^p M)
    (z : ⋀[R]^q M) :
    exteriorMulOf h y z = ((-1 : R)) ^ (p * q) • exteriorMulOf h' z y := by
  refine Subtype.ext ?_
  rw [exteriorMulOf_coe]
  show (y : ExteriorAlgebra R M) * (z : ExteriorAlgebra R M) =
    ((-1 : R)) ^ (p * q) • (exteriorMulOf h' z y : ExteriorAlgebra R M)
  rw [exteriorMulOf_coe, exteriorPower_mul_comm]

end GradedCommutation

section Functorial

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {p q n : ℕ}

theorem comp_finAppend (f : M →ₗ[R] N) (ψ : Fin p → M) (χ : Fin q → M) :
    (f : M → N) ∘ Fin.append ψ χ = Fin.append ((f : M → N) ∘ ψ) ((f : M → N) ∘ χ) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    show f (Fin.append ψ χ (Fin.castAdd q a)) = Fin.append ((f : M → N) ∘ ψ) _ (Fin.castAdd q a)
    rw [Fin.append_left, Fin.append_left]
    rfl
  · intro a
    show f (Fin.append ψ χ (Fin.natAdd p a)) = Fin.append _ ((f : M → N) ∘ χ) (Fin.natAdd p a)
    rw [Fin.append_right, Fin.append_right]
    rfl

theorem exteriorMulOf_ιMulti (ψ : Fin p → M) (χ : Fin q → M) :
    exteriorMulOf (rfl : p + q = p + q) (exteriorPower.ιMulti R p ψ)
        (exteriorPower.ιMulti R q χ) =
      exteriorPower.ιMulti R (p + q) (Fin.append ψ χ) := by
  refine Subtype.ext ?_
  rw [exteriorMulOf_coe]
  show ExteriorAlgebra.ιMulti R p ψ * ExteriorAlgebra.ιMulti R q χ =
    ExteriorAlgebra.ιMulti R (p + q) (Fin.append ψ χ)
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- **The product of exterior powers is natural**: the exterior power of a linear map is
multiplicative. -/
theorem exteriorMulOf_map (h : p + q = n) (f : M →ₗ[R] N) (y : ⋀[R]^p M) (z : ⋀[R]^q M) :
    exteriorPower.map n f (exteriorMulOf h y z) =
      exteriorMulOf h (exteriorPower.map p f y) (exteriorPower.map q f z) := by
  subst h
  -- both generators
  have hgen : ∀ (ψ : Fin p → M) (χ : Fin q → M),
      exteriorPower.map (p + q) f
          (exteriorMulOf rfl (exteriorPower.ιMulti R p ψ) (exteriorPower.ιMulti R q χ)) =
        exteriorMulOf rfl (exteriorPower.map p f (exteriorPower.ιMulti R p ψ))
          (exteriorPower.map q f (exteriorPower.ιMulti R q χ)) := by
    intro ψ χ
    rw [exteriorMulOf_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
      exteriorPower.map_apply_ιMulti, exteriorMulOf_ιMulti, comp_finAppend]
  -- generator on the left, arbitrary on the right
  have hleft : ∀ (ψ : Fin p → M) (z : ⋀[R]^q M),
      exteriorPower.map (p + q) f
          (exteriorMulOf rfl (exteriorPower.ιMulti R p ψ) z) =
        exteriorMulOf rfl (exteriorPower.map p f (exteriorPower.ιMulti R p ψ))
          (exteriorPower.map q f z) := by
    intro ψ
    set F : ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) N :=
      (exteriorPower.map (p + q) f).comp
        ({ toFun := fun z => exteriorMulOf rfl (exteriorPower.ιMulti R p ψ) z
           map_add' := exteriorMulOf_add_right rfl _
           map_smul' := fun c z => exteriorMulOf_smul_right rfl c _ z } :
          ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) M) with hF
    set G : ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) N :=
      ({ toFun := fun w => exteriorMulOf rfl
           (exteriorPower.map p f (exteriorPower.ιMulti R p ψ)) w
         map_add' := exteriorMulOf_add_right rfl _
         map_smul' := fun c w => exteriorMulOf_smul_right rfl c _ w } :
        ⋀[R]^q N →ₗ[R] ⋀[R]^(p + q) N).comp (exteriorPower.map q f) with hG
    have hFG : F = G :=
      LinearMap.ext_on (exteriorPower.ιMulti_span R q M) (by
        rintro w ⟨χ, rfl⟩
        exact hgen ψ χ)
    exact fun z => LinearMap.congr_fun hFG z
  -- arbitrary on both sides
  set F : ⋀[R]^p M →ₗ[R] ⋀[R]^(p + q) N :=
    (exteriorPower.map (p + q) f).comp
      ({ toFun := fun y => exteriorMulOf rfl y z
         map_add' := fun y y' => exteriorMulOf_add_left rfl y y' z
         map_smul' := fun c y => exteriorMulOf_smul_left rfl c y z } :
        ⋀[R]^p M →ₗ[R] ⋀[R]^(p + q) M) with hF
  set G : ⋀[R]^p M →ₗ[R] ⋀[R]^(p + q) N :=
    ({ toFun := fun u => exteriorMulOf rfl u (exteriorPower.map q f z)
       map_add' := fun u u' => exteriorMulOf_add_left rfl u u' _
       map_smul' := fun c u => exteriorMulOf_smul_left rfl c u _ } :
      ⋀[R]^p N →ₗ[R] ⋀[R]^(p + q) N).comp (exteriorPower.map p f) with hG
  have hFG : F = G :=
    LinearMap.ext_on (exteriorPower.ιMulti_span R p M) (by
      rintro u ⟨ψ, rfl⟩
      exact hleft ψ z)
  exact LinearMap.congr_fun hFG y

end Functorial

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p q n : ℕ}

theorem exteriorMulOf_zero_left' (h : p + q = n) (z : ⋀[R]^q M) :
    exteriorMulOf h (0 : ⋀[R]^p M) z = 0 := by
  have h0 : (0 : ⋀[R]^p M) = (0 : R) • (0 : ⋀[R]^p M) := (zero_smul R _).symm
  rw [h0, exteriorMulOf_smul_left, zero_smul]

theorem exteriorMulOf_zero_right' (h : p + q = n) (y : ⋀[R]^p M) :
    exteriorMulOf h y (0 : ⋀[R]^q M) = 0 := by
  have h0 : (0 : ⋀[R]^q M) = (0 : R) • (0 : ⋀[R]^q M) := (zero_smul R _).symm
  rw [h0, exteriorMulOf_smul_right, zero_smul]

end GaloisForLFunctions.HTGeometry
