import GaloisForLFunctions.HTGeometry.CDGAUnital
import Mathlib.Algebra.DirectSum.Algebra

/-!
# The total algebra of a unital commutative differential graded algebra

Summing the degrees of a unital commutative differential graded algebra gives an associative unital
`R`-algebra: the graded product is bilinear, associative and unital, so the family is a graded ring
in the sense of direct sums.  It is not a commutative ring — the product is commutative only up to
the Koszul sign — but that is irrelevant for its use as a receptacle for universal properties of
algebras.

The family is carried by a type synonym so that the algebra and its unit are visible to instance
resolution.

* `CDGATotalCarrier` : the degrees of a unital algebra, as a family instance resolution can see.
* `CDGATotal` : the direct sum of the degrees, a ring and an `R`-algebra.
* `cdgaTotalOf` : the inclusion of a degree.
-/

universe u v

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)]

/-- The product does not depend on the proof identifying the target degree: transporting along the
identification is the same as using it in the product. -/
theorem CDGAStructure.mul_eq_rec (A : CDGAStructure R X) {a b n : ℕ} (h : a + b = n) (x : X a)
    (y : X b) : A.mul h x y = h ▸ A.mul rfl x y := by
  cases h
  rfl

/-- The degrees of a unital commutative differential graded algebra, as a family that instance
resolution can see the algebra and the unit in. -/
def CDGATotalCarrier (A : CDGAStructure R X) (_u : CDGAUnit A) (n : ℕ) : Type v := X n

namespace CDGATotalCarrier

variable {A : CDGAStructure R X} {u : CDGAUnit A}

instance (n : ℕ) : AddCommGroup (CDGATotalCarrier A u n) := inferInstanceAs (AddCommGroup (X n))

instance (n : ℕ) : Module R (CDGATotalCarrier A u n) := inferInstanceAs (Module R (X n))

instance : GradedMonoid.GOne (CDGATotalCarrier A u) where
  one := u.one

instance : GradedMonoid.GMul (CDGATotalCarrier A u) where
  mul {_ _} x y := A.mul rfl x y

theorem gMul_def {i j : ℕ} (x : CDGATotalCarrier A u i) (y : CDGATotalCarrier A u j) :
    GradedMonoid.GMul.mul x y = A.mul rfl x y := rfl

theorem gOne_def : (GradedMonoid.GOne.one : CDGATotalCarrier A u 0) = u.one := rfl

instance : DirectSum.GNonUnitalNonAssocSemiring (CDGATotalCarrier A u) where
  mul_zero {i j} x := by
    show A.mul rfl (x : X i) (0 : X j) = 0
    have h0 : (0 : X j) = (0 : R) • (0 : X j) := (zero_smul R _).symm
    rw [h0, A.mul_smul_right, zero_smul]
  zero_mul {i j} y := by
    show A.mul rfl (0 : X i) (y : X j) = 0
    have h0 : (0 : X i) = (0 : R) • (0 : X i) := (zero_smul R _).symm
    rw [h0, A.mul_smul_left, zero_smul]
  mul_add {i j} x y z := A.mul_add_right rfl (x : X i) (y : X j) z
  add_mul {i j} x y z := A.mul_add_left rfl (x : X i) (y : X i) (z : X j)

/-- Transporting twice along an identification and its inverse changes nothing. -/
theorem rec_rec_symm {i j : ℕ} (h : i = j) (y : CDGATotalCarrier A u j) :
    h ▸ (h.symm ▸ y : CDGATotalCarrier A u i) = y := by
  cases h
  rfl

/-- Two graded elements agree when their degrees do and the transported values do. -/
theorem gradedMonoid_mk_eq {i j : ℕ} (h : i = j) (x : CDGATotalCarrier A u i)
    (y : CDGATotalCarrier A u j) (hxy : h ▸ x = y) :
    GradedMonoid.mk i x = GradedMonoid.mk j y := by
  cases h
  cases hxy
  rfl

instance : GradedMonoid.GMonoid (CDGATotalCarrier A u) where
  one_mul a := by
    obtain ⟨i, x⟩ := a
    refine gradedMonoid_mk_eq (Nat.zero_add i) _ _ ?_
    exact (A.mul_eq_rec (Nat.zero_add i) u.one x).symm.trans (u.one_mul i x)
  mul_one a := by
    obtain ⟨i, x⟩ := a
    refine gradedMonoid_mk_eq (Nat.add_zero i) _ _ ?_
    exact (A.mul_eq_rec (Nat.add_zero i) x u.one).symm.trans (u.mul_one i x)
  mul_assoc a b c := by
    obtain ⟨i, x⟩ := a
    obtain ⟨j, y⟩ := b
    obtain ⟨k, z⟩ := c
    refine gradedMonoid_mk_eq (Nat.add_assoc i j k) _ _ ?_
    have hstep : A.mul rfl (A.mul rfl x y) z
        = (Nat.add_assoc i j k).symm ▸ A.mul rfl x (A.mul rfl y z) := by
      rw [A.mul_assoc rfl rfl rfl (Nat.add_assoc i j k).symm x y z]
      exact A.mul_eq_rec (Nat.add_assoc i j k).symm x (A.mul rfl y z)
    show (Nat.add_assoc i j k) ▸ A.mul rfl (A.mul rfl x y) z = _
    rw [hstep]
    exact rec_rec_symm (A := A) (u := u) (Nat.add_assoc i j k)
      (A.mul rfl x (A.mul rfl y z) : CDGATotalCarrier A u (i + (j + k)))

instance : DirectSum.GSemiring (CDGATotalCarrier A u) where
  natCast n := n • u.one
  natCast_zero := zero_smul ℕ u.one
  natCast_succ n := succ_nsmul u.one n

instance : DirectSum.GRing (CDGATotalCarrier A u) where
  intCast n := n • u.one
  intCast_ofNat n := natCast_zsmul u.one n
  intCast_negSucc_ofNat n := by
    show (Int.negSucc n) • u.one = -((n + 1) • u.one)
    rw [negSucc_zsmul]

/-- Scaling both sides of an equality of graded elements. -/
theorem gradedMonoid_smul_congr {i j : ℕ} {x : CDGATotalCarrier A u i}
    {y : CDGATotalCarrier A u j} (h : GradedMonoid.mk i x = GradedMonoid.mk j y) (r : R) :
    GradedMonoid.mk i (r • x) = GradedMonoid.mk j (r • y) := by
  injection h with h1 h2
  cases h1
  cases eq_of_heq h2
  rfl

instance : DirectSum.GAlgebra R (CDGATotalCarrier A u) where
  toFun :=
    { toFun := fun r => r • u.one
      map_zero' := zero_smul R u.one
      map_add' := fun r s => add_smul r s u.one }
  map_one := one_smul R u.one
  map_mul r s := by
    show GradedMonoid.mk 0 (((r * s) • u.one : X 0))
      = GradedMonoid.mk (0 + 0) (A.mul rfl (r • u.one) (s • u.one))
    have hsm : (A.mul rfl (r • u.one) (s • u.one) : X (0 + 0))
        = (r * s) • A.mul rfl u.one u.one := by
      rw [A.mul_smul_left, A.mul_smul_right, smul_smul]
    rw [hsm]
    exact (gradedMonoid_smul_congr
      (GradedMonoid.GMonoid.one_mul (⟨0, u.one⟩ : GradedMonoid (CDGATotalCarrier A u)))
      (r * s)).symm
  commutes r x := by
    obtain ⟨i, y⟩ := x
    show GradedMonoid.mk (0 + i) (A.mul rfl (r • u.one) y)
      = GradedMonoid.mk (i + 0) (A.mul rfl y (r • u.one))
    have hL : (A.mul rfl (r • u.one) y : X (0 + i)) = r • A.mul rfl u.one y :=
      A.mul_smul_left rfl r u.one y
    have hR : (A.mul rfl y (r • u.one) : X (i + 0)) = r • A.mul rfl y u.one :=
      A.mul_smul_right rfl r y u.one
    rw [hL, hR]
    refine Eq.trans ?_ (gradedMonoid_smul_congr
      (GradedMonoid.GMonoid.mul_one (⟨i, y⟩ : GradedMonoid (CDGATotalCarrier A u))) r).symm
    exact gradedMonoid_smul_congr
      (GradedMonoid.GMonoid.one_mul (⟨i, y⟩ : GradedMonoid (CDGATotalCarrier A u))) r
  smul_def r x := by
    obtain ⟨i, y⟩ := x
    show GradedMonoid.mk i ((r • y : X i))
      = GradedMonoid.mk (0 + i) (A.mul rfl (r • u.one) y)
    have hsm : (A.mul rfl (r • u.one) y : X (0 + i)) = r • A.mul rfl u.one y :=
      A.mul_smul_left rfl r u.one y
    rw [hsm]
    exact (gradedMonoid_smul_congr
      (GradedMonoid.GMonoid.one_mul (⟨i, y⟩ : GradedMonoid (CDGATotalCarrier A u))) r).symm

end CDGATotalCarrier

open CDGATotalCarrier

/-- **The total algebra of a unital commutative differential graded algebra**: the direct sum of its
degrees, an associative unital `R`-algebra. -/
abbrev CDGATotal (A : CDGAStructure R X) (u : CDGAUnit A) : Type v :=
  DirectSum ℕ (CDGATotalCarrier A u)

/-- The inclusion of a degree into the total algebra. -/
noncomputable def cdgaTotalOf (A : CDGAStructure R X) (u : CDGAUnit A) (n : ℕ) :
    X n →ₗ[R] CDGATotal A u :=
  DirectSum.lof R ℕ (CDGATotalCarrier A u) n

@[simp] theorem cdgaTotalOf_apply (A : CDGAStructure R X) (u : CDGAUnit A) (n : ℕ) (x : X n) :
    cdgaTotalOf A u n x = DirectSum.of (CDGATotalCarrier A u) n x := rfl

/-- **The inclusion turns the graded product into the product of the total algebra.** -/
theorem cdgaTotalOf_mul (A : CDGAStructure R X) (u : CDGAUnit A) {a b : ℕ} (x : X a) (y : X b) :
    cdgaTotalOf A u a x * cdgaTotalOf A u b y = cdgaTotalOf A u (a + b) (A.mul rfl x y) :=
  DirectSum.of_mul_of (A := CDGATotalCarrier A u) x y

/-- The unit of the total algebra is the unit of the algebra in degree zero. -/
theorem cdgaTotalOf_one (A : CDGAStructure R X) (u : CDGAUnit A) :
    cdgaTotalOf A u 0 u.one = 1 := rfl

end GaloisForLFunctions.HTGeometry
