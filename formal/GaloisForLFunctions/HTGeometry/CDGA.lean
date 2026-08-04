import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Linarith

/-!
# Commutative differential graded algebras

A commutative differential graded algebra over a commutative ring is a family of modules indexed by
the nonnegative degrees, with a bilinear associative graded commutative product that adds degrees
and a differential raising the degree by one, squaring to zero and satisfying the Leibniz rule.  Its
cohomology in each degree is the cocycles modulo the coboundaries, a morphism induces a map on
cohomology, and a quasi-isomorphism is a morphism inducing isomorphisms in every degree.  Mathlib has
graded algebras and homological complexes but no such structure.

The family of modules is a parameter rather than a field, so that the coercions of a concrete
algebra stay at the concrete types.

* `CDGAStructure` : the structure.
* `CDGAStructure.cohomology` : the cohomology in a degree.
* `CDGAHom`, `CDGAHom.cohomologyMap` : morphisms and the induced map.
* `CDGAHom.IsQuasiIso` : a morphism inducing isomorphisms on cohomology.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

/-- **A commutative differential graded algebra** over a commutative ring, in nonnegative degrees,
on a given family of modules. -/
structure CDGAStructure (R : Type u) [CommRing R] (X : ℕ → Type v)
    [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)] where
  /-- The product, adding degrees. -/
  mul : ∀ {a b n : ℕ}, a + b = n → X a → X b → X n
  /-- The differential, raising the degree by one. -/
  d : ∀ n : ℕ, X n → X (n + 1)
  mul_add_left : ∀ {a b n : ℕ} (h : a + b = n) (x x' : X a) (y : X b),
    mul h (x + x') y = mul h x y + mul h x' y
  mul_add_right : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (y y' : X b),
    mul h x (y + y') = mul h x y + mul h x y'
  mul_smul_left : ∀ {a b n : ℕ} (h : a + b = n) (c : R) (x : X a) (y : X b),
    mul h (c • x) y = c • mul h x y
  mul_smul_right : ∀ {a b n : ℕ} (h : a + b = n) (c : R) (x : X a) (y : X b),
    mul h x (c • y) = c • mul h x y
  mul_assoc : ∀ {a b k m m' n : ℕ} (h₁ : a + b = m) (h₂ : m + k = n) (h₃ : b + k = m')
    (h₄ : a + m' = n) (x : X a) (y : X b) (z : X k),
    mul h₂ (mul h₁ x y) z = mul h₄ x (mul h₃ y z)
  mul_comm : ∀ {a b n : ℕ} (h : a + b = n) (h' : b + a = n) (x : X a) (y : X b),
    mul h x y = ((-1 : R)) ^ (a * b) • mul h' y x
  d_add : ∀ (n : ℕ) (x y : X n), d n (x + y) = d n x + d n y
  d_smul : ∀ (n : ℕ) (c : R) (x : X n), d n (c • x) = c • d n x
  d_d : ∀ (n : ℕ) (x : X n), d (n + 1) (d n x) = 0
  d_mul : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (y : X b),
    d n (mul h x y) = mul (show a + 1 + b = n + 1 by omega) (d a x) y +
      ((-1 : R)) ^ a • mul (show a + (b + 1) = n + 1 by omega) x (d b y)

namespace CDGAStructure

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] (A : CDGAStructure R X)

/-- The product as a bilinear map. -/
def mulₗ {a b n : ℕ} (h : a + b = n) : X a →ₗ[R] X b →ₗ[R] X n where
  toFun x :=
    { toFun := fun y => A.mul h x y
      map_add' := A.mul_add_right h x
      map_smul' := fun c y => A.mul_smul_right h c x y }
  map_add' x x' := LinearMap.ext fun y => A.mul_add_left h x x' y
  map_smul' c x := LinearMap.ext fun y => A.mul_smul_left h c x y

@[simp]
theorem mulₗ_apply {a b n : ℕ} (h : a + b = n) (x : X a) (y : X b) :
    A.mulₗ h x y = A.mul h x y := rfl

/-- The differential as a linear map. -/
def dₗ (n : ℕ) : X n →ₗ[R] X (n + 1) where
  toFun := A.d n
  map_add' := A.d_add n
  map_smul' c x := A.d_smul n c x

@[simp]
theorem dₗ_apply (n : ℕ) (x : X n) : A.dₗ n x = A.d n x := rfl

/-- **The cocycles of a given degree**: the elements killed by the differential. -/
def cocycles (n : ℕ) : Submodule R (X n) := LinearMap.ker (A.dₗ n)

theorem mem_cocycles {n : ℕ} {x : X n} : x ∈ A.cocycles n ↔ A.d n x = 0 := Iff.rfl

/-- **The coboundaries inside the cocycles of degree `n + 1`.** -/
def coboundaries (n : ℕ) : Submodule R (A.cocycles (n + 1)) where
  carrier := {x | ∃ y : X n, (x : X (n + 1)) = A.d n y}
  zero_mem' := ⟨0, by rw [show A.d n 0 = 0 from (A.dₗ n).map_zero]; rfl⟩
  add_mem' := by
    rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
    refine ⟨y + y', ?_⟩
    show (x : X (n + 1)) + (x' : X (n + 1)) = A.d n (y + y')
    rw [A.d_add, hy, hy']
  smul_mem' := by
    rintro c x ⟨y, hy⟩
    refine ⟨c • y, ?_⟩
    show c • (x : X (n + 1)) = A.d n (c • y)
    rw [A.d_smul, hy]

theorem mem_coboundaries {n : ℕ} {x : A.cocycles (n + 1)} :
    x ∈ A.coboundaries n ↔ ∃ y : X n, (x : X (n + 1)) = A.d n y := Iff.rfl

/-- **The cohomology of a commutative differential graded algebra** in a degree. -/
abbrev cohomology (n : ℕ) := (↥(A.cocycles (n + 1))) ⧸ (A.coboundaries n)

end CDGAStructure

/-- **A morphism of commutative differential graded algebras**: a degree-wise linear map commuting
with the product and the differential. -/
structure CDGAHom {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
    [∀ n, Module R (X n)] {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
    (A : CDGAStructure R X) (B : CDGAStructure R Y) where
  /-- The map in each degree. -/
  toFun : ∀ n : ℕ, X n → Y n
  map_add : ∀ (n : ℕ) (x y : X n), toFun n (x + y) = toFun n x + toFun n y
  map_smul : ∀ (n : ℕ) (c : R) (x : X n), toFun n (c • x) = c • toFun n x
  map_mul : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (y : X b),
    toFun n (A.mul h x y) = B.mul h (toFun a x) (toFun b y)
  map_d : ∀ (n : ℕ) (x : X n), toFun (n + 1) (A.d n x) = B.d n (toFun n x)

namespace CDGAHom

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {A : CDGAStructure R X} {B : CDGAStructure R Y} (φ : CDGAHom A B)

/-- The map of a morphism in a given degree, as a linear map. -/
def mapₗ (n : ℕ) : X n →ₗ[R] Y n where
  toFun := φ.toFun n
  map_add' := φ.map_add n
  map_smul' c x := φ.map_smul n c x

@[simp]
theorem mapₗ_apply (n : ℕ) (x : X n) : φ.mapₗ n x = φ.toFun n x := rfl

/-- A morphism carries cocycles to cocycles. -/
theorem map_mem_cocycles {n : ℕ} {x : X n} (hx : x ∈ A.cocycles n) :
    φ.toFun n x ∈ B.cocycles n := by
  rw [CDGAStructure.mem_cocycles] at hx ⊢
  rw [← φ.map_d n x, hx]
  exact (φ.mapₗ (n + 1)).map_zero

/-- The map induced by a morphism on cocycles. -/
def cocyclesMap (n : ℕ) : A.cocycles n →ₗ[R] B.cocycles n where
  toFun x := ⟨φ.toFun n (x : X n), φ.map_mem_cocycles x.2⟩
  map_add' _ _ := Subtype.ext (φ.map_add n _ _)
  map_smul' c _ := Subtype.ext (φ.map_smul n c _)

@[simp]
theorem cocyclesMap_coe (n : ℕ) (x : A.cocycles n) :
    ((φ.cocyclesMap n x : B.cocycles n) : Y n) = φ.toFun n (x : X n) := rfl

/-- **The map induced by a morphism on cohomology.** -/
def cohomologyMap (n : ℕ) : A.cohomology n →ₗ[R] B.cohomology n :=
  Submodule.mapQ _ _ (φ.cocyclesMap (n + 1)) (by
    rintro x ⟨y, hy⟩
    refine ⟨φ.toFun n y, ?_⟩
    show φ.toFun (n + 1) (x : X (n + 1)) = B.d n (φ.toFun n y)
    rw [hy, φ.map_d n y])

theorem cohomologyMap_mk (n : ℕ) (x : A.cocycles (n + 1)) :
    φ.cohomologyMap n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.cocyclesMap (n + 1) x) := rfl

/-- **A quasi-isomorphism**: a morphism inducing an isomorphism on cohomology in every degree. -/
def IsQuasiIso : Prop := ∀ n : ℕ, Function.Bijective (φ.cohomologyMap n)

end CDGAHom

end GaloisForLFunctions.HTGeometry
