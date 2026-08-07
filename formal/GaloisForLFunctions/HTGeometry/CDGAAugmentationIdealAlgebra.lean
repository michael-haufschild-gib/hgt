import GaloisForLFunctions.HTGeometry.CDGAAugmentation

/-!
# The augmentation ideal as a non-unital algebra

The kernel of an augmentation is closed under the product of the algebra, because the augmentation is
multiplicative and one factor already dies.  The product on it inherits bilinearity, associativity,
graded commutativity and the Leibniz rule from the algebra, so the ideal is a commutative
differential graded algebra without a unit — the object the bar construction is built on.

* `HTGeometry.augIdealMul` : the product on the augmentation ideal.
* `HTGeometry.augIdealMul_assoc`, `_comm`, `_leibniz` : its laws.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- The augmentation ideal is closed under the product on both sides. -/
theorem augIdeal_mul_mem_both {a b n : ℕ} (h : a + b = n) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) : A.mul h (x : X a) (y : X b) ∈ LinearMap.ker (ε.mapₗ n) :=
  augIdeal_mul_mem ε h (x : X a) y

/-- **The product on the augmentation ideal.** -/
def augIdealMul {a b n : ℕ} (h : a + b = n) (x : augIdealCarrier ε a) (y : augIdealCarrier ε b) :
    augIdealCarrier ε n :=
  ⟨A.mul h (x : X a) (y : X b), augIdeal_mul_mem_both ε h x y⟩

@[simp] theorem augIdealMul_coe {a b n : ℕ} (h : a + b = n) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    ((augIdealMul ε h x y : augIdealCarrier ε n) : X n) = A.mul h (x : X a) (y : X b) := rfl

theorem augIdealMul_add_left {a b n : ℕ} (h : a + b = n) (x x' : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    augIdealMul ε h (x + x') y = augIdealMul ε h x y + augIdealMul ε h x' y :=
  Subtype.ext (A.mul_add_left h _ _ _)

theorem augIdealMul_add_right {a b n : ℕ} (h : a + b = n) (x : augIdealCarrier ε a)
    (y y' : augIdealCarrier ε b) :
    augIdealMul ε h x (y + y') = augIdealMul ε h x y + augIdealMul ε h x y' :=
  Subtype.ext (A.mul_add_right h _ _ _)

theorem augIdealMul_smul_left {a b n : ℕ} (h : a + b = n) (c : R) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    augIdealMul ε h (c • x) y = c • augIdealMul ε h x y :=
  Subtype.ext (A.mul_smul_left h c _ _)

theorem augIdealMul_smul_right {a b n : ℕ} (h : a + b = n) (c : R) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    augIdealMul ε h x (c • y) = c • augIdealMul ε h x y :=
  Subtype.ext (A.mul_smul_right h c _ _)

/-- **The product on the augmentation ideal is associative.** -/
theorem augIdealMul_assoc {a b k m m' n : ℕ} (h₁ : a + b = m) (h₂ : m + k = n) (h₃ : b + k = m')
    (h₄ : a + m' = n) (x : augIdealCarrier ε a) (y : augIdealCarrier ε b)
    (z : augIdealCarrier ε k) :
    augIdealMul ε h₂ (augIdealMul ε h₁ x y) z = augIdealMul ε h₄ x (augIdealMul ε h₃ y z) :=
  Subtype.ext (A.mul_assoc h₁ h₂ h₃ h₄ _ _ _)

/-- **The product on the augmentation ideal is graded commutative.** -/
theorem augIdealMul_comm {a b n : ℕ} (h : a + b = n) (h' : b + a = n) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    augIdealMul ε h x y = ((-1 : R)) ^ (a * b) • augIdealMul ε h' y x :=
  Subtype.ext (A.mul_comm h h' _ _)

/-- **The Leibniz rule on the augmentation ideal.** -/
theorem augIdealMul_leibniz {a b n : ℕ} (h : a + b = n) (x : augIdealCarrier ε a)
    (y : augIdealCarrier ε b) :
    (augIdealModule ε).d n (augIdealMul ε h x y)
      = augIdealMul ε (show a + 1 + b = n + 1 by omega) ((augIdealModule ε).d a x) y
        + ((-1 : R)) ^ a •
          augIdealMul ε (show a + (b + 1) = n + 1 by omega) x ((augIdealModule ε).d b y) :=
  Subtype.ext (A.d_mul h _ _)

end GaloisForLFunctions.HTGeometry
