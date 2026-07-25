import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Even Real structures on algebraic cyclic words

A conjugate-linear, multiplicative, unital involution on a complex ring acts componentwise on
cyclic words. This file proves that componentwise action commutes with the elementary internal
face, last face, degeneracy, and cyclic rotation schemas.

Lists encode pure cyclic tensors. The tensor-product statement follows from the tensor
universal property once completed cyclic modules are introduced. No topology, cyclic homology,
arithmetic, positivity, zero spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- An even `KRealStructure` compatible with the unit and multiplication of a complex ring. -/
structure KRealAlgebraStructure (A : Type*)
    [Ring A] [Module ℂ A] extends KRealStructure false A where
  map_one : sigma 1 = 1
  map_mul : ∀ a b, sigma (a * b) = sigma a * sigma b

namespace KRealAlgebraStructure

variable {A : Type*} [Ring A] [Module ℂ A]

/-- Componentwise Real involution on a pure cyclic word. -/
def cyclicWordSigma (K : KRealAlgebraStructure A) (w : List A) : List A :=
  w.map K.sigma

@[simp]
theorem cyclicWordSigma_nil (K : KRealAlgebraStructure A) :
    K.cyclicWordSigma [] = [] :=
  rfl

@[simp]
theorem cyclicWordSigma_cons (K : KRealAlgebraStructure A)
    (a : A) (w : List A) :
    K.cyclicWordSigma (a :: w) = K.sigma a :: K.cyclicWordSigma w :=
  rfl

@[simp]
theorem cyclicWordSigma_append (K : KRealAlgebraStructure A)
    (u v : List A) :
    K.cyclicWordSigma (u ++ v) =
      K.cyclicWordSigma u ++ K.cyclicWordSigma v := by
  simp [cyclicWordSigma]

/-- Componentwise application remains an involution in every cyclic degree. -/
theorem cyclicWordSigma_sq (K : KRealAlgebraStructure A) (w : List A) :
    K.cyclicWordSigma (K.cyclicWordSigma w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change K.sigma (K.sigma a) ::
        K.cyclicWordSigma (K.cyclicWordSigma w) = a :: w
      rw [K.sq, ih]
      rfl

/-- One-step cyclic rotation, moving the first entry to the end. -/
def cyclicWordRotate : List A → List A
  | [] => []
  | a :: w => w ++ [a]

/-- Componentwise Real action commutes with cyclic rotation. -/
theorem cyclicWordSigma_rotate (K : KRealAlgebraStructure A) (w : List A) :
    K.cyclicWordSigma (cyclicWordRotate w) =
      cyclicWordRotate (K.cyclicWordSigma w) := by
  cases w <;> simp [cyclicWordRotate]

/-- Componentwise Real action commutes with every internal cyclic face schema. -/
theorem cyclicWordSigma_internalFace
    (K : KRealAlgebraStructure A) (pre post : List A) (a b : A) :
    K.cyclicWordSigma (pre ++ (a * b) :: post) =
      K.cyclicWordSigma pre ++
        (K.sigma a * K.sigma b) :: K.cyclicWordSigma post := by
  simp [K.map_mul]

/-- Componentwise Real action commutes with the last cyclic face schema. -/
theorem cyclicWordSigma_lastFace
    (K : KRealAlgebraStructure A) (middle : List A) (last first : A) :
    K.cyclicWordSigma ((last * first) :: middle) =
      (K.sigma last * K.sigma first) :: K.cyclicWordSigma middle := by
  simp [K.map_mul]

/-- Componentwise Real action commutes with every unit-inserting degeneracy schema. -/
theorem cyclicWordSigma_degeneracy
    (K : KRealAlgebraStructure A) (pre post : List A) :
    K.cyclicWordSigma (pre ++ 1 :: post) =
      K.cyclicWordSigma pre ++ 1 :: K.cyclicWordSigma post := by
  simp [K.map_one]

end KRealAlgebraStructure

end RHTower
end GaloisForLFunctions
