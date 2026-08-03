import GaloisForLFunctions.RHTower.CyclicBarCyclicModule

/-!
# Trace augmentations of the genuine cyclic bar construction

A linear trace `τ : A → R` determines in every cyclic degree the functional

`a₀ ⊗ ⋯ ⊗ aₙ ↦ τ(a₀ ⋯ aₙ)`.

This file constructs those maps directly on `PiTensorProduct` and proves compatibility with every
face, degeneracy, and cyclic rotation.  The proof uses the exact simplicial and Connes relations
already established for the genuine tensor cyclic bar.  Only the final two-factor wrap face uses
the trace law.  No commutativity of `A` is assumed.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Ordered multiplication of a degree-zero cyclic-bar tensor. -/
def cyclicBarDegreeZeroProduct : CyclicBarTensor R A 0 →ₗ[R] A :=
  (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ A) 0).toLinearMap

@[simp]
theorem cyclicBarDegreeZeroProduct_tprod (x : Fin 1 → A) :
    cyclicBarDegreeZeroProduct (R := R)
        (PiTensorProduct.tprod R x) = x 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

/-- Multiply all tensor factors in their cyclic-bar order. -/
def cyclicBarTotalProduct : (n : ℕ) → CyclicBarTensor R A n →ₗ[R] A
  | 0 => cyclicBarDegreeZeroProduct (R := R)
  | n + 1 =>
      (cyclicBarTotalProduct n).comp
        (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 2)))

/-- Degreewise cyclic functional obtained by composing ordered multiplication with a trace. -/
def cyclicBarTraceAugmentation (τ : A →ₗ[R] R) (n : ℕ) :
    CyclicBarTensor R A n →ₗ[R] R :=
  τ.comp (cyclicBarTotalProduct n)

@[simp]
theorem cyclicBarTraceAugmentation_zero_tprod (τ : A →ₗ[R] R)
    (x : Fin 1 → A) :
    cyclicBarTraceAugmentation τ 0 (PiTensorProduct.tprod R x) = τ (x 0) := by
  change τ (cyclicBarDegreeZeroProduct (R := R)
    (PiTensorProduct.tprod R x)) = τ (x 0)
  rw [cyclicBarDegreeZeroProduct_tprod]

/-- Every face preserves the product trace.  The wrap face is exactly where cyclicity of `τ`
is required. -/
theorem cyclicBarTraceAugmentation_comp_face
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    ∀ (n : ℕ) (i : Fin (n + 2)),
      (cyclicBarTraceAugmentation τ n).comp
          (cyclicBarFace (R := R) (A := A) i) =
        cyclicBarTraceAugmentation τ (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          apply PiTensorProduct.ext
          ext x
          change
            τ (cyclicBarDegreeZeroProduct (R := R)
              (cyclicBarFace (R := R) (A := A) (1 : Fin 2)
                (PiTensorProduct.tprod R x))) =
            τ (cyclicBarDegreeZeroProduct (R := R)
              (cyclicBarFace (R := R) (A := A) (0 : Fin 2)
                (PiTensorProduct.tprod R x)))
          rw [cyclicBarFace_tprod, cyclicBarFace_tprod,
            cyclicBarDegreeZeroProduct_tprod,
            cyclicBarDegreeZeroProduct_tprod]
          change τ (x 1 * x 0) = τ (x 0 * x 1)
          exact hτ (x 1) (x 0)
  | succ n ih =>
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ j =>
          change
            ((cyclicBarTraceAugmentation τ n).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarFace (R := R) (A := A) j.succ) = _
          rw [LinearMap.comp_assoc,
            cyclicBarFace_comp_face (R := R) (A := A)
              (0 : Fin (n + 2)) j (Fin.zero_le j),
            ← LinearMap.comp_assoc, ih j]
          rfl

/-- Inserting a unit preserves every product trace. -/
theorem cyclicBarTraceAugmentation_comp_degeneracy
    (τ : A →ₗ[R] R) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      (cyclicBarTraceAugmentation τ (n + 1)).comp
          (cyclicBarDegeneracy (R := R) (A := A) i) =
        cyclicBarTraceAugmentation τ n := by
  intro n
  induction n with
  | zero =>
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change
        ((cyclicBarTraceAugmentation τ 0).comp
            (cyclicBarFace (R := R) (A := A) 0)).comp
            (cyclicBarDegeneracy (R := R) (A := A) 0) = _
      have hface :=
        cyclicBarFace_comp_degeneracy_self
          (R := R) (A := A) (0 : Fin 1)
      change
        (cyclicBarFace (R := R) (A := A) (0 : Fin 2)).comp
            (cyclicBarDegeneracy (R := R) (A := A) (0 : Fin 1)) =
          LinearMap.id at hface
      rw [LinearMap.comp_assoc, hface]
      rfl
  | succ n ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          change
            ((cyclicBarTraceAugmentation τ (n + 1)).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarDegeneracy (R := R) (A := A) 0) = _
          have hface :=
            cyclicBarFace_comp_degeneracy_self
              (R := R) (A := A) (0 : Fin (n + 2))
          change
            (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 3))).comp
                (cyclicBarDegeneracy (R := R) (A := A) (0 : Fin (n + 2))) =
              LinearMap.id at hface
          rw [LinearMap.comp_assoc, hface]
          rfl
      | succ j =>
          change
            ((cyclicBarTraceAugmentation τ (n + 1)).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarDegeneracy (R := R) (A := A) j.succ) = _
          have hface :=
            cyclicBarFace_comp_degeneracy_of_le
              (R := R) (A := A) (0 : Fin (n + 2)) j (Fin.zero_le _)
          change
            (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 3))).comp
                (cyclicBarDegeneracy (R := R) (A := A) j.succ) =
              (cyclicBarDegeneracy (R := R) (A := A) j).comp
                (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 2))) at hface
          rw [LinearMap.comp_assoc, hface, ← LinearMap.comp_assoc, ih j]
          rfl

/-- Cyclic rotation preserves the product trace in every degree. -/
theorem cyclicBarTraceAugmentation_comp_rotate
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (n : ℕ) :
    (cyclicBarTraceAugmentation τ n).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
      cyclicBarTraceAugmentation τ n := by
  cases n with
  | zero =>
      apply PiTensorProduct.ext
      ext x
      simp
  | succ n =>
      change
        ((cyclicBarTraceAugmentation τ n).comp
            (cyclicBarFace (R := R) (A := A) 0)).comp
            (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap = _
      rw [LinearMap.comp_assoc,
        cyclicBarRotate_comp_face_zero (R := R) (A := A),
        cyclicBarTraceAugmentation_comp_face τ hτ n (Fin.last (n + 1))]

end RHTower
end GaloisForLFunctions
