import GaloisForLFunctions.HTGeometry.ThreeParticleLegsRing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Entrywise derivatives of matrix-valued functions

`HasMatrixDerivAt M M' b` says every entry of `M` has derivative the corresponding entry of `M'`.
The product rule, the two tensor-leg rules, and translation of the argument are all entrywise
consequences of the scalar rules; uniqueness is entrywise uniqueness.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- Entrywise derivative of a matrix-valued function of one complex variable. -/
def HasMatrixDerivAt {m n : Type*} (M : ℂ → Matrix m n ℂ) (M' : Matrix m n ℂ) (b : ℂ) : Prop :=
  ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) b

namespace HasMatrixDerivAt

variable {m n p : Type*}

theorem const (C : Matrix m n ℂ) (b : ℂ) : HasMatrixDerivAt (fun _ => C) 0 b :=
  fun _ _ => hasDerivAt_const b _

theorem add {A B : ℂ → Matrix m n ℂ} {A' B' : Matrix m n ℂ} {b : ℂ}
    (hA : HasMatrixDerivAt A A' b) (hB : HasMatrixDerivAt B B' b) :
    HasMatrixDerivAt (fun t => A t + B t) (A' + B') b :=
  fun i j => (hA i j).add (hB i j)

theorem sub {A B : ℂ → Matrix m n ℂ} {A' B' : Matrix m n ℂ} {b : ℂ}
    (hA : HasMatrixDerivAt A A' b) (hB : HasMatrixDerivAt B B' b) :
    HasMatrixDerivAt (fun t => A t - B t) (A' - B') b :=
  fun i j => (hA i j).sub (hB i j)

theorem mul [Fintype n] [DecidableEq n] {A : ℂ → Matrix m n ℂ} {B : ℂ → Matrix n p ℂ}
    {A' : Matrix m n ℂ} {B' : Matrix n p ℂ} {b : ℂ}
    (hA : HasMatrixDerivAt A A' b) (hB : HasMatrixDerivAt B B' b) :
    HasMatrixDerivAt (fun t => A t * B t) (A' * B b + A b * B') b := by
  intro i j
  have hsum : HasDerivAt (fun t => ∑ k : n, A t i k * B t k j)
      (∑ k : n, (A' i k * B b k j + A b i k * B' k j)) b := by
    have hfam : ∀ k ∈ (Finset.univ : Finset n),
        HasDerivAt (fun t => A t i k * B t k j)
          (A' i k * B b k j + A b i k * B' k j) b := fun k _ => (hA i k).mul (hB k j)
    have hsum := HasDerivAt.sum (A := fun k => fun t => A t i k * B t k j)
      (A' := fun k => A' i k * B b k j + A b i k * B' k j) hfam
    have hfun : (∑ k : n, fun t : ℂ => A t i k * B t k j)
        = fun t : ℂ => ∑ k : n, A t i k * B t k j := by
      funext t
      simp
    rw [hfun] at hsum
    exact hsum
  have hval : (A' * B b + A b * B') i j
      = ∑ k : n, (A' i k * B b k j + A b i k * B' k j) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  rw [hval]
  exact hsum

theorem comp_const_add {A : ℂ → Matrix m n ℂ} {A' : Matrix m n ℂ} {a b : ℂ}
    (hA : HasMatrixDerivAt A A' (a + b)) :
    HasMatrixDerivAt (fun t => A (a + t)) A' b := by
  intro i j
  have hinner : HasDerivAt (fun t : ℂ => a + t) 1 b := by
    simpa using (hasDerivAt_id b).const_add a
  have hc := (hA i j).scomp b hinner
  rw [one_smul] at hc
  exact hc

theorem legLeft {κ : Type*} [DecidableEq κ] {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    {A' : Matrix (κ × κ) (κ × κ) ℂ} {b : ℂ} (hA : HasMatrixDerivAt A A' b) :
    HasMatrixDerivAt (fun t => HTGeometry.legLeft (A t)) (HTGeometry.legLeft A') b := by
  intro i j
  simpa [HTGeometry.legLeft] using (hA (i.1, i.2.1) (j.1, j.2.1)).mul_const
    ((1 : Matrix κ κ ℂ) i.2.2 j.2.2)

theorem legRight {κ : Type*} [DecidableEq κ] {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    {A' : Matrix (κ × κ) (κ × κ) ℂ} {b : ℂ} (hA : HasMatrixDerivAt A A' b) :
    HasMatrixDerivAt (fun t => HTGeometry.legRight (A t)) (HTGeometry.legRight A') b := by
  intro i j
  simpa [HTGeometry.legRight] using (hA i.2 j.2).const_mul
    ((1 : Matrix κ κ ℂ) i.1 j.1)

theorem unique {A : ℂ → Matrix m n ℂ} {A' B' : Matrix m n ℂ} {b : ℂ}
    (hA : HasMatrixDerivAt A A' b) (hB : HasMatrixDerivAt A B' b) : A' = B' := by
  ext i j
  exact (hA i j).unique (hB i j)

theorem congr {A B : ℂ → Matrix m n ℂ} {A' : Matrix m n ℂ} {b : ℂ}
    (hA : HasMatrixDerivAt A A' b) (h : A = B) : HasMatrixDerivAt B A' b := by
  subst h; exact hA

end HasMatrixDerivAt

end GaloisForLFunctions.HTGeometry
