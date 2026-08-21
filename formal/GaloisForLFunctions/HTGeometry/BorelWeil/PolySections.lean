/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.BorelSubgroup
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The polynomial model of the Borel–Weil sections

For `G = GL(n,k)` with Borel `B` the invertible upper-triangular matrices, and a weight
`lam : n → ℕ`, the space of global sections of the line bundle `L_lam` on the flag variety `G/B` is
the space of *polynomial* functions on the matrix space that transform by the character
`borelCharMat lam` under right translation by `B`.  Because `k` is infinite, polynomial functions
are faithfully represented by polynomials, so we work directly inside
`MvPolynomial (n × n) k`.

This is Jantzen's `H⁰(lam) = ind_B^G lam` in its polynomial (Schur-algebra) incarnation.  Unlike
the group model of `Sections.lean`, this one lives on affine space, where a polynomial is
determined by its values; that makes the big-cell density arguments elementary.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.matEval` — evaluation at a matrix.
* `GaloisForLFunctions.HTGeometry.BorelWeil.IsBorelMat` — invertible upper triangular.
* `GaloisForLFunctions.HTGeometry.BorelWeil.borelCharMat` — the character of `B`.
* `GaloisForLFunctions.HTGeometry.BorelWeil.polySections` — the space of sections.
* `GaloisForLFunctions.HTGeometry.BorelWeil.substLeft` — left translation of polynomials.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [Field k]

/-- Evaluation of a polynomial in the matrix entries at a matrix. -/
noncomputable def matEval (g : Matrix n n k) (p : MvPolynomial (n × n) k) : k :=
  MvPolynomial.eval (fun ij : n × n => g ij.1 ij.2) p

@[simp] theorem matEval_add (g : Matrix n n k) (p q : MvPolynomial (n × n) k) :
    matEval g (p + q) = matEval g p + matEval g q := by simp [matEval]

@[simp] theorem matEval_zero (g : Matrix n n k) : matEval g (0 : MvPolynomial (n × n) k) = 0 := by
  simp [matEval]

@[simp] theorem matEval_smul (g : Matrix n n k) (c : k) (p : MvPolynomial (n × n) k) :
    matEval g (c • p) = c * matEval g p := by simp [matEval]

@[simp] theorem matEval_mul (g : Matrix n n k) (p q : MvPolynomial (n × n) k) :
    matEval g (p * q) = matEval g p * matEval g q := by simp [matEval]

@[simp] theorem matEval_one (g : Matrix n n k) : matEval g (1 : MvPolynomial (n × n) k) = 1 := by
  simp [matEval]

@[simp] theorem matEval_pow (g : Matrix n n k) (p : MvPolynomial (n × n) k) (m : ℕ) :
    matEval g (p ^ m) = (matEval g p) ^ m := by simp [matEval]

@[simp] theorem matEval_X (g : Matrix n n k) (ij : n × n) :
    matEval g (MvPolynomial.X ij) = g ij.1 ij.2 := by simp [matEval]

/-- A polynomial is determined by its values at matrices, over an infinite field. -/
theorem matEval_injective [Infinite k] {p q : MvPolynomial (n × n) k}
    (h : ∀ g : Matrix n n k, matEval g p = matEval g q) : p = q := by
  refine MvPolynomial.funext fun x => ?_
  have := h (Matrix.of fun i j => x (i, j))
  simpa [matEval] using this

/-- The Borel subgroup of `GL(n,k)`: invertible upper-triangular matrices. -/
def IsBorelMat (B : Matrix n n k) : Prop := B.BlockTriangular id ∧ ∀ i, B i i ≠ 0

theorem IsBorelMat.one : IsBorelMat (1 : Matrix n n k) :=
  ⟨Matrix.blockTriangular_one, fun i => by simp⟩

theorem IsBorelMat.mul {A B : Matrix n n k} (hA : IsBorelMat A) (hB : IsBorelMat B) :
    IsBorelMat (A * B) :=
  ⟨hA.1.mul hB.1, fun i => by
    rw [diag_mul_of_blockTriangular hA.1 hB.1]
    exact mul_ne_zero (hA.2 i) (hB.2 i)⟩

theorem IsBorelMat.smul_one {t : k} (ht : t ≠ 0) : IsBorelMat (t • (1 : Matrix n n k)) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h0 : (1 : Matrix n n k) i j = 0 := Matrix.one_apply_ne (Ne.symm (ne_of_lt hij))
    simp [h0]
  · simpa using ht

/-- The character of the Borel attached to a weight. -/
def borelCharMat (lam : n → ℕ) (B : Matrix n n k) : k := ∏ i, (B i i) ^ (lam i)

@[simp] theorem borelCharMat_one (lam : n → ℕ) :
    borelCharMat lam (1 : Matrix n n k) = 1 := by
  simp [borelCharMat]

theorem borelCharMat_mul (lam : n → ℕ) {A B : Matrix n n k}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) :
    borelCharMat lam (A * B) = borelCharMat lam A * borelCharMat lam B := by
  simp only [borelCharMat, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    rw [diag_mul_of_blockTriangular hA hB i, mul_pow]

theorem borelCharMat_smul_one (lam : n → ℕ) (t : k) :
    borelCharMat lam (t • (1 : Matrix n n k)) = t ^ (∑ i, lam i) := by
  simp [borelCharMat, Finset.prod_pow_eq_pow_sum]

/-- **The polynomial model of the Borel–Weil sections.** -/
def polySections (lam : n → ℕ) : Submodule k (MvPolynomial (n × n) k) where
  carrier := {p | ∀ g B : Matrix n n k, IsBorelMat B →
    matEval (g * B) p = borelCharMat lam B * matEval g p}
  add_mem' hp hq g B hB := by rw [matEval_add, matEval_add, hp g B hB, hq g B hB, mul_add]
  zero_mem' := by intro g B _; simp
  smul_mem' c p hp g B hB := by rw [matEval_smul, matEval_smul, hp g B hB]; ring

theorem mem_polySections {lam : n → ℕ} {p : MvPolynomial (n × n) k} :
    p ∈ polySections lam ↔ ∀ g B : Matrix n n k, IsBorelMat B →
      matEval (g * B) p = borelCharMat lam B * matEval g p := Iff.rfl

/-- Left translation of polynomials: `substLeft x p` evaluates at `x * g` what `p` evaluates at
`g`. -/
noncomputable def substLeft (x : Matrix n n k) :
    MvPolynomial (n × n) k →ₐ[k] MvPolynomial (n × n) k :=
  MvPolynomial.aeval fun ij : n × n => ∑ r : n, MvPolynomial.C (x ij.1 r) * MvPolynomial.X (r, ij.2)

theorem matEval_substLeft (x g : Matrix n n k) (p : MvPolynomial (n × n) k) :
    matEval g (substLeft x p) = matEval (x * g) p := by
  have h1 : (MvPolynomial.eval (fun ij : n × n => g ij.1 ij.2)).comp
      (substLeft x).toRingHom
      = MvPolynomial.eval (fun ij : n × n => (x * g) ij.1 ij.2) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [substLeft]
    · intro ij
      simp [substLeft, Matrix.mul_apply]
  exact congrFun (congrArg (fun φ : MvPolynomial (n × n) k →+* k => (φ : _ → k)) h1) p

/-- The section space is stable under left translation. -/
theorem polySections_substLeft {lam : n → ℕ} (x : Matrix n n k)
    {p : MvPolynomial (n × n) k} (hp : p ∈ polySections lam) :
    substLeft x p ∈ polySections lam := by
  intro g B hB
  rw [matEval_substLeft, matEval_substLeft, ← mul_assoc]
  exact hp (x * g) B hB

end GaloisForLFunctions.HTGeometry.BorelWeil
