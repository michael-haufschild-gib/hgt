import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Ancilla-indexed block matrices

A matrix on `n × m` is the same thing as an `m × m` array of `n × n` blocks.  This module records
that dictionary and the four facts the amplification calculus needs: block multiplication, the
block adjoint, the block trace, and the fact that the ancilla amplification of a map is exactly
its entrywise action on blocks.
-/

open Matrix
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {n m : Type*}

/-- Assemble a matrix with an ancilla index from its blocks. -/
def blockMat (B : m → m → Matrix n n ℂ) : Matrix (n × m) (n × m) ℂ :=
  fun p q => B p.2 q.2 p.1 q.1

/-- The blocks of a matrix with an ancilla index. -/
def matBlock (X : Matrix (n × m) (n × m) ℂ) : m → m → Matrix n n ℂ :=
  fun a b i j => X (i, a) (j, b)

@[simp] theorem blockMat_apply (B : m → m → Matrix n n ℂ) (p q : n × m) :
    blockMat B p q = B p.2 q.2 p.1 q.1 := rfl

@[simp] theorem matBlock_apply (X : Matrix (n × m) (n × m) ℂ) (a b : m) (i j : n) :
    matBlock X a b i j = X (i, a) (j, b) := rfl

@[simp] theorem blockMat_matBlock (X : Matrix (n × m) (n × m) ℂ) : blockMat (matBlock X) = X := rfl

@[simp] theorem matBlock_blockMat (B : m → m → Matrix n n ℂ) : matBlock (blockMat B) = B := rfl

/-- **Block multiplication.** -/
theorem blockMat_mul [Fintype n] [Fintype m] (B C : m → m → Matrix n n ℂ) :
    blockMat B * blockMat C = blockMat (fun a b => ∑ c, B a c * C c b) := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [blockMat_apply, Matrix.sum_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **The block adjoint.** -/
theorem blockMat_conjTranspose (B : m → m → Matrix n n ℂ) :
    (blockMat B)ᴴ = blockMat (fun a b => (B b a)ᴴ) := by
  ext p q
  simp [blockMat, Matrix.conjTranspose_apply]

/-- **The block trace.** -/
theorem blockMat_trace [Fintype n] [Fintype m] (B : m → m → Matrix n n ℂ) :
    (blockMat B).trace = ∑ a, (B a a).trace := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, blockMat_apply]
  exact Finset.sum_comm

/-- **The ancilla amplification acts entrywise on blocks.** -/
theorem amplify_blockMat [Fintype n] [DecidableEq n] [Fintype m]
    (Φ : Matrix n n ℂ → Matrix n n ℂ) (B : m → m → Matrix n n ℂ) :
    amplify Φ m (blockMat B) = blockMat (fun a b => Φ (B a b)) := rfl

/-- **Amplification is trace preserving whenever the map is.** -/
theorem trace_amplify [Fintype n] [DecidableEq n] [Fintype m]
    {Φ : Matrix n n ℂ → Matrix n n ℂ} (htp : ∀ X, (Φ X).trace = X.trace)
    (X : Matrix (n × m) (n × m) ℂ) : (amplify Φ m X).trace = X.trace := by
  conv_lhs => rw [← blockMat_matBlock X, amplify_blockMat]
  rw [blockMat_trace]
  conv_rhs => rw [← blockMat_matBlock X, blockMat_trace]
  exact Finset.sum_congr rfl fun a _ => htp _

/-- **Amplification is additive whenever the map is.** -/
theorem amplify_sub' [Fintype n] [DecidableEq n] [Fintype m]
    {Φ : Matrix n n ℂ → Matrix n n ℂ} (hsub : ∀ X Y, Φ (X - Y) = Φ X - Φ Y)
    (X Y : Matrix (n × m) (n × m) ℂ) :
    amplify Φ m (X - Y) = amplify Φ m X - amplify Φ m Y := by
  ext p q
  rw [Matrix.sub_apply, amplify_apply, amplify_apply, amplify_apply,
    show (fun i j => (X - Y) (i, p.2) (j, q.2))
      = matBlock X p.2 q.2 - matBlock Y p.2 q.2 from rfl, hsub]
  rfl

end GaloisForLFunctions.HTGeometry
