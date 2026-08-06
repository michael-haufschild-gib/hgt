import GaloisForLFunctions.HTGeometry.CompoundOperatorOrder
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The compound of an exponential ray

A Hermitian matrix written in diagonalised form `Vᴴ D V` generates on the `k`-th compound the
Hermitian matrix `(Λᵏ V)ᴴ Σ (Λᵏ V)`, where `Σ` carries the subset sums of the eigenvalues, and

```text
Λᵏ (exp (t W)) = exp (t Λᵏ_gen W).
```

The identity is elementary in a diagonalising frame: the compound of a diagonal matrix is the
diagonal of the subset products, and a subset product of exponentials is the exponential of the
subset sum.  What it buys is that the two rays being compared stay exponential rays after passing
to the compound, so the operator-order inequalities of the functional calculus apply there.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-! ## The induced generator -/

/-- The subset sums of a real tuple, indexed by the `k`-element subsets. -/
def subsetSum (k : ℕ) (w : ι → ℝ) (s : Set.powersetCard ι k) : ℝ :=
  ∑ i ∈ (s : Finset ι), w i

/-- The generator induced on the `k`-th compound by a Hermitian matrix `Vᴴ (diag w) V`. -/
noncomputable def compoundGen (k : ℕ) (V : Matrix ι ι ℂ) (w : ι → ℝ) :
    Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) ℂ :=
  (compound k V)ᴴ * rdiag (subsetSum k w) * compound k V

theorem rdiag_conjTranspose {κ : Type*} [DecidableEq κ] (w : κ → ℝ) :
    (rdiag w)ᴴ = rdiag w := by
  rw [rdiag, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem isHermitian_conj_rdiag' {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (w : κ → ℝ) : (Uᴴ * rdiag w * U).IsHermitian := by
  show (Uᴴ * rdiag w * U)ᴴ = Uᴴ * rdiag w * U
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    rdiag_conjTranspose, ← mul_assoc]

theorem isHermitian_compoundGen (k : ℕ) (V : Matrix ι ι ℂ) (w : ι → ℝ) :
    (compoundGen k V w).IsHermitian :=
  isHermitian_conj_rdiag' _ _

/-! ## The compound of a diagonal ray -/

theorem compound_rdiag_exp (k : ℕ) (w : ι → ℝ) (t : ℝ) :
    compound k (rdiag fun i => Real.exp (t * w i))
      = rdiag fun s : Set.powersetCard ι k => Real.exp (t * subsetSum k w s) := by
  rw [compound_rdiag]
  congr 1
  funext s
  rw [subsetSum, Finset.mul_sum, Real.exp_sum]

/-! ## The compound of an exponential ray is an exponential ray -/

theorem compound_conj_rdiag_exp (k : ℕ) (V : Matrix ι ι ℂ) (w : ι → ℝ) (t : ℝ) :
    compound k (Vᴴ * (rdiag fun i => Real.exp (t * w i)) * V)
      = (compound k V)ᴴ * (rdiag fun s : Set.powersetCard ι k =>
          Real.exp (t * subsetSum k w s)) * compound k V := by
  rw [compound_mul, compound_mul, compound_conjTranspose, compound_rdiag_exp]

/-- The compound of a unitary is unitary, in the two-sided form the conjugation needs. -/
theorem compound_conjTranspose_mul_self {k : ℕ} {V : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    (compound k V)ᴴ * compound k V = 1 := by
  have := compound_unitary (k := k) hV
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
  exact this

theorem compound_mul_conjTranspose_self {k : ℕ} {V : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    compound k V * (compound k V)ᴴ = 1 := by
  have := compound_unitary (k := k) hV
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
  exact this

/-! ## The matrix exponential of the induced generator -/

omit [LinearOrder ι] in
theorem exp_smul_rdiag (k : ℕ) (w : ι → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • rdiag (subsetSum k w))
      = rdiag fun s : Set.powersetCard ι k => Real.exp (t * subsetSum k w s) := by
  have hsmul : (t : ℂ) • rdiag (subsetSum k w)
      = Matrix.diagonal fun s : Set.powersetCard ι k => ((t * subsetSum k w s : ℝ) : ℂ) := by
    ext s u
    rw [Matrix.smul_apply, rdiag, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : s = u
    · subst h
      simp only [smul_eq_mul]
      push_cast
      ring
    · simp [h]
  rw [hsmul, Matrix.exp_diagonal]
  show Matrix.diagonal (NormedSpace.exp
    fun s : Set.powersetCard ι k => ((t * subsetSum k w s : ℝ) : ℂ)) = _
  rw [rdiag]
  congr 1
  rw [Pi.exp_def]
  funext s
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

end GaloisForLFunctions.HTGeometry
