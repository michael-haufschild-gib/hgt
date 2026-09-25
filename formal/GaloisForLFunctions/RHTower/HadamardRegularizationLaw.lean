import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Nat.Choose.Basic

/-!
# Which regularizations preserve a free positivity

Raw prime-side Gram matrices are positive semidefinite at every finite aperture with no hypothesis;
what destroys the positivity is the regularization that makes the limit finite.  The regularizations
in question act entrywise, so the question has an exact answer: an entrywise multiplier preserves
positive semidefiniteness for **every** positive semidefinite input if and only if the multiplier is
itself positive semidefinite.  One direction is Schur's product theorem, the other follows by
feeding in the all-ones matrix.

Applied to the factorial regularization this is decisive.  The identity
`(m+n)! = binom(m+n, m)·m!·n!` splits `1/(m+n)!` into a diagonal congruence `(1/m!)(1/n!)`, which is
harmless, times the entrywise multiplier `1/binom(m+n,m)`, which is **not** positive semidefinite —
its two-by-two corner has determinant `−1/2`.  And no diagonal congruence can do the job on its own:
`c_m c_n = 1/(m+n)!` is already contradictory at `m, n ∈ {0,1}`.

So the free positivity survives exactly those regularizations whose multiplier is a positive kernel,
and factorial damping is not one of them.  The inductive limit of the unregularized Grams is, by
contrast, a genuine pre-Hilbert space: consistency of the finite blocks gives a nonnegative form on
finitely supported vectors with no further hypothesis.
-/

open Matrix

namespace RHTower

/-! ## The criterion -/

/-- The all-ones matrix is positive semidefinite. -/
theorem posSemidef_allOnes (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
  have h : (Matrix.of (fun _ _ : ι => (1 : ℝ)))
      = (Matrix.of (fun (_ : Unit) (_ : ι) => (1 : ℝ)))ᴴ *
        (Matrix.of (fun (_ : Unit) (_ : ι) => (1 : ℝ))) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **The regularization criterion.**  An entrywise multiplier preserves positive semidefiniteness
for every positive semidefinite input exactly when the multiplier is a positive kernel. -/
theorem hadamard_preserves_posSemidef_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) :
    (∀ A : Matrix ι ι ℝ, A.PosSemidef → (A.hadamard B).PosSemidef) ↔ B.PosSemidef := by
  constructor
  · intro h
    have hone := h _ (posSemidef_allOnes ι)
    have heq : (Matrix.of (fun _ _ : ι => (1 : ℝ))).hadamard B = B := by
      ext i j
      simp [Matrix.hadamard]
    rwa [heq] at hone
  · intro hB A hA
    exact hA.hadamard hB

/-! ## The factorial regularization fails it -/

/-- The residual entrywise multiplier of the factorial regularization, on its smallest block. -/
noncomputable def reciprocalBinomKernel : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j => 1 / (Nat.choose ((i : ℕ) + (j : ℕ)) (i : ℕ) : ℝ))

theorem reciprocalBinomKernel_apply_zero_zero : reciprocalBinomKernel 0 0 = 1 := by
  simp [reciprocalBinomKernel]

theorem reciprocalBinomKernel_apply_zero_one : reciprocalBinomKernel 0 1 = 1 := by
  simp [reciprocalBinomKernel]

theorem reciprocalBinomKernel_apply_one_zero : reciprocalBinomKernel 1 0 = 1 := by
  simp [reciprocalBinomKernel]

theorem reciprocalBinomKernel_apply_one_one : reciprocalBinomKernel 1 1 = 1 / 2 := by
  norm_num [reciprocalBinomKernel]

/-- **The residual multiplier is not a positive kernel.**  The two-by-two corner already fails, with
determinant `−1/2`; the vector `(1, −2)` is an explicit witness. -/
theorem reciprocalBinomKernel_not_posSemidef : ¬ reciprocalBinomKernel.PosSemidef := by
  intro h
  have hx := h.re_dotProduct_nonneg ![(1 : ℝ), -2]
  have hval : (star ![(1 : ℝ), -2]) ⬝ᵥ (reciprocalBinomKernel.mulVec ![(1 : ℝ), -2]) = -1 := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [reciprocalBinomKernel_apply_zero_zero, reciprocalBinomKernel_apply_zero_one,
      reciprocalBinomKernel_apply_one_zero, reciprocalBinomKernel_apply_one_one]
    norm_num
  rw [hval] at hx
  simp at hx
  linarith

/-- The factorial regularization splits into a congruence and the residual multiplier. -/
theorem factorial_hadamard_factorization (m n : ℕ) :
    (1 : ℝ) / (Nat.factorial (m + n) : ℝ)
      = (1 / (Nat.factorial m : ℝ)) * (1 / (Nat.factorial n : ℝ)) *
          (1 / (Nat.choose (m + n) m : ℝ)) := by
  have hsplit : Nat.choose (m + n) m * Nat.factorial m * Nat.factorial n
      = Nat.factorial (m + n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    simpa using h
  have hm : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hc : (Nat.choose (m + n) m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right m n)).ne'
  have hcast : (Nat.factorial (m + n) : ℝ)
      = (Nat.choose (m + n) m : ℝ) * (Nat.factorial m : ℝ) * (Nat.factorial n : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsplit.symm
  rw [hcast]
  field_simp

/-- **No diagonal congruence achieves factorial damping.**  Already the indices `0` and `1` are
contradictory, so the failure is not an artefact of the size of the block. -/
theorem no_congruence_factorial (c : ℕ → ℝ)
    (h : ∀ m n : ℕ, c m * c n = 1 / (Nat.factorial (m + n) : ℝ)) : False := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h11 := h 1 1
  norm_num [Nat.factorial] at h00 h01 h11
  nlinarith [h00, h01, h11]

/-! ## The unregularized limit is a pre-Hilbert space -/

/-- **The inductive limit of consistent positive Grams.**  If every finite principal block of a
kernel is positive semidefinite, the induced form on finitely supported vectors is nonnegative with
no further hypothesis: the unregularized limit carries a genuine positive form. -/
theorem kernel_form_nonneg {ι : Type*} [DecidableEq ι] (K : ι → ι → ℝ)
    (hK : ∀ s : Finset ι, (Matrix.of (fun i j : s => K (i : ι) (j : ι))).PosSemidef)
    (s : Finset ι) (u : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, u i * (K i j * u j) := by
  classical
  have hx := (hK s).re_dotProduct_nonneg (fun i : s => u (i : ι))
  have hval : (star (fun i : s => u (i : ι))) ⬝ᵥ
      ((Matrix.of (fun i j : s => K (i : ι) (j : ι))).mulVec (fun i : s => u (i : ι)))
      = ∑ i ∈ s, ∑ j ∈ s, u i * (K i j * u j) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.of_apply]
    rw [← Finset.sum_coe_sort s (fun i => ∑ j ∈ s, u i * (K i j * u j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_coe_sort s (fun j => u (i : ι) * (K (i : ι) j * u j))]
    simp only [Finset.mul_sum]
  rw [hval] at hx
  simpa using hx

end RHTower
