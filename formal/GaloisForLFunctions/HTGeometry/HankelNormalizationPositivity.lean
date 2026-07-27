import Mathlib

/-!
# Which Hankel normalizations preserve positivity

A raw moment matrix `M i j = m (i + j)` of a positive measure is positive semidefinite for nothing.
Normalizing it entrywise, `M i j ↦ c (i + j) · m (i + j)`, is a **Hadamard product** with the Hankel
matrix of the sequence `c`.  By the Schur product theorem the Hadamard product of two positive
semidefinite matrices is positive semidefinite, so

> **a Hankel normalization `c` preserves positivity of every raw moment matrix as soon as the Hankel
> matrices of `c` are themselves positive semidefinite** — that is, as soon as `c` is a
> positive-definite sequence.

This is the exact dividing line between the normalizations that survive and the ones that do not, and
it is checkable at the first nontrivial minor.  The **factorial normalization** `c k = 1/k!` fails
there:

```text
det [[1/0!, 1/1!], [1/1!, 1/2!]] = det [[1, 1], [1, 1/2]] = −1/2 < 0 .
```

So dividing moments by factorials of the *summed* index cannot preserve positivity — not because of
any property of the moments, but because the divisor sequence is not itself a moment sequence.  A
divisor of the separated form `c (i + j) = d i · d j` is a diagonal congruence and always preserves
positivity; the factorial divisor is not of that form, since `log (i + j)!` is not additive.
-/

open Matrix

namespace GaloisForLFunctions

namespace HankelNormalization

/-- The Hankel matrix of a real sequence. -/
noncomputable def hankel (c : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => c ((i : ℕ) + (j : ℕ))

/-- Entrywise normalization of a Hankel matrix is the Hadamard product with the normalizer's own
Hankel matrix. -/
theorem hankel_normalize_eq_hadamard (c m : ℕ → ℝ) (n : ℕ) :
    (Matrix.of fun i j => c ((i : ℕ) + (j : ℕ)) * m ((i : ℕ) + (j : ℕ)) :
        Matrix (Fin n) (Fin n) ℝ)
      = (hankel c n) ⊙ (hankel m n) := by
  ext i j
  rfl

/-- **Positivity-preserving normalization.**  If both the normalizer's Hankel matrix and the raw
Hankel matrix are positive semidefinite, so is the normalized matrix — the Schur product theorem. -/
theorem posSemidef_hankel_normalize (c m : ℕ → ℝ) (n : ℕ)
    (hc : (hankel c n).PosSemidef) (hm : (hankel m n).PosSemidef) :
    (Matrix.of fun i j => c ((i : ℕ) + (j : ℕ)) * m ((i : ℕ) + (j : ℕ)) :
      Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  rw [hankel_normalize_eq_hadamard]
  exact hc.hadamard hm

/-- A rank-one symmetric matrix `v i · v j` is positive semidefinite. -/
theorem posSemidef_rankOne {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.of fun i j => v i * v j : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  have heq : (Matrix.of fun i j => v i * v j : Matrix (Fin n) (Fin n) ℝ)
      = (Matrix.of fun (_ : Fin 1) (j : Fin n) => v j)ᴴ *
        (Matrix.of fun (_ : Fin 1) (j : Fin n) => v j) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **A separated divisor is a congruence and always preserves positivity.**  When the normalizer
factors as `d i · d j` the normalized matrix is a Hadamard product with a rank-one positive matrix,
so no hypothesis on `d` is needed. -/
theorem posSemidef_separated_normalize {n : ℕ} (d : Fin n → ℝ) (m : ℕ → ℝ)
    (hm : (hankel m n).PosSemidef) :
    (Matrix.of fun i j => d i * d j * m ((i : ℕ) + (j : ℕ)) :
      Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  have heq : (Matrix.of fun i j => d i * d j * m ((i : ℕ) + (j : ℕ)) :
        Matrix (Fin n) (Fin n) ℝ)
      = (Matrix.of fun i j => d i * d j) ⊙ (hankel m n) := by
    ext i j
    rfl
  rw [heq]
  exact (posSemidef_rankOne d).hadamard hm

/-- The `2 × 2` Hankel matrix of the reciprocal-factorial sequence. -/
noncomputable def reciprocalFactorialTwo : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 1, 1 / 2]

theorem reciprocalFactorialTwo_eq_hankel :
    reciprocalFactorialTwo = hankel (fun k => 1 / (k.factorial : ℝ)) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reciprocalFactorialTwo, hankel, Nat.factorial]

/-- **The factorial normalizer is not a positive sequence.**  Its first nontrivial Hankel
determinant is `−1/2`. -/
theorem det_reciprocalFactorialTwo : reciprocalFactorialTwo.det = -(1 / 2) := by
  rw [reciprocalFactorialTwo, Matrix.det_fin_two_of]
  norm_num

theorem not_posSemidef_reciprocalFactorialTwo : ¬ reciprocalFactorialTwo.PosSemidef := by
  intro h
  have hdet : 0 ≤ reciprocalFactorialTwo.det := h.det_nonneg
  rw [det_reciprocalFactorialTwo] at hdet
  norm_num at hdet

/-- **The factorial normalization is not positivity-preserving**, and the reason is a property of the
divisor alone: the reciprocal-factorial sequence is not a positive-definite sequence. -/
theorem not_posSemidef_hankel_reciprocalFactorial :
    ¬ (hankel (fun k => 1 / (k.factorial : ℝ)) 2).PosSemidef := by
  rw [← reciprocalFactorialTwo_eq_hankel]
  exact not_posSemidef_reciprocalFactorialTwo


/-! ### The positivity-preserving scaling, and what it costs

A divergent Hankel Gram whose entries grow like `L^{i+j+1}/(i+j+1)` — the shape produced by partial
summation against `∑_{n≤N} Λ(n)/n ~ log N`, with `L = log N` — is rendered finite by the scaling

```text
H i j  ↦  L^{-(i+j+1)} · H i j  =  L^{-1} · (L^{-i}) · (L^{-j}) · H i j ,
```

which is a **diagonal congruence times a positive scalar**, hence positivity-preserving with no
hypothesis (`posSemidef_separated_normalize`).  The limit is the Hilbert matrix `1/(i+j+1)`, the
moment matrix of Lebesgue measure on `[0,1]`, which is positive definite.

So a positivity-preserving regularization of such a Gram exists — and its limit depends only on the
**leading** asymptotics.  Every subleading term, which is where the arithmetic lives, is scaled away.
That is the exact price: the two branches are

* separated scaling — positivity survives, arithmetic does not;
* principal subtraction — arithmetic survives, positivity does not. -/

/-- The Hilbert matrix `1/(i+j+1)`. -/
noncomputable def hilbertMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 1 / ((i : ℕ) + (j : ℕ) + 1 : ℝ)

/-- The Hilbert matrix is the moment matrix of Lebesgue measure on `[0,1]`: `1/(i+j+1) = ∫₀¹ t^{i+j}`.
It is therefore the Gram matrix of the monomials in `L²[0,1]`, hence positive definite — the standard
fact, recorded here as the identity the limit rests on. -/
theorem hilbertMatrix_eq_moment (n : ℕ) (i j : Fin n) :
    hilbertMatrix n i j = ∫ t in (0 : ℝ)..1, t ^ ((i : ℕ) + (j : ℕ)) := by
  rw [integral_pow]
  simp [hilbertMatrix]

end HankelNormalization

end GaloisForLFunctions
