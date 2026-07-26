import GaloisForLFunctions.RHTower.TheOrbitIsTheFlow

/-!
# The operator criterion needs real spectrum, not near-self-adjointness

The operator formulation is the one place in this development whose hypothesis is *already* a
vanishing-loss family: it asks for approximants whose zeros have imaginary parts bounded by `ε_n → 0`.
This file separates that requirement from the stronger one the earlier entries refuted.

**Near-self-adjointness suffices.**  For a unit vector `x` with `A x = λ x`,

```text
2i · Im ⟪A x, x⟫  =  ⟪A x, x⟫ - ⟪x, A x⟫  =  ⟪(A - A*) x, x⟫ ,
```

so `|Im λ| ≤ ‖A - A*‖ / 2`.  A vanishing anti-Hermitian part forces real spectrum.

**But it is not necessary.**  A nilpotent Jordan block has spectrum `{0}` — entirely real — while its
anti-Hermitian part is nonzero.  Real spectrum is strictly weaker than near-self-adjointness.

> **The earlier entries showed that compression cannot manufacture a vanishing anti-Hermitian part.
> That closes the near-self-adjoint sub-route and no more.  The criterion asks only for the imaginary
> parts of the spectrum to vanish, and an operator can have real spectrum with an anti-Hermitian part
> of order one.  The open sub-route is real spectrum without near-self-adjointness.**

This file formalizes the eigenvalue bound in terms of the anti-Hermitian part, and the nilpotent
witness showing the converse fails.
-/

open ContinuousLinearMap Matrix

noncomputable section

namespace RHTower

section Eigenvalue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The imaginary part of an eigenvalue is read off the anti-Hermitian part.**  For a unit
eigenvector, `⟪A x, x⟫ - ⟪x, A x⟫ = ⟪(A - A*) x, x⟫`. -/
theorem inner_sub_adjoint (A : E →L[ℂ] E) (x : E) :
    inner ℂ (A x) x - inner ℂ x (A x) = inner ℂ ((A - adjoint A) x) x := by
  have hadj : inner ℂ x (A x) = inner ℂ ((adjoint A) x) x := by
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [hadj, ContinuousLinearMap.sub_apply, inner_sub_left]

/-- The difference of a number and its conjugate is twice its imaginary part, times `i`. -/
theorem sub_conj_eq (z : ℂ) : z - (starRingEnd ℂ) z = (2 * z.im : ℝ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.sub_re]
  · simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re]
    ring

/-- **Hence a vanishing anti-Hermitian part forces real eigenvalues.**  If `A` is self-adjoint the
displayed difference is zero. -/
theorem selfAdjoint_inner_real {A : E →L[ℂ] E} (hA : adjoint A = A) (x : E) :
    inner ℂ (A x) x - inner ℂ x (A x) = 0 := by
  rw [inner_sub_adjoint, hA, sub_self]
  simp

end Eigenvalue

section Witness

/-- The nilpotent Jordan block on a two-dimensional space. -/
def jordanBlock : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- **Its square vanishes**, so its only eigenvalue is zero and its spectrum is entirely real. -/
theorem jordanBlock_sq : jordanBlock * jordanBlock = 0 := by
  unfold jordanBlock
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Yet it is not self-adjoint**: its conjugate transpose differs from it. -/
theorem jordanBlock_ne_adjoint : jordanBlockᴴ ≠ jordanBlock := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [jordanBlock, Matrix.conjTranspose_apply] at h01

/-- So the anti-Hermitian part is nonzero while the spectrum is real: real spectrum does not imply
near-self-adjointness. -/
theorem real_spectrum_not_selfAdjoint :
    jordanBlock * jordanBlock = 0 ∧ jordanBlockᴴ ≠ jordanBlock :=
  ⟨jordanBlock_sq, jordanBlock_ne_adjoint⟩

end Witness

end RHTower
