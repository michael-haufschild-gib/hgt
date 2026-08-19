import GaloisForLFunctions.HTGeometry.HermitianTraceNorm

/-!
# Positive trace-preserving maps contract the trace norm

A Hermitian matrix splits as a difference of two positive semidefinite matrices whose traces add
up to its nuclear norm -- the Jordan decomposition, obtained here from the functional calculus of
`x ↦ max x 0`.  A positive, trace-preserving linear map sends each half to a positive matrix of
the same trace, so the triangle inequality for the nuclear norm gives

`‖Φ A‖₁ ≤ ‖A‖₁`

for every Hermitian `A`.  Only positivity and trace preservation are used; no complete positivity
and no adjoint.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive part of a Hermitian matrix. -/
def hermPos (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun x : ℝ => max x 0) A

/-- The negative part of a Hermitian matrix. -/
def hermNeg (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun x : ℝ => max (-x) 0) A

theorem hermPos_posSemidef (A : Matrix n n ℂ) : (hermPos A).PosSemidef := by
  have h : (0 : Matrix n n ℂ) ≤ hermPos A := cfc_nonneg fun x _ => le_max_right x 0
  simpa using Matrix.le_iff.mp h

theorem hermNeg_posSemidef (A : Matrix n n ℂ) : (hermNeg A).PosSemidef := by
  have h : (0 : Matrix n n ℂ) ≤ hermNeg A := cfc_nonneg fun x _ => le_max_right (-x) 0
  simpa using Matrix.le_iff.mp h

/-- **The Jordan decomposition.** -/
theorem hermPos_sub_hermNeg {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermPos A - hermNeg A = A := by
  have hc1 : ContinuousOn (fun x : ℝ => max x 0) (spectrum ℝ A) :=
    (continuous_id.max continuous_const).continuousOn
  have hc2 : ContinuousOn (fun x : ℝ => max (-x) 0) (spectrum ℝ A) :=
    (continuous_neg.max continuous_const).continuousOn
  rw [hermPos, hermNeg, ← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) A hc1 hc2]
  have hfun : (fun x : ℝ => max x 0 - max (-x) 0) = fun x : ℝ => x := by
    funext x
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  rw [hfun]
  exact cfc_id ℝ A hA.isSelfAdjoint

/-- **The two halves carry the whole nuclear norm.** -/
theorem trace_hermPos_add_trace_hermNeg {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hermPos A).trace.re + (hermNeg A).trace.re = finiteMatrixNuclearNorm A := by
  rw [hermPos, hermNeg, trace_cfc_re hA, trace_cfc_re hA,
    finiteMatrixNuclearNorm_isHermitian hA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (hA.eigenvalues i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), add_zero, abs_of_nonneg h]
  · rw [max_eq_right h, max_eq_left (by linarith), zero_add, abs_of_nonpos h]

/-- **A positive trace-preserving map contracts the nuclear norm of a Hermitian matrix.** -/
theorem finiteMatrixNuclearNorm_apply_le {Φ : Matrix n n ℂ → Matrix n n ℂ}
    (hsub : ∀ X Y, Φ (X - Y) = Φ X - Φ Y)
    (hpos : ∀ X : Matrix n n ℂ, X.PosSemidef → (Φ X).PosSemidef)
    (htp : ∀ X : Matrix n n ℂ, (Φ X).trace = X.trace)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    finiteMatrixNuclearNorm (Φ A) ≤ finiteMatrixNuclearNorm A := by
  have hP := hermPos_posSemidef (n := n) A
  have hN := hermNeg_posSemidef (n := n) A
  have hPP : (Φ (hermPos A)).PosSemidef := hpos _ hP
  have hNP : (Φ (hermNeg A)).PosSemidef := hpos _ hN
  have hsplit : Φ A = Φ (hermPos A) - Φ (hermNeg A) := by
    rw [← hsub, hermPos_sub_hermNeg hA]
  have hstep : finiteMatrixNuclearNorm (Φ A)
      ≤ finiteMatrixNuclearNorm (Φ (hermPos A)) + finiteMatrixNuclearNorm (-Φ (hermNeg A)) := by
    rw [hsplit, sub_eq_add_neg]
    exact finiteMatrixNuclearNorm_add_le hPP.isHermitian
      (by simpa using hNP.isHermitian.neg)
  have hnegnorm : finiteMatrixNuclearNorm (-Φ (hermNeg A))
      = finiteMatrixNuclearNorm (Φ (hermNeg A)) := by
    have h1 : (-Φ (hermNeg A))ᴴ * (-Φ (hermNeg A)) = (Φ (hermNeg A))ᴴ * (Φ (hermNeg A)) := by
      simp
    rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, finiteMatrixNuclearNorm_eq_trace_sqrt_re, h1]
  rw [hnegnorm] at hstep
  refine hstep.trans ?_
  rw [finiteMatrixNuclearNorm_posSemidef hPP, finiteMatrixNuclearNorm_posSemidef hNP,
    htp, htp, trace_hermPos_add_trace_hermNeg hA]

end

end GaloisForLFunctions.HTGeometry
