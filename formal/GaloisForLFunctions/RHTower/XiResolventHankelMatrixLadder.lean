import GaloisForLFunctions.RHTower.XiResolventArithmeticTarget

/-!
# The certificate ladder: RH as positive semidefiniteness of finite arithmetic matrices

The resolvent Hankel criterion is packaged in matrix form: with
`(xiResolventHankelMatrix N X) i j = Re (R_(i+j) X)` — real numbers, and arithmetic ones, since
`R_0` is the Euler-ray value of `logDeriv xi` and each `R_(n+1)` is `-R_n'/(n+1)` — the Riemann
hypothesis is equivalent to

`∀ N, (xiResolventHankelMatrix N X).PosSemidef`

at any single shift `X ≥ 0`.  Each rung `N` is a finite positivity claim about finitely many
explicitly computable real numbers.  By Favard's correspondence the rung-`N` certificate is the
first `N` three-term recurrence coefficients of the orthogonal polynomials of the zero measure —
equivalently the coefficients of the Stieltjes continued fraction of the Euler-ray response —
so the ladder is the J-fraction positivity of one explicit arithmetic function, rung by rung.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- The `N`-th resolvent Hankel matrix at shift `X`: the moment matrix of the divisor functional
in the monomial basis. -/
def xiResolventHankelMatrix (N : ℕ) (X : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (xiResolventMoment ((i : ℕ) + (j : ℕ)) X).re

theorem xiResolventHankelMatrix_isHermitian (N : ℕ) (X : ℝ) :
    (xiResolventHankelMatrix N X).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, xiResolventHankelMatrix, star_trivial]
  rw [Nat.add_comm]

/-- The Hankel quadratic form is the matrix quadratic form of the truncated coefficient
vector. -/
theorem dotProduct_xiResolventHankelMatrix_mulVec (N : ℕ) (X : ℝ) (a : ℕ → ℝ) :
    (fun i : Fin N => a i) ⬝ᵥ (xiResolventHankelMatrix N X *ᵥ (fun i : Fin N => a i)) =
      (xiResolventHankelForm N a X).re := by
  rw [xiResolventHankelForm_re]
  simp only [dotProduct, Matrix.mulVec, xiResolventHankelMatrix]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑ k ∈ Finset.range N, a j * a k * (xiResolventMoment (j + k) X).re) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => a (i : ℕ) * a k * (xiResolventMoment ((i : ℕ) + k) X).re) N]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The certificate ladder**: RH holds iff every finite resolvent Hankel matrix at one shift is
positive semidefinite. -/
theorem riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ N : ℕ, (xiResolventHankelMatrix N X).PosSemidef := by
  rw [riemannHypothesis_iff_forall_xiResolventHankelForm_re_nonneg hX]
  constructor
  · intro h N
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨xiResolventHankelMatrix_isHermitian N X, fun x => ?_⟩
    have hstar : (star x : Fin N → ℝ) = x := by
      funext i
      simp
    rw [hstar]
    have hx : x = fun i : Fin N => (fun n : ℕ => if hn : n < N then x ⟨n, hn⟩ else 0) i := by
      funext i
      simp [i.isLt]
    have hbridge := dotProduct_xiResolventHankelMatrix_mulVec N X
      (fun n : ℕ => if hn : n < N then x ⟨n, hn⟩ else 0)
    rw [← hx] at hbridge
    rw [hbridge]
    exact h N _
  · intro h N a
    have h2 := (h N).dotProduct_mulVec_nonneg (fun i : Fin N => a i)
    have hstar : (star (fun i : Fin N => a (i : ℕ)) : Fin N → ℝ) =
        fun i : Fin N => a (i : ℕ) := by
      funext i
      simp
    rw [hstar, dotProduct_xiResolventHankelMatrix_mulVec] at h2
    exact h2

/-- Under RH every rung of the Hankel determinant ladder is nonnegative. -/
theorem xiResolventHankelMatrix_det_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) (N : ℕ) :
    0 ≤ (xiResolventHankelMatrix N X).det :=
  ((riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef hX).mp hRH N).det_nonneg

end

end RHTower
