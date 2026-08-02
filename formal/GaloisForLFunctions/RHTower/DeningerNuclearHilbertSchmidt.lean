import GaloisForLFunctions.RHTower.DeningerHilbertSchmidtAdjoint

/-!
# A nuclear operator on a Hilbert space is Hilbert–Schmidt

If an operator is nuclear then so is the composite with its adjoint, which is therefore trace
class.  Pairing a trace-class operator against an orthonormal family is dominated by the trace
norm, and the pairing of that composite against a Hilbert basis is exactly the family of squared
norms of the images of the basis.  So those squares have uniformly bounded partial sums and the
operator is Hilbert–Schmidt.

Together with the converse direction this identifies, on Hilbert spaces, the nuclear operators
inside the Hilbert–Schmidt ones.

* `DeningerIsNuclear.isHilbertSchmidtOn` : a nuclear operator is Hilbert–Schmidt.
-/

namespace RHTower

open ContinuousLinearMap

section NuclearHilbertSchmidt

variable {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pairing of `T* T` against a vector is the squared norm of its image. -/
theorem deningerInner_adjoint_comp (T : H →L[ℂ] H) (x : H) :
    (inner ℂ x (((ContinuousLinearMap.adjoint T).comp T) x) : ℂ)
      = ((‖T x‖ ^ 2 : ℝ) : ℂ) := by
  show (inner ℂ x (ContinuousLinearMap.adjoint T (T x)) : ℂ) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (T x)]
  norm_cast

/-- **A nuclear operator on a Hilbert space is Hilbert–Schmidt.** -/
theorem DeningerIsNuclear.isHilbertSchmidtOn (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : DeningerIsNuclear T) : DeningerIsHilbertSchmidtOn b T := by
  classical
  have hSnuc : DeningerIsNuclear ((ContinuousLinearMap.adjoint T).comp T) :=
    hT.compL (ContinuousLinearMap.adjoint T)
  have hcpt : IsCompactOperator ((ContinuousLinearMap.adjoint T).comp T) :=
    hSnuc.isCompactOperator
  have hsum1 : Summable fun n => approxNumber ((ContinuousLinearMap.adjoint T).comp T) n := by
    have hmem := hSnuc.memSchattenClass_one
    rw [MemSchattenClass] at hmem
    refine hmem.congr fun n => ?_
    exact Real.rpow_one _
  have horth : Orthonormal ℂ (b : ι → H) := b.orthonormal
  have hg1 : ∀ n, (b n : H) = 0 ∨ ‖(b n : H)‖ = 1 := fun n => Or.inr (horth.1 n)
  have hgo : ∀ m n, m ≠ n → (inner ℂ (b m) (b n) : ℂ) = 0 := fun _ _ h => horth.2 h
  refine summable_of_sum_le (c := traceNorm H ((ContinuousLinearMap.adjoint T).comp T))
    (fun n => by positivity) fun s => ?_
  have hkey := sum_norm_inner_le_traceNorm hcpt hsum1 hg1 hgo hg1 hgo s
  refine le_trans (le_of_eq ?_) hkey
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [deningerInner_adjoint_comp T (b n)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end NuclearHilbertSchmidt

end RHTower

