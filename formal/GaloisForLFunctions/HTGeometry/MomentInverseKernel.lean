import GaloisForLFunctions.HTGeometry.MomentNormalBlockDividedDifference
import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem

/-!
# Reproduction by an invertible moment section

An invertible Hankel section, including an indefinite section, has a unique
polynomial reproducing each evaluation. A normalized displacement identity
propagates reproduction from the constant moment to every lower moment row.
These facts identify source-constructed kernels without assuming positivity.
-/

open Polynomial Matrix
open scoped BigOperators
namespace HTGeometry
noncomputable section

/-- Polynomial whose coefficient vector is the inverse Hankel image of the
monomial evaluation vector. -/
def momentInverseKernel (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ[X] :=
  ofFn n ((momentHankelMatrix s n)⁻¹ *ᵥ fun i : Fin n => x ^ (i : ℕ))

theorem momentInverseKernel_degree_lt (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (momentInverseKernel s n x).degree < (n : WithBot ℕ) :=
  ofFn_degree_lt _

theorem momentInverseKernel_monomial {s : ℕ → ℝ} {n : ℕ}
    (hdet : (momentHankelMatrix s n).det ≠ 0) (x : ℝ) (i : Fin n) :
    momentFunctional s (X ^ (i : ℕ) * momentInverseKernel s n x) = x ^ (i : ℕ) := by
  rw [momentInverseKernel, momentFunctional_X_pow_ofFn_row, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- Reproduction on monomials gives reproduction on the whole finite section. -/
theorem momentFunctional_mul_eq_eval_of_monomial {s : ℕ → ℝ} {n : ℕ}
    {K : ℝ[X]} {x : ℝ}
    (hrow : ∀ i < n, momentFunctional s (X ^ i * K) = x ^ i)
    (p : ℝ[X]) (hp : p.degree < (n : WithBot ℕ)) :
    momentFunctional s (p * K) = p.eval x := by
  have h := momentFunctional_X_pow_mul_mul_eq_sum s K p 0
  simp only [pow_zero, one_mul, zero_add] at h
  rw [mul_comm, h, eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hrow i (by
    exact_mod_cast lt_of_le_of_lt (le_degree_of_ne_zero (mem_support_iff.mp hi)) hp)]

theorem momentInverseKernel_reproduces {s : ℕ → ℝ} {n : ℕ}
    (hdet : (momentHankelMatrix s n).det ≠ 0) (x : ℝ)
    (p : ℝ[X]) (hp : p.degree < (n : WithBot ℕ)) :
    momentFunctional s (p * momentInverseKernel s n x) = p.eval x :=
  momentFunctional_mul_eq_eval_of_monomial
    (fun i hi => momentInverseKernel_monomial hdet x ⟨i, hi⟩) p hp

/-- A finite reproducing polynomial is the inverse-Hankel kernel. -/
theorem eq_momentInverseKernel_of_monomial {s : ℕ → ℝ} {n : ℕ}
    (hdet : (momentHankelMatrix s n).det ≠ 0) {K : ℝ[X]} {x : ℝ}
    (hdeg : K.degree < (n : WithBot ℕ))
    (hrow : ∀ i < n, momentFunctional s (X ^ i * K) = x ^ i) :
    K = momentInverseKernel s n x := by
  apply sub_eq_zero.mp
  apply momentSectionKernel_eq_zero_of_det_ne_zero hdet
  refine ⟨lt_of_le_of_lt (degree_sub_le _ _)
    (max_lt hdeg (momentInverseKernel_degree_lt s n x)), ?_⟩
  intro i hi
  rw [mul_sub, momentFunctional_sub, hrow i hi,
    momentInverseKernel_monomial hdet x ⟨i, hi⟩, sub_self]

/-- A normalized displacement orthogonal to the lower rows forces all the
evaluation moments. This uses no sign property of the functional. -/
theorem moment_monomial_of_displacement {s : ℕ → ℝ} {n : ℕ}
    {K : ℝ[X]} {x : ℝ} (hbase : momentFunctional s K = 1)
    (hshift : ∀ i, i + 1 < n →
      momentFunctional s (X ^ i * ((X - C x) * K)) = 0) :
    ∀ i < n, momentFunctional s (X ^ i * K) = x ^ i := by
  intro i
  induction i with
  | zero => intro _; simpa using hbase
  | succ i ih =>
    intro hi
    have hs := hshift i hi
    have he : X ^ i * ((X - C x) * K) =
        X ^ (i + 1) * K - x • (X ^ i * K) := by
      rw [smul_eq_C_mul, pow_succ]
      ring
    rw [he, momentFunctional_sub, momentFunctional_smul, ih (by omega)] at hs
    calc
      _ = x * x ^ i := sub_eq_zero.mp hs
      _ = x ^ (i + 1) := by rw [pow_succ]; ring

end
end HTGeometry
