/-
# Bihomogeneous polynomials in the spectral variables over the coordinate ring

The symmetrised criticality construction lives in the polynomials in the spectral variables whose
coefficients are polynomials in the shell coordinates.  The relevant grading is the total one: a
monomial of spectral degree `a` carries a coefficient homogeneous of coordinate degree `d − a`.
Under simultaneous scaling of the coordinates and of the spectrum, such an object scales by `t^d`.

Main results:
* `IsBihomogeneous` — the total grading.
* `eval₂_smul_of_isBihomogeneous` — **a bihomogeneous object scales by its total degree**.
-/
import GaloisForLFunctions.HTGeometry.ShellCoeffScaling

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- Total-degree grading: the coefficient of a spectral monomial of degree `a` is homogeneous of
coordinate degree `d − a`, and vanishes when `a` exceeds `d`. -/
def IsBihomogeneous (d : ℕ) (A : MvPolynomial (Fin D) (MvPolynomial (Fin N) ℝ)) : Prop :=
  ∀ α : Fin D →₀ ℕ,
    ((A.coeff α).IsHomogeneous (d - ∑ i ∈ α.support, α i)
      ∧ (d < ∑ i ∈ α.support, α i → A.coeff α = 0))

/-- **A bihomogeneous object scales by its total degree** under simultaneous scaling of the
coordinates and of the spectrum. -/
theorem eval₂_smul_of_isBihomogeneous {d : ℕ}
    {A : MvPolynomial (Fin D) (MvPolynomial (Fin N) ℝ)} (hA : IsBihomogeneous d A)
    (θ : Fin N → ℝ) (t : ℝ) (lam : Fin D → ℝ) :
    MvPolynomial.eval₂ (MvPolynomial.eval (fun a => t * θ a)) (fun i => t * lam i) A
      = t ^ d * MvPolynomial.eval₂ (MvPolynomial.eval θ) lam A := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hne : MvPolynomial.coeff α A ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have hle : (∑ i ∈ α.support, α i) ≤ d := by
    by_contra hc
    exact hne ((hA α).2 (Nat.lt_of_not_le hc))
  have hcoeff : MvPolynomial.eval (fun a => t * θ a) (MvPolynomial.coeff α A)
      = t ^ (d - ∑ i ∈ α.support, α i) * MvPolynomial.eval θ (MvPolynomial.coeff α A) :=
    eval_smul_of_isHomogeneous (hA α).1 t θ
  have hmon : (∏ i ∈ α.support, (t * lam i) ^ α i)
      = t ^ (∑ i ∈ α.support, α i) * ∏ i ∈ α.support, (lam i) ^ α i := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow t (lam i) (α i)
  have hd : t ^ (d - ∑ i ∈ α.support, α i) * t ^ (∑ i ∈ α.support, α i) = t ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hcoeff, hmon, ← hd]
  ring

end

end GaloisForLFunctions.HTGeometry
