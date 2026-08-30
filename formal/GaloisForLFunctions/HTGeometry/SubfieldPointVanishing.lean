import Mathlib

/-!
# Polynomials vanishing on the points of a subfield

A polynomial with coefficients in an extension field `L`, all of whose values at points of an
infinite subfield `C` vanish, is zero.  Pushing the coefficients through a `C`-linear functional
reduces the statement to `MvPolynomial.funext` over `C`, and the functionals separate `L`.

This is the Zariski-density input of every rational-point separation argument: it lets one pass
from "the identity holds at every `C`-point" to "the identity holds formally".
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C L ι : Type*} [Field C] [Field L] [Algebra C L]

/-- The coefficientwise image of a polynomial under a `C`-linear functional. -/
def coeffPush (φ : L →ₗ[C] C) (P : MvPolynomial ι L) : MvPolynomial ι C :=
  ∑ d ∈ P.support, MvPolynomial.monomial d (φ (MvPolynomial.coeff d P))

theorem coeff_coeffPush (φ : L →ₗ[C] C) (P : MvPolynomial ι L) (e : ι →₀ ℕ) :
    MvPolynomial.coeff e (coeffPush φ P) = φ (MvPolynomial.coeff e P) := by
  classical
  rw [coeffPush, MvPolynomial.coeff_sum]
  by_cases he : e ∈ P.support
  · rw [Finset.sum_eq_single e]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro d _ hde
      rw [MvPolynomial.coeff_monomial, if_neg hde]
    · intro hcon; exact absurd he hcon
  · have hz : MvPolynomial.coeff e P = 0 := by
      by_contra hne
      exact he (MvPolynomial.mem_support_iff.mpr hne)
    rw [hz, map_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hde : d ≠ e := fun hcon => he (hcon ▸ hd)
    rw [MvPolynomial.coeff_monomial, if_neg hde]

theorem eval_coeffPush (φ : L →ₗ[C] C) (P : MvPolynomial ι L) (x : ι → C) :
    MvPolynomial.eval x (coeffPush φ P)
      = φ (MvPolynomial.eval (fun i => algebraMap C L (x i)) P) := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, map_sum]
  have hterm : ∀ d ∈ P.support,
      MvPolynomial.coeff d (coeffPush φ P) * ∏ i ∈ d.support, x i ^ d i
        = φ (MvPolynomial.coeff d P
            * ∏ i ∈ d.support, (algebraMap C L (x i)) ^ d i) := by
    intro d _
    have hprod : ∏ i ∈ d.support, (algebraMap C L (x i)) ^ d i
        = algebraMap C L (∏ i ∈ d.support, x i ^ d i) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
    rw [hprod, coeff_coeffPush]
    have hsm : MvPolynomial.coeff d P * algebraMap C L (∏ i ∈ d.support, x i ^ d i)
        = (∏ i ∈ d.support, x i ^ d i) • MvPolynomial.coeff d P := by
      rw [Algebra.smul_def]; ring
    rw [hsm, map_smul, smul_eq_mul]
    ring
  have hsub : (coeffPush φ P).support ⊆ P.support := by
    intro e he
    by_contra hcon
    have hz : MvPolynomial.coeff e P = 0 := by
      by_contra hne
      exact hcon (MvPolynomial.mem_support_iff.mpr hne)
    exact (MvPolynomial.mem_support_iff.mp he) (by rw [coeff_coeffPush, hz, map_zero])
  have hzero : ∀ d ∈ P.support, d ∉ (coeffPush φ P).support →
      MvPolynomial.coeff d (coeffPush φ P) * ∏ i ∈ d.support, x i ^ d i = 0 := by
    intro d _ hd
    have hz : MvPolynomial.coeff d (coeffPush φ P) = 0 := by
      by_contra hne
      exact hd (MvPolynomial.mem_support_iff.mpr hne)
    rw [hz, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl hterm

/-- **A polynomial over `L` vanishing at every point of an infinite subfield is zero.** -/
theorem mvPolynomial_eq_zero_of_eval_subfield_eq_zero [Infinite C] {P : MvPolynomial ι L}
    (hP : ∀ x : ι → C, MvPolynomial.eval (fun i => algebraMap C L (x i)) P = 0) :
    P = 0 := by
  classical
  have hpush : ∀ φ : L →ₗ[C] C, coeffPush φ P = 0 := by
    intro φ
    refine MvPolynomial.funext ?_
    intro x
    rw [eval_coeffPush, hP x, map_zero]
    simp
  refine MvPolynomial.ext P 0 fun d => ?_
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero C hne
  exact hφ (by rw [← coeff_coeffPush φ P d, hpush φ, MvPolynomial.coeff_zero])

end

end GaloisForLFunctions.HTGeometry
