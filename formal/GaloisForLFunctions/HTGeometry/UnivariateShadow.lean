import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The univariate shadow of a jet polynomial

A differential polynomial that involves no jet variable is a polynomial in the independent variable
alone, and its *univariate shadow* — the evaluation sending the zeroth slot to `X` and every jet slot
to `0` — is then nonzero.

The proof is coefficient extraction.  If every monomial of `P` is supported on the zeroth slot, then
distinct monomials have distinct total degrees in that slot, so the shadow's coefficient at
`μ 0` is exactly the coefficient of `P` at `μ`.

This is the base case of the separant selection: a minimal nonzero differential relation cannot be
free of jets, because its shadow would then be a nonzero polynomial and the relation would not hold.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [DecidableEq σ] {k : Type*} [CommRing k]

/-- The univariate shadow: send the distinguished slot to `X` and every other slot to `0`. -/
noncomputable def univShadow (i₀ : σ) (P : MvPolynomial σ k) : Polynomial k :=
  MvPolynomial.aeval (fun i : σ => if i = i₀ then Polynomial.X else 0) P

theorem univShadow_eq_sum (i₀ : σ) (P : MvPolynomial σ k) :
    univShadow i₀ P = ∑ μ ∈ P.support,
      Polynomial.C (MvPolynomial.coeff μ P)
        * ∏ i ∈ μ.support, (if i = i₀ then (Polynomial.X : Polynomial k) else 0) ^ μ i := by
  rw [univShadow, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rfl

/-- On a monomial supported at the distinguished slot the shadow is the pure power. -/
theorem shadow_monomial (i₀ : σ) {μ : σ →₀ ℕ} (hμ : ∀ i, i ≠ i₀ → μ i = 0) :
    (∏ i ∈ μ.support, (if i = i₀ then (Polynomial.X : Polynomial k) else 0) ^ μ i)
      = Polynomial.X ^ μ i₀ := by
  classical
  by_cases h0 : μ i₀ = 0
  · have hzero : μ = 0 := by
      ext i
      by_cases hi : i = i₀
      · subst hi; simpa using h0
      · simpa using hμ i hi
    rw [hzero]
    simp
  · have hsupp : μ.support = {i₀} := by
      ext i
      simp only [Finsupp.mem_support_iff, Finset.mem_singleton]
      constructor
      · intro hi
        by_contra hne
        exact hi (hμ i hne)
      · intro hi
        subst hi
        exact h0
    rw [hsupp, Finset.prod_singleton, if_pos rfl]

/-- **A jet-free polynomial has a nonzero univariate shadow.** -/
theorem univShadow_ne_zero (i₀ : σ) {P : MvPolynomial σ k} (hP : P ≠ 0)
    (hvars : ∀ μ ∈ P.support, ∀ i, i ≠ i₀ → μ i = 0) : univShadow i₀ P ≠ 0 := by
  classical
  have hsupne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact hP (MvPolynomial.support_eq_empty.mp hc)
  obtain ⟨μ₀, hμ₀⟩ := hsupne
  have hpow : univShadow i₀ P
      = ∑ μ ∈ P.support,
        Polynomial.C (MvPolynomial.coeff μ P) * Polynomial.X ^ μ i₀ := by
    rw [univShadow_eq_sum]
    exact Finset.sum_congr rfl fun μ hμ => by
      rw [shadow_monomial i₀ (hvars μ hμ)]
  have hinj : ∀ μ₁ ∈ P.support, ∀ μ₂ ∈ P.support, μ₁ i₀ = μ₂ i₀ → μ₁ = μ₂ := by
    intro μ₁ h₁ μ₂ h₂ heq
    ext i
    by_cases hi : i = i₀
    · subst hi; exact heq
    · rw [hvars μ₁ h₁ i hi, hvars μ₂ h₂ i hi]
  have hcoeff : Polynomial.coeff (univShadow i₀ P) (μ₀ i₀) = MvPolynomial.coeff μ₀ P := by
    rw [hpow, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single μ₀]
    · simp
    · intro μ hμ hne
      have hne2 : μ₀ i₀ ≠ μ i₀ := fun hc => hne (hinj μ hμ μ₀ hμ₀ hc.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne2]
    · intro hcon
      exact absurd hμ₀ hcon
  intro hzero
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hμ₀) hcoeff.symm

end GaloisForLFunctions.HTGeometry
