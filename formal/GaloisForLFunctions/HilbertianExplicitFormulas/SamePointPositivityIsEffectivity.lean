import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.Basic

/-!
# Same-point positivity is effectivity

A Hilbertian explicit formula compares an explicit statistic with the same-point form
`∑ m_ρ |F(ρ)|²`. That form is a Hilbert norm only when every multiplicity is nonnegative. For a
signed divisor (zeros and poles, as for twins such as `ζ(2s)/ζ(s)`) a single negative multiplicity
already makes it indefinite on polynomial tests: the Lagrange polynomial vanishing at every other
point isolates it. So the Hilbertian side of the theory exists exactly for effective divisors.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-- Same-point form of a signed finite divisor. -/
def signedSamePointForm (S : Finset ℂ) (m : ℂ → ℝ) (F : ℂ → ℂ) : ℝ :=
  ∑ ρ ∈ S, m ρ * ‖F ρ‖ ^ 2

/-- The Lagrange polynomial vanishing on `S` except at `ρ₀`. -/
def isolatingPolynomial (S : Finset ℂ) (ρ₀ : ℂ) : ℂ[X] :=
  ∏ ρ ∈ S.erase ρ₀, (X - C ρ)

theorem eval_isolatingPolynomial_of_ne {S : Finset ℂ} {ρ₀ ρ : ℂ} (hρ : ρ ∈ S) (hne : ρ ≠ ρ₀) :
    (isolatingPolynomial S ρ₀).eval ρ = 0 := by
  rw [isolatingPolynomial, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hρ⟩) (by simp)

theorem eval_isolatingPolynomial_self_ne_zero (S : Finset ℂ) (ρ₀ : ℂ) :
    (isolatingPolynomial S ρ₀).eval ρ₀ ≠ 0 := by
  rw [isolatingPolynomial, eval_prod, Finset.prod_ne_zero_iff]
  intro ρ hρ
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact (Finset.ne_of_mem_erase hρ).symm

/-- On the isolating polynomial the same-point form reads off one multiplicity. -/
theorem signedSamePointForm_isolating {S : Finset ℂ} (m : ℂ → ℝ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ S) :
    signedSamePointForm S m (fun z => (isolatingPolynomial S ρ₀).eval z) =
      m ρ₀ * ‖(isolatingPolynomial S ρ₀).eval ρ₀‖ ^ 2 := by
  rw [signedSamePointForm, Finset.sum_eq_single ρ₀]
  · intro ρ hρ hne
    rw [eval_isolatingPolynomial_of_ne hρ hne, norm_zero]
    ring
  · intro h; exact absurd h₀ h

/-- **Effectivity.** The same-point form of a signed finite divisor is nonnegative on all polynomial
tests exactly when every multiplicity is nonnegative. -/
theorem signedSamePointForm_nonneg_iff (S : Finset ℂ) (m : ℂ → ℝ) :
    (∀ P : ℂ[X], 0 ≤ signedSamePointForm S m (fun z => P.eval z)) ↔ ∀ ρ ∈ S, 0 ≤ m ρ := by
  constructor
  · intro hpos ρ₀ h₀
    by_contra hneg
    have hlt : m ρ₀ < 0 := lt_of_not_ge hneg
    have hform := hpos (isolatingPolynomial S ρ₀)
    rw [signedSamePointForm_isolating m h₀] at hform
    have hev : 0 < ‖(isolatingPolynomial S ρ₀).eval ρ₀‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (eval_isolatingPolynomial_self_ne_zero S ρ₀)) 2
    nlinarith
  · intro hm P
    exact Finset.sum_nonneg fun ρ hρ => mul_nonneg (hm ρ hρ) (sq_nonneg _)

/-- A divisor with a pole has an indefinite same-point form: some polynomial test is negative. -/
theorem exists_signedSamePointForm_neg {S : Finset ℂ} {m : ℂ → ℝ} {ρ₀ : ℂ} (h₀ : ρ₀ ∈ S)
    (hneg : m ρ₀ < 0) : ∃ P : ℂ[X], signedSamePointForm S m (fun z => P.eval z) < 0 := by
  refine ⟨isolatingPolynomial S ρ₀, ?_⟩
  rw [signedSamePointForm_isolating m h₀]
  exact mul_neg_of_neg_of_pos hneg
    (pow_pos (norm_pos_iff.mpr (eval_isolatingPolynomial_self_ne_zero S ρ₀)) 2)

end

end GaloisForLFunctions.HilbertianExplicitFormulas
