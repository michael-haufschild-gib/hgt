/-
# Hurwitz rational-tail gate — algebraic pole-tower injectivity

This proves the algebraic part of the polylog pole-tower argument in
`hurwitz-quadratic-all-n-tail-independence.md`: once the highest pole
coefficient has the form of a polynomial in the pole locations `2πim`, vanishing
at infinitely many nonzero pole locations forces every top coefficient to be
zero.
-/
import GaloisForLFunctions.Hurwitz.DescentAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Polynomial

namespace HurwitzPolylogPoleTower

noncomputable section

/-- The nonzero pole spacing `2πi`. -/
def twoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem twoPiI_ne_zero : twoPiI ≠ 0 := by
  unfold twoPiI
  exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero

/-- The highest-pole coefficient polynomial
`Σ_j a_j γ_j X^j`.  In the card, `γ_j = Γ(1-s-j)`, nonzero for `s ∉ ℤ`. -/
noncomputable def polePolynomial {M : ℕ} (gamma a : Fin (M + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (M + 1), C (a j * gamma j) * X ^ (j : ℕ)

/-- A polynomial vanishing at every positive `2πi(n+1)` is zero. -/
theorem eq_zero_of_pole_roots {p : Polynomial ℂ}
    (hroot : ∀ n : ℕ, p.eval (twoPiI * ((n + 1 : ℕ) : ℂ)) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hUniv : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  have hinj : Set.InjOn (fun n : ℕ => twoPiI * ((n + 1 : ℕ) : ℂ)) Set.univ := by
    intro a _ b _ h
    have hcast : ((a + 1 : ℕ) : ℂ) = ((b + 1 : ℕ) : ℂ) :=
      mul_left_cancel₀ twoPiI_ne_zero h
    have hnat : a + 1 = b + 1 := Nat.cast_injective hcast
    omega
  have himg : ((fun n : ℕ => twoPiI * ((n + 1 : ℕ) : ℂ)) '' (Set.univ : Set ℕ)).Infinite :=
    hUniv.image hinj
  refine Set.Infinite.mono ?_ himg
  rintro x ⟨n, _hn, rfl⟩
  exact hroot n

/-- Coefficient extraction from `polePolynomial`. -/
theorem polePolynomial_coeff {M : ℕ} (gamma a : Fin (M + 1) → ℂ) (j : Fin (M + 1)) :
    (polePolynomial gamma a).coeff (j : ℕ) = a j * gamma j := by
  unfold polePolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow]
    simp
  · intro b _ hb
    have hne : (j : ℕ) ≠ (b : ℕ) := by
      intro hnat
      exact hb (Fin.ext hnat.symm)
    rw [Polynomial.coeff_C_mul_X_pow]
    simp [hne]
  · intro h
    simp at h

/-- Pole-tower injectivity in polynomial form. -/
theorem coefficients_zero_of_polePolynomial_roots {M : ℕ} {gamma a : Fin (M + 1) → ℂ}
    (hgamma : ∀ j, gamma j ≠ 0)
    (hroot : ∀ n : ℕ, (polePolynomial gamma a).eval (twoPiI * ((n + 1 : ℕ) : ℂ)) = 0) :
    ∀ j, a j = 0 := by
  have hp : polePolynomial gamma a = 0 := eq_zero_of_pole_roots hroot
  intro j
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (j : ℕ)) hp
  change (polePolynomial gamma a).coeff (j : ℕ) = (0 : Polynomial ℂ).coeff (j : ℕ) at hc
  rw [polePolynomial_coeff] at hc
  simp only [coeff_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_right (hgamma j)

/-- Pole-tower injectivity in the expanded sum form used by the paper proof. -/
theorem coefficients_zero_of_pole_sum_roots {M : ℕ} {gamma a : Fin (M + 1) → ℂ}
    (hgamma : ∀ j, gamma j ≠ 0)
    (hroot : ∀ n : ℕ,
      (∑ j : Fin (M + 1), a j * gamma j * (twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) :
    ∀ j, a j = 0 := by
  apply coefficients_zero_of_polePolynomial_roots hgamma
  intro n
  simpa [polePolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, mul_assoc, mul_left_comm,
    mul_comm] using hroot n

end

end HurwitzPolylogPoleTower

namespace HurwitzPolylogPoleTower

noncomputable section

/-- Polynomial-valued pole-tower injectivity.  If every coefficient degree gives
an expanded pole-root identity, then every coefficient polynomial is zero. -/
theorem polynomials_zero_of_pole_sum_roots {M : ℕ} {gamma : Fin (M + 1) → ℂ}
    {p : Fin (M + 1) → Polynomial ℂ}
    (hgamma : ∀ j, gamma j ≠ 0)
    (hroot : ∀ (d n : ℕ),
      (∑ j : Fin (M + 1),
        (p j).coeff d * gamma j *
          (twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) :
    ∀ j, p j = 0 := by
  intro j
  apply Polynomial.ext
  intro d
  exact coefficients_zero_of_pole_sum_roots hgamma (fun n => hroot d n) j

end

end HurwitzPolylogPoleTower

namespace HurwitzPolylogPoleTower

/-- The actual fractional-polylog pole coefficients `Gamma(1 - s - j)` are
nonzero whenever `s` is not an integer. -/
theorem gamma_one_sub_shift_ne_zero {M : ℕ} {s : ℂ}
    (hs : ∀ k : ℤ, s ≠ (k : ℂ)) :
    ∀ j : Fin (M + 1), Complex.Gamma (1 - s - (j : ℂ)) ≠ 0 := by
  intro j
  apply Complex.Gamma_ne_zero
  intro m hbad
  have hs_eq_nat : s = (m : ℂ) + 1 - ((j : ℕ) : ℂ) := by
    linear_combination -hbad
  have hs_eq : s = (((m : ℤ) + 1 - ((j : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_natCast]
    exact hs_eq_nat
  exact hs (((m : ℤ) + 1 - ((j : ℕ) : ℤ) : ℤ)) hs_eq

end HurwitzPolylogPoleTower

namespace HurwitzPolylogPoleTower

/-- Actual Gamma-coefficient scalar pole-tower injectivity for the Hurwitz
rational-tail proof. -/
theorem coefficients_zero_of_gamma_pole_sum_roots {M : ℕ} {s : ℂ} {a : Fin (M + 1) → ℂ}
    (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    (hroot : ∀ n : ℕ,
      (∑ j : Fin (M + 1),
        a j * Complex.Gamma (1 - s - (j : ℂ)) *
          (twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) :
    ∀ j, a j = 0 := by
  exact coefficients_zero_of_pole_sum_roots (gamma_one_sub_shift_ne_zero hs) hroot

/-- Actual Gamma-coefficient polynomial-valued pole-tower injectivity for the
Hurwitz rational-tail proof. -/
theorem polynomials_zero_of_gamma_pole_sum_roots {M : ℕ} {s : ℂ}
    {p : Fin (M + 1) → Polynomial ℂ}
    (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    (hroot : ∀ (d n : ℕ),
      (∑ j : Fin (M + 1),
        (p j).coeff d * Complex.Gamma (1 - s - (j : ℂ)) *
          (twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (j : ℕ)) = 0) :
    ∀ j, p j = 0 := by
  exact polynomials_zero_of_pole_sum_roots (gamma_one_sub_shift_ne_zero hs) hroot

end HurwitzPolylogPoleTower
