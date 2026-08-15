import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature

/-!
# The Gauss quadrature resolvent and its error factor

The Gauss quadrature sum attached to a positive moment form is a rational function of the spectral
parameter, and its value is completely determined by the orthogonal polynomial: with
`p = monicOrtho s (n+1)` and nodes `x_i` with Christoffel weights `ω_i`,

`∑ ω_i / (x_i - z) = L((p(z)² - p(X)²)/(X - z)) / p(z)²`.

The numerator on the right is a genuine polynomial of degree `2n+1`, so the identity is Gauss
exactness applied to it.  It is the algebraic core of the Padé description of a moment resolvent:
the quadrature sum is the `[n/n+1]` Padé approximant, and the error is carried by the same divided
square with the orthogonal polynomial squared in the denominator.
-/

open Polynomial

noncomputable section

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## The divided square -/

/-- The polynomial `X ↦ (p(z)² - p(X)²)/(X - z)`. -/
def dividedSquare (p : Polynomial ℝ) (z : ℝ) : Polynomial ℝ :=
  (Polynomial.C (p.eval z ^ 2) - p ^ 2) /ₘ (Polynomial.X - Polynomial.C z)

theorem dividedSquare_mul (p : Polynomial ℝ) (z : ℝ) :
    (Polynomial.X - Polynomial.C z) * dividedSquare p z
      = Polynomial.C (p.eval z ^ 2) - p ^ 2 := by
  have hroot : (Polynomial.C (p.eval z ^ 2) - p ^ 2).IsRoot z := by
    simp [Polynomial.IsRoot]
  have hdvd : (Polynomial.X - Polynomial.C z) ∣ (Polynomial.C (p.eval z ^ 2) - p ^ 2) :=
    Polynomial.dvd_iff_isRoot.2 hroot
  rw [dividedSquare]
  exact (Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot)

theorem eval_dividedSquare (p : Polynomial ℝ) (z x : ℝ) (hx : x ≠ z) :
    (dividedSquare p z).eval x = (p.eval z ^ 2 - p.eval x ^ 2) / (x - z) := by
  have h := congrArg (fun q : Polynomial ℝ => q.eval x) (dividedSquare_mul p z)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow] at h
  have hne : x - z ≠ 0 := sub_ne_zero.2 hx
  field_simp
  linarith [h]

theorem natDegree_dividedSquare_lt (p : Polynomial ℝ) (z : ℝ) (hp : 0 < p.natDegree) :
    (dividedSquare p z).natDegree < 2 * p.natDegree := by
  have hmonic : (Polynomial.X - Polynomial.C z).Monic := Polynomial.monic_X_sub_C z
  have hnd : (dividedSquare p z).natDegree
      = (Polynomial.C (p.eval z ^ 2) - p ^ 2).natDegree - 1 := by
    rw [dividedSquare, Polynomial.natDegree_divByMonic _ hmonic, Polynomial.natDegree_X_sub_C]
  have hle : (Polynomial.C (p.eval z ^ 2) - p ^ 2).natDegree ≤ 2 * p.natDegree := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    exact ⟨Nat.zero_le _, le_of_eq (Polynomial.natDegree_pow p 2 ▸ by ring)⟩
  omega

theorem degree_dividedSquare_lt (p : Polynomial ℝ) (z : ℝ) (hp : 0 < p.natDegree) :
    (dividedSquare p z).degree < ((2 * p.natDegree : ℕ) : WithBot ℕ) := by
  have hnd := natDegree_dividedSquare_lt p z hp
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast hnd

/-! ## The quadrature resolvent -/

/-- **The Gauss quadrature resolvent is the divided square over the orthogonal square.**
Gauss exactness applied to the degree-`2n+1` polynomial `(p(z)² - p(X)²)/(X - z)`. -/
theorem momentFunctional_dividedSquare (h : PositiveMomentForm s) (n : ℕ) (z : ℝ)
    (hz : ∀ x ∈ gaussNodes s n, x ≠ z) :
    momentFunctional s (dividedSquare (monicOrtho s (n + 1)) z)
      = (monicOrtho s (n + 1)).eval z ^ 2
        * ∑ x ∈ gaussNodes s n, christoffel s n x / (x - z) := by
  have hdegp : (monicOrtho s (n + 1)).natDegree = n + 1 := by
    have hd := monicOrtho_degree s (n + 1)
    rw [Polynomial.degree_eq_natDegree (monicOrtho_ne_zero s (n + 1))] at hd
    exact_mod_cast hd
  have hdeg : (dividedSquare (monicOrtho s (n + 1)) z).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    have h1 := degree_dividedSquare_lt (monicOrtho s (n + 1)) z (by omega)
    rw [hdegp] at h1
    have h2 : ((2 * (n + 1) : ℕ) : WithBot ℕ) = ((2 * n + 2 : ℕ) : WithBot ℕ) := by
      norm_cast
    rwa [h2] at h1
  rw [momentFunctional_eq_gaussSum h n _ hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hroot : (monicOrtho s (n + 1)).eval x = 0 := (mem_gaussNodes_iff n x).1 hx
  have hne : x - z ≠ 0 := sub_ne_zero.2 (hz x hx)
  rw [eval_dividedSquare _ _ _ (hz x hx), hroot]
  field_simp
  ring

/-- The same identity solved for the quadrature sum. -/
theorem gaussSum_resolvent_eq (h : PositiveMomentForm s) (n : ℕ) (z : ℝ)
    (hz : ∀ x ∈ gaussNodes s n, x ≠ z) (hp : (monicOrtho s (n + 1)).eval z ≠ 0) :
    (∑ x ∈ gaussNodes s n, christoffel s n x / (x - z))
      = momentFunctional s (dividedSquare (monicOrtho s (n + 1)) z)
        / (monicOrtho s (n + 1)).eval z ^ 2 := by
  rw [momentFunctional_dividedSquare h n z hz]
  field_simp

end HTGeometry

end
