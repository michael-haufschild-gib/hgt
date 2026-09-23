import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Coefficient-sign cones for finite moment functionals

A polynomial whose coefficients have one weak sign has a square with coefficientwise
nonnegative coefficients. Consequently, a finite positive prefix of a moment sequence controls
the square-moment functional for every such polynomial of bounded degree.
-/

open Polynomial

namespace HTGeometry

noncomputable section

/-- All coefficients of a real polynomial have one weak sign. -/
def PolynomialCoeffwiseOneSign (p : Polynomial ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ p.coeff k) ∨ (∀ k : ℕ, p.coeff k ≤ 0)

/-- The coefficient convolution of a polynomial with itself is nonnegative. -/
def PolynomialSquareCoeffNonnegative (p : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, 0 ≤ (p ^ (2 : ℕ)).coeff k

/-- Squaring a coefficientwise one-sign polynomial produces nonnegative coefficients. -/
theorem coeff_sq_nonneg_of_coeffwiseOneSign
    {p : Polynomial ℝ} (hp : PolynomialCoeffwiseOneSign p) (k : ℕ) :
    0 ≤ (p ^ (2 : ℕ)).coeff k := by
  rw [pow_two, Polynomial.coeff_mul]
  rcases hp with hp | hp
  · exact Finset.sum_nonneg fun ij _ =>
      mul_nonneg (hp ij.1) (hp ij.2)
  · exact Finset.sum_nonneg fun ij _ =>
      mul_nonneg_of_nonpos_of_nonpos (hp ij.1) (hp ij.2)

/-- Coefficientwise one-sign polynomials lie in the square-coefficient cone. -/
theorem polynomialSquareCoeffNonnegative_of_coeffwiseOneSign
    {p : Polynomial ℝ} (hp : PolynomialCoeffwiseOneSign p) :
    PolynomialSquareCoeffNonnegative p :=
  coeff_sq_nonneg_of_coeffwiseOneSign hp

/-- A nonnegative moment prefix through order `2d` is nonnegative on the square of every
bounded-degree polynomial whose self-convolution coefficients are nonnegative. -/
theorem momentFunctional_sq_nonneg_of_squareCoeffNonnegative
    (s : ℕ → ℝ) {d : ℕ} {p : Polynomial ℝ}
    (hdegree : p.natDegree ≤ d)
    (hp : PolynomialSquareCoeffNonnegative p)
    (hs : ∀ k : ℕ, k ≤ 2 * d → 0 ≤ s k) :
    0 ≤ momentFunctional s (p ^ (2 : ℕ)) := by
  rw [momentFunctional_eq_support_sum]
  apply Finset.sum_nonneg
  intro k hk
  apply mul_nonneg (hp k)
  apply hs k
  have hkdegree : k ≤ (p ^ (2 : ℕ)).natDegree :=
    Polynomial.le_natDegree_of_mem_supp k hk
  rw [Polynomial.natDegree_pow] at hkdegree
  exact hkdegree.trans (Nat.mul_le_mul_left 2 hdegree)

/-- A nonnegative moment prefix through order `2d` is positive on squares of all
coefficientwise one-sign polynomials of degree at most `d`. -/
theorem momentFunctional_sq_nonneg_of_coeffwiseOneSign
    (s : ℕ → ℝ) {d : ℕ} {p : Polynomial ℝ}
    (hdegree : p.natDegree ≤ d)
    (hp : PolynomialCoeffwiseOneSign p)
    (hs : ∀ k : ℕ, k ≤ 2 * d → 0 ≤ s k) :
    0 ≤ momentFunctional s (p ^ (2 : ℕ)) :=
  momentFunctional_sq_nonneg_of_squareCoeffNonnegative s hdegree
    (polynomialSquareCoeffNonnegative_of_coeffwiseOneSign hp) hs

/-- A strictly positive moment prefix is strictly positive on every nonzero bounded-degree
polynomial whose self-convolution coefficients are nonnegative. -/
theorem momentFunctional_sq_pos_of_squareCoeffNonnegative
    (s : ℕ → ℝ) {d : ℕ} {p : Polynomial ℝ}
    (hdegree : p.natDegree ≤ d)
    (hp : PolynomialSquareCoeffNonnegative p)
    (hpne : p ≠ 0)
    (hs : ∀ k : ℕ, k ≤ 2 * d → 0 < s k) :
    0 < momentFunctional s (p ^ (2 : ℕ)) := by
  rw [momentFunctional_eq_support_sum]
  apply Finset.sum_pos'
  · intro k hk
    apply mul_nonneg (hp k)
    have hkdegree : k ≤ (p ^ (2 : ℕ)).natDegree :=
      Polynomial.le_natDegree_of_mem_supp k hk
    rw [Polynomial.natDegree_pow] at hkdegree
    exact (hs k (hkdegree.trans (Nat.mul_le_mul_left 2 hdegree))).le
  · have hp2ne : p ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hpne
    let k := (p ^ (2 : ℕ)).natDegree
    have hk : k ∈ (p ^ (2 : ℕ)).support :=
      Polynomial.natDegree_mem_support_of_nonzero hp2ne
    refine ⟨k, hk, mul_pos ?_ (hs k ?_)⟩
    · exact lt_of_le_of_ne (hp k)
        (Ne.symm (Polynomial.mem_support_iff.mp hk))
    · have hkdegree : k ≤ (p ^ (2 : ℕ)).natDegree := le_rfl
      rw [Polynomial.natDegree_pow] at hkdegree
      exact hkdegree.trans (Nat.mul_le_mul_left 2 hdegree)

/-- A strictly positive moment prefix is strictly positive on every nonzero
coefficientwise one-sign polynomial of bounded degree. -/
theorem momentFunctional_sq_pos_of_coeffwiseOneSign
    (s : ℕ → ℝ) {d : ℕ} {p : Polynomial ℝ}
    (hdegree : p.natDegree ≤ d)
    (hp : PolynomialCoeffwiseOneSign p)
    (hpne : p ≠ 0)
    (hs : ∀ k : ℕ, k ≤ 2 * d → 0 < s k) :
    0 < momentFunctional s (p ^ (2 : ℕ)) :=
  momentFunctional_sq_pos_of_squareCoeffNonnegative s hdegree
    (polynomialSquareCoeffNonnegative_of_coeffwiseOneSign hp) hpne hs

/-- A degree-seven square remains nonnegative when all square coefficients are nonnegative and
the penultimate coefficient dominates the endpoint coefficient, provided the first fourteen
moments are nonnegative and the penultimate moment dominates the endpoint moment in absolute
value. This isolates the final adjacent-pair compensation that ordinary coefficientwise
positivity cannot see. -/
theorem momentFunctional_sq_nonneg_of_degreeSeven_endpointPair
    (s : ℕ → ℝ) {p : Polynomial ℝ}
    (hdegree : p.natDegree ≤ 7)
    (hp : PolynomialSquareCoeffNonnegative p)
    (hpair : (p ^ (2 : ℕ)).coeff 14 ≤ (p ^ (2 : ℕ)).coeff 13)
    (hs : ∀ k : ℕ, k ≤ 13 → 0 ≤ s k)
    (hend : |s 14| ≤ s 13) :
    0 ≤ momentFunctional s (p ^ (2 : ℕ)) := by
  let f : ℕ → ℝ := fun k => (p ^ (2 : ℕ)).coeff k * s k
  have hsqdegree : (p ^ (2 : ℕ)).natDegree ≤ 14 := by
    rw [Polynomial.natDegree_pow]
    omega
  have hpad :
      ∑ k ∈ Finset.range ((p ^ (2 : ℕ)).natDegree + 1), f k =
        ∑ k ∈ Finset.range 15, f k := by
    rw [← Finset.sum_range_add_sum_Ico f
      (show (p ^ (2 : ℕ)).natDegree + 1 ≤ 15 by omega)]
    have hzero :
        ∑ k ∈ Finset.Ico ((p ^ (2 : ℕ)).natDegree + 1) 15, f k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : (p ^ (2 : ℕ)).natDegree < k :=
        (Finset.mem_Ico.mp hk).1
      rw [show f k = (p ^ (2 : ℕ)).coeff k * s k by rfl,
        Polynomial.coeff_eq_zero_of_natDegree_lt hklt, zero_mul]
    rw [hzero, add_zero]
  have hprefix : 0 ≤ ∑ k ∈ Finset.range 13, f k := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (hp k) (hs k (by
      have := Finset.mem_range.mp hk
      omega))
  have h13 : 0 ≤ (p ^ (2 : ℕ)).coeff 13 := hp 13
  have h14 : 0 ≤ (p ^ (2 : ℕ)).coeff 14 := hp 14
  have hs13 : 0 ≤ s 13 := hs 13 le_rfl
  have hlast :
      0 ≤ (p ^ (2 : ℕ)).coeff 13 * s 13 +
        (p ^ (2 : ℕ)).coeff 14 * s 14 := by
    have hs14lower : -|s 14| ≤ s 14 := neg_abs_le (s 14)
    have h14lower :
        -(p ^ (2 : ℕ)).coeff 14 * |s 14| ≤
          (p ^ (2 : ℕ)).coeff 14 * s 14 := by
      nlinarith [mul_le_mul_of_nonneg_left hs14lower h14]
    have hpairmass :
        (p ^ (2 : ℕ)).coeff 14 * |s 14| ≤
          (p ^ (2 : ℕ)).coeff 13 * s 13 := by
      calc
        (p ^ (2 : ℕ)).coeff 14 * |s 14| ≤
            (p ^ (2 : ℕ)).coeff 14 * s 13 :=
          mul_le_mul_of_nonneg_left hend h14
        _ ≤ (p ^ (2 : ℕ)).coeff 13 * s 13 :=
          mul_le_mul_of_nonneg_right hpair hs13
    nlinarith
  rw [momentFunctional]
  have hrange := (p ^ (2 : ℕ)).sum_over_range
    (f := fun k c => c * s k) (by simp)
  rw [hrange, hpad]
  rw [show 15 = 14 + 1 by omega, Finset.sum_range_succ,
    show 14 = 13 + 1 by omega, Finset.sum_range_succ]
  dsimp only [f] at hlast ⊢
  nlinarith

/-- A five-term mixed-sign polynomial whose square has nonnegative coefficients. -/
def mixedSignSquareCoeffPolynomial (a : ℝ) : Polynomial ℝ :=
  C a * X ^ (0 : ℕ) + C (2 * a) * X - C a * X ^ (2 : ℕ) +
    C (2 * a) * X ^ (3 : ℕ) + C a * X ^ (4 : ℕ)

/-- Exact self-convolution identity for the mixed-sign five-term family. -/
theorem mixedSignSquareCoeffPolynomial_sq (a : ℝ) :
    mixedSignSquareCoeffPolynomial a ^ (2 : ℕ) =
      C (a ^ (2 : ℕ)) * X ^ (0 : ℕ) +
        C (4 * a ^ (2 : ℕ)) * X ^ (1 : ℕ) +
        C (2 * a ^ (2 : ℕ)) * X ^ (2 : ℕ) +
        C (11 * a ^ (2 : ℕ)) * X ^ (4 : ℕ) +
        C (2 * a ^ (2 : ℕ)) * X ^ (6 : ℕ) +
        C (4 * a ^ (2 : ℕ)) * X ^ (7 : ℕ) +
        C (a ^ (2 : ℕ)) * X ^ (8 : ℕ) := by
  simp only [mixedSignSquareCoeffPolynomial, map_mul, map_pow, map_ofNat]
  ring

/-- The mixed-sign five-term family lies in the square-coefficient cone. -/
theorem polynomialSquareCoeffNonnegative_mixedSign (a : ℝ) :
    PolynomialSquareCoeffNonnegative (mixedSignSquareCoeffPolynomial a) := by
  intro k
  rw [mixedSignSquareCoeffPolynomial_sq]
  simp only [coeff_add, coeff_C_mul_X_pow]
  by_cases hk : k ≤ 8
  · interval_cases k <;> norm_num <;> positivity
  · split_ifs <;> norm_num <;> omega

/-- For positive scale, the five-term family is not coefficientwise one-sign. -/
theorem not_polynomialCoeffwiseOneSign_mixedSign {a : ℝ} (ha : 0 < a) :
    ¬ PolynomialCoeffwiseOneSign (mixedSignSquareCoeffPolynomial a) := by
  rintro (hpos | hneg)
  · have h := hpos 2
    simp only [mixedSignSquareCoeffPolynomial, coeff_add, coeff_sub,
      coeff_C_mul_X_pow] at h
    norm_num at h
    linarith
  · have h := hneg 0
    simp only [mixedSignSquareCoeffPolynomial, coeff_add, coeff_sub,
      coeff_C_mul_X_pow] at h
    norm_num at h
    linarith

end

end HTGeometry
