import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators

/-!
# The hyperbolic cost of a reflected zero pair

The two zero equations at equal height give an exact hyperbolic moment.
Its endpoint-normalized test yields the central positive-mass cost of the pair.
Positive trinomials with two opposite endpoint phases attain this cost.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem sinh_test_identity (δ c L : ℝ) :
    Real.sinh (δ * (c - L)) =
      (Real.exp (δ * c) * Real.exp (-δ * L) -
        Real.exp (-δ * c) * Real.exp (δ * L)) / 2 := by
  rw [← Real.exp_add, ← Real.exp_add, Real.sinh_eq]
  congr 2 <;> congr 1 <;> ring

private theorem shifted_frequency_sum {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (ρ : ℂ) (t : ℝ) :
    (∑ d ∈ P.support.erase 0, (Real.exp (-t * monomialLog d) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
        dirichletEval (ρ + (t : ℂ)) P - 1 := by
  rw [dirichletEval_eq_one_add_tail hP, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.ofReal_exp]
  calc
    _ = (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
        (Complex.exp ((-t * monomialLog d : ℝ) : ℂ) *
          Complex.exp (-(monomialLog d : ℂ) * ρ)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The two reflected zeros prescribe a nonzero hyperbolic frequency moment. -/
theorem reflected_pair_hyperbolic_moment {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ}
    (hplus : dirichletEval (ρ + (δ : ℂ)) P = 0)
    (hminus : dirichletEval (ρ - (δ : ℂ)) P = 0) (c : ℝ) :
    (∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
        -(Real.sinh (δ * c) : ℂ) := by
  have hp := shifted_frequency_sum hP ρ δ
  have hm := shifted_frequency_sum hP ρ (-δ)
  rw [hplus, zero_sub] at hp
  simp only [neg_neg, Complex.ofReal_neg, ← sub_eq_add_neg, hminus, zero_sub] at hm
  have he : (∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
      ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) =
      ((Real.exp (δ * c) : ℂ) * (∑ d ∈ P.support.erase 0,
        (Real.exp (-δ * monomialLog d) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))) -
       (Real.exp (-δ * c) : ℂ) * (∑ d ∈ P.support.erase 0,
        (Real.exp (δ * monomialLog d) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)))) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [sinh_test_identity]
    push_cast
    ring
  rw [he, hp, hm, Real.sinh_eq]
  push_cast
  congr 2 <;> ring

/-- Equal-height reflected zeros force the sharp central-mass bound associated
with the available logarithmic frequency interval. -/
theorem reflected_pair_forces_hyperbolic_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hplus : dirichletEval (ρ + (δ : ℂ)) P = 0)
    (hminus : dirichletEval (ρ - (δ : ℂ)) P = 0)
    {a B : ℝ} (ha : 0 < a) (hB : a < B)
    (hfreq : ∀ d ∈ P.support.erase 0, a ≤ monomialLog d ∧ monomialLog d ≤ B) :
    Real.sinh (δ * ((B + a) / 2)) / Real.sinh (δ * ((B - a) / 2)) ≤
      dirichletTailMass P ρ.re := by
  let c := (B + a) / 2
  let h := (B - a) / 2
  have hh : 0 < h := by dsimp only [h]; positivity
  have hc : 0 < c := by dsimp only [c]; linarith only [ha, hB]
  have hden : 0 < Real.sinh (δ * h) := Real.sinh_pos_iff.mpr (mul_pos hδ hh)
  have hmoment := reflected_pair_hyperbolic_moment hP hplus hminus c
  have htest (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      |Real.sinh (δ * (c - monomialLog d))| ≤ Real.sinh (δ * h) := by
    rw [Real.abs_sinh]
    apply Real.sinh_le_sinh.mpr
    rw [abs_mul, abs_of_pos hδ]
    apply mul_le_mul_of_nonneg_left _ hδ.le
    apply abs_le.mpr
    dsimp only [c, h]
    constructor <;> linarith only [(hfreq d hd).1, (hfreq d hd).2]
  have hcost : Real.sinh (δ * c) ≤ Real.sinh (δ * h) * dirichletTailMass P ρ.re := by
    calc
      _ = ‖∑ d ∈ P.support.erase 0, (Real.sinh (δ * (c - monomialLog d)) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))‖ := by
        rw [hmoment, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.sinh_pos_iff.mpr (mul_pos hδ hc))]
      _ ≤ ∑ d ∈ P.support.erase 0, ‖(Real.sinh (δ * (c - monomialLog d)) : ℂ) *
          ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ P.support.erase 0, Real.sinh (δ * h) *
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp, Complex.mul_re,
          Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
          neg_zero, zero_mul, sub_zero]
        exact mul_le_mul_of_nonneg_right (htest d hd)
          (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
      _ = _ := by rw [dirichletTailMass, Finset.mul_sum]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcost)

#print axioms reflected_pair_hyperbolic_moment
#print axioms reflected_pair_forces_hyperbolic_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
