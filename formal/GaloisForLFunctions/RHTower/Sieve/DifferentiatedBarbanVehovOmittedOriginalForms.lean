import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedPolynomialMain
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovHigherSelbergForms

/-!
# Original Selberg forms for the omitted-head boundary

The pointwise Barban--Vehov/lcm conversion rewrites each omitted boundary polynomial using the
literal Möbius/gcd Selberg coefficient.  These identities expose the sole remaining coupled
`log(M/max(m,n))` asymptotic without recreating any existing ordinary Selberg form.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- On positive natural divisors, the logarithmic maximum endpoint is the minimum of the two
complementary logarithms. -/
theorem log_nat_div_max_eq_min
    {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r) :
    Real.log ((M : ℝ) / ((max q r : ℕ) : ℝ)) =
      min (Real.log ((M : ℝ) / (q : ℝ)))
        (Real.log ((M : ℝ) / (r : ℝ))) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rcases le_total q r with hqr | hrq
  · rw [max_eq_right hqr]
    have hlog : Real.log (q : ℝ) ≤ Real.log (r : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hqr
    rw [Real.log_div hMR hqR, Real.log_div hMR hrR, min_eq_right]
    linarith
  · rw [max_eq_left hrq]
    have hlog : Real.log (r : ℝ) ≤ Real.log (q : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hrq
    rw [Real.log_div hMR hqR, Real.log_div hMR hrR, min_eq_left]
    linarith

/-- Original Selberg-coefficient form of the omitted base boundary. -/
def selbergOriginalOmittedBaseBoundary (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    selbergOriginalCoeff p.1 p.2 * (A * B * u)

/-- Original Selberg-coefficient form of the omitted base/derivative boundary. -/
def selbergOriginalOmittedCrossBoundary (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    (-1 : ℝ) * selbergOriginalCoeff p.1 p.2 * (A * B) *
      (u * (ell + B) - u ^ 2 / 2)

/-- Original Selberg-coefficient form of the omitted derivative-square boundary. -/
def selbergOriginalOmittedDerivativeBoundary (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ))
    selbergOriginalCoeff p.1 p.2 * (A * B) *
      (u * (ell + A) * (ell + B) -
        u ^ 2 / 2 * (2 * ell + A + B) + u ^ 3 / 3)

theorem barbanVehovOmittedLongBasePolynomialMain_eq_originalBoundary (M : ℕ) :
    barbanVehovOmittedLongBasePolynomialMain M =
      selbergOriginalOmittedBaseBoundary M := by
  rw [barbanVehovOmittedLongBasePolynomialMain,
    selbergOriginalOmittedBaseBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
    (Finset.mem_Icc.mp hp1).2 (Finset.mem_Icc.mp hp2).2
  dsimp only
  rw [hfactor]
  ring

theorem barbanVehovOmittedLongCrossPolynomialMain_eq_originalBoundary
    (ell : ℝ) (M : ℕ) :
    barbanVehovOmittedLongCrossPolynomialMain ell M =
      selbergOriginalOmittedCrossBoundary ell M := by
  rw [barbanVehovOmittedLongCrossPolynomialMain,
    selbergOriginalOmittedCrossBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
    (Finset.mem_Icc.mp hp1).2 (Finset.mem_Icc.mp hp2).2
  dsimp only
  rw [hfactor]
  ring

theorem barbanVehovOmittedLongDerivativePolynomialMain_eq_originalBoundary
    (ell : ℝ) (M : ℕ) :
    barbanVehovOmittedLongDerivativePolynomialMain ell M =
      selbergOriginalOmittedDerivativeBoundary ell M := by
  rw [barbanVehovOmittedLongDerivativePolynomialMain,
    selbergOriginalOmittedDerivativeBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
    (Finset.mem_Icc.mp hp1).2 (Finset.mem_Icc.mp hp2).2
  dsimp only
  rw [hfactor]

/-- Generic finite-sum bridge from the maximum divisor endpoint to the minimum of complementary
logarithms.  This isolates the shared combinatorial rewrite used by all omitted-head forms. -/
theorem sum_log_nat_div_max_eq_min
    (M : ℕ) (hM : 0 < M) (F : ℕ × ℕ → ℝ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      F p (Real.log ((M : ℝ) / ((max p.1 p.2 : ℕ) : ℝ)))) =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        F p (min (Real.log ((M : ℝ) / (p.1 : ℝ)))
          (Real.log ((M : ℝ) / (p.2 : ℝ)))) := by
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [log_nat_div_max_eq_min hM
    (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1]

/-- Min-normal form of the omitted base boundary. -/
theorem selbergOriginalOmittedBaseBoundary_eq_min
    (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedBaseBoundary M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        selbergOriginalCoeff p.1 p.2 * (A * B * min A B) := by
  rw [selbergOriginalOmittedBaseBoundary]
  exact sum_log_nat_div_max_eq_min M hM
    (fun p u =>
      let A := Real.log ((M : ℝ) / (p.1 : ℝ))
      let B := Real.log ((M : ℝ) / (p.2 : ℝ))
      selbergOriginalCoeff p.1 p.2 * (A * B * u))

/-- Min-normal form of the omitted base/derivative boundary. -/
theorem selbergOriginalOmittedCrossBoundary_eq_min
    (ell : ℝ) (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedCrossBoundary ell M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        let u := min A B
        (-1 : ℝ) * selbergOriginalCoeff p.1 p.2 * (A * B) *
          (u * (ell + B) - u ^ 2 / 2) := by
  rw [selbergOriginalOmittedCrossBoundary]
  exact sum_log_nat_div_max_eq_min M hM
    (fun p u =>
      let A := Real.log ((M : ℝ) / (p.1 : ℝ))
      let B := Real.log ((M : ℝ) / (p.2 : ℝ))
      (-1 : ℝ) * selbergOriginalCoeff p.1 p.2 * (A * B) *
        (u * (ell + B) - u ^ 2 / 2))

/-- Min-normal form of the omitted derivative-square boundary. -/
theorem selbergOriginalOmittedDerivativeBoundary_eq_min
    (ell : ℝ) (M : ℕ) (hM : 0 < M) :
    selbergOriginalOmittedDerivativeBoundary ell M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        let u := min A B
        selbergOriginalCoeff p.1 p.2 * (A * B) *
          (u * (ell + A) * (ell + B) -
            u ^ 2 / 2 * (2 * ell + A + B) + u ^ 3 / 3) := by
  rw [selbergOriginalOmittedDerivativeBoundary]
  exact sum_log_nat_div_max_eq_min M hM
    (fun p u =>
      let A := Real.log ((M : ℝ) / (p.1 : ℝ))
      let B := Real.log ((M : ℝ) / (p.2 : ℝ))
      selbergOriginalCoeff p.1 p.2 * (A * B) *
        (u * (ell + A) * (ell + B) -
          u ^ 2 / 2 * (2 * ell + A + B) + u ^ 3 / 3))

end

end RHTower.Sieve
