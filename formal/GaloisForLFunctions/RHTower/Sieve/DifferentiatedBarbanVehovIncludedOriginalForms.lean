import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedContinuous
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovHigherSelbergForms

/-!
# Original Selberg forms for the included detector-head boundary

The included endpoint `log(min(q,r))` equals `log M - A - B + min(A,B)` in complementary
coordinates `A = log(M/q)` and `B = log(M/r)`.  Combining this identity with the existing
Barban--Vehov/lcm conversion exposes the literal original Selberg coefficient without duplicating
the ordinary or minimum-logarithmic Selberg infrastructure.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- The included minimum divisor endpoint in complementary logarithmic coordinates. -/
theorem log_nat_min_eq_log_sub_complementary_add_min
    {M q r : ℕ} (hM : 0 < M) (hq : 0 < q) (hr : 0 < r) :
    Real.log ((min q r : ℕ) : ℝ) =
      Real.log M - Real.log ((M : ℝ) / (q : ℝ)) -
        Real.log ((M : ℝ) / (r : ℝ)) +
          min (Real.log ((M : ℝ) / (q : ℝ)))
            (Real.log ((M : ℝ) / (r : ℝ))) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rcases le_total q r with hqr | hrq
  · rw [min_eq_left hqr]
    have hlog : Real.log (q : ℝ) ≤ Real.log (r : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hqr
    rw [Real.log_div hMR hqR, Real.log_div hMR hrR, min_eq_right]
    · ring
    · linarith
  · rw [min_eq_right hrq]
    have hlog : Real.log (r : ℝ) ≤ Real.log (q : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hrq
    rw [Real.log_div hMR hqR, Real.log_div hMR hrR, min_eq_left]
    · ring
    · linarith

/-- Original Selberg-coefficient form of the included base boundary. -/
def selbergOriginalIncludedBaseBoundary (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := min A B
    selbergOriginalCoeff p.1 p.2 *
      (A * B * (Real.log M - A - B + u))

/-- Original Selberg-coefficient form of the included base/derivative boundary. -/
def selbergOriginalIncludedCrossBoundary (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := min A B
    let v := Real.log M - A - B + u
    (-1 : ℝ) * selbergOriginalCoeff p.1 p.2 * (A * B) *
      (v * (ell - Real.log M + B) + v ^ (2 : ℕ) / 2)

/-- Original Selberg-coefficient form of the included derivative-square boundary. -/
def selbergOriginalIncludedDerivativeBoundary (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    let A := Real.log ((M : ℝ) / (p.1 : ℝ))
    let B := Real.log ((M : ℝ) / (p.2 : ℝ))
    let u := min A B
    let v := Real.log M - A - B + u
    selbergOriginalCoeff p.1 p.2 * (A * B) *
      (v * (ell - Real.log M + A) * (ell - Real.log M + B) +
        v ^ (2 : ℕ) / 2 * (2 * (ell - Real.log M) + A + B) + v ^ (3 : ℕ) / 3)

theorem barbanVehovIncludedLongBasePolynomialMain_eq_originalBoundary
    {M : ℕ} (hM : 0 < M) :
    barbanVehovIncludedLongBasePolynomialMain M =
      selbergOriginalIncludedBaseBoundary M := by
  rw [barbanVehovIncludedLongBasePolynomialMain,
    selbergOriginalIncludedBaseBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    hp1.1 hp2.1 hp1.2 hp2.2
  have hendpoint := log_nat_min_eq_log_sub_complementary_add_min
    hM hp1.1 hp2.1
  dsimp only
  rw [hfactor, hendpoint]
  ring

theorem barbanVehovIncludedLongCrossPolynomialMain_eq_originalBoundary
    (ell : ℝ) {M : ℕ} (hM : 0 < M) :
    barbanVehovIncludedLongCrossPolynomialMain ell M =
      selbergOriginalIncludedCrossBoundary ell M := by
  rw [barbanVehovIncludedLongCrossPolynomialMain,
    selbergOriginalIncludedCrossBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    hp1.1 hp2.1 hp1.2 hp2.2
  have hendpoint := log_nat_min_eq_log_sub_complementary_add_min
    hM hp1.1 hp2.1
  dsimp only
  rw [hfactor, hendpoint, log_nat_div hM hp2.1]
  ring

theorem barbanVehovIncludedLongDerivativePolynomialMain_eq_originalBoundary
    (ell : ℝ) {M : ℕ} (hM : 0 < M) :
    barbanVehovIncludedLongDerivativePolynomialMain ell M =
      selbergOriginalIncludedDerivativeBoundary ell M := by
  rw [barbanVehovIncludedLongDerivativePolynomialMain,
    selbergOriginalIncludedDerivativeBoundary]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hfactor := barbanVehovWeight_mul_div_lcm_eq_originalCoeff
    hp1.1 hp2.1 hp1.2 hp2.2
  have hendpoint := log_nat_min_eq_log_sub_complementary_add_min
    hM hp1.1 hp2.1
  dsimp only
  rw [hfactor, hendpoint, log_nat_div hM hp1.1, log_nat_div hM hp2.1]
  ring

end

end RHTower.Sieve
