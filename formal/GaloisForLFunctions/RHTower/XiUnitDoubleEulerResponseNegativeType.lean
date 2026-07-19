import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# Negative type of the finite unit--double Euler response

Before archimedean completion at the real-part-one boundary, the completed unit--double response
has Dirichlet spectral coefficient

`Λ(n) (2 / n² - 1 / n) = Λ(n) (2-n) / n²`.

Every coefficient for `n ≥ 2` is nonpositive, and on prime-power support only the literal mode
`n = 2` vanishes.  Consequently each finite Euler truncation is a negative-type translation
kernel: its quadratic form is a nonpositive sum of squared twisted cosine/sine amplitudes.

This moves all unresolved signed Jordan behavior into the archimedean/boundary completion.  No
limit at real part one, AC25 identification, or RH estimate is asserted here.
-/

open scoped BigOperators
open ArithmeticFunction

namespace RHTower

noncomputable section

/-- Dirichlet spectral coefficient of the unit--double Euler response. -/
def xiUnitDoubleEulerResponseSpectralCoefficient (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (2 / (n : ℝ) ^ 2 - 1 / (n : ℝ))

theorem xiUnitDoubleEulerResponseSpectralCoefficient_eq
    {n : ℕ} (hn : 2 ≤ n) :
    xiUnitDoubleEulerResponseSpectralCoefficient n =
      ArithmeticFunction.vonMangoldt n *
        (2 - (n : ℝ)) / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [xiUnitDoubleEulerResponseSpectralCoefficient]
  field_simp [hn0]
  ring

/-- Every genuine Euler mode is nonpositive under the unit--double response. -/
theorem xiUnitDoubleEulerResponseSpectralCoefficient_nonpos
    {n : ℕ} (hn : 2 ≤ n) :
    xiUnitDoubleEulerResponseSpectralCoefficient n ≤ 0 := by
  rw [xiUnitDoubleEulerResponseSpectralCoefficient_eq hn]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 2 - (n : ℝ) ≤ 0 := sub_nonpos.mpr hnR
  have hden : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  exact mul_nonpos_of_nonneg_of_nonpos
    ArithmeticFunction.vonMangoldt_nonneg
    (div_nonpos_of_nonpos_of_nonneg hnum hden)

/-- Exact null-channel classification: on positive prime-power support only `n=2` is killed. -/
theorem xiUnitDoubleEulerResponseSpectralCoefficient_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) :
    xiUnitDoubleEulerResponseSpectralCoefficient n = 0 ↔
      n = 2 ∨ ¬IsPrimePow n := by
  rw [xiUnitDoubleEulerResponseSpectralCoefficient_eq hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [div_eq_zero_iff, mul_eq_zero,
    ArithmeticFunction.vonMangoldt_eq_zero_iff]
  constructor
  · rintro (hnot | htwo)
    · exact Or.inr hnot
    · left
      have hcast : (n : ℝ) = 2 := by linarith
      exact_mod_cast hcast
  · rintro (rfl | hnot)
    · simp
    · exact Or.inl hnot
  · exact pow_ne_zero 2 hn0

private theorem finite_cosine_translation_quadratic_eq_sq
    {ι : Type*} (I : Finset ι) (weight node : ι → ℝ) (t : ℝ) :
    (∑ i ∈ I, ∑ j ∈ I,
      weight i * weight j * Real.cos (t * (node i - node j))) =
      (∑ i ∈ I, weight i * Real.cos (t * node i)) ^ 2 +
        (∑ i ∈ I, weight i * Real.sin (t * node i)) ^ 2 := by
  rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show t * (node i - node j) = t * node i - t * node j by ring,
    Real.cos_sub]
  ring

/-- Quadratic form of one finite unit--double Euler truncation on arbitrary real nodes. -/
def xiUnitDoubleFiniteEulerResponseQuadratic
    {ι : Type*} (N : Finset ℕ) (I : Finset ι)
    (weight node : ι → ℝ) : ℝ :=
  ∑ n ∈ N, xiUnitDoubleEulerResponseSpectralCoefficient n *
    (∑ i ∈ I, ∑ j ∈ I,
      weight i * weight j *
        Real.cos (Real.log n * (node i - node j)))

/-- Exact negative-square spectral factorization of the finite Euler response. -/
theorem xiUnitDoubleFiniteEulerResponseQuadratic_eq_sq
    {ι : Type*} (N : Finset ℕ) (I : Finset ι)
    (weight node : ι → ℝ) :
    xiUnitDoubleFiniteEulerResponseQuadratic N I weight node =
      ∑ n ∈ N, xiUnitDoubleEulerResponseSpectralCoefficient n *
        ((∑ i ∈ I, weight i * Real.cos (Real.log n * node i)) ^ 2 +
          (∑ i ∈ I, weight i * Real.sin (Real.log n * node i)) ^ 2) := by
  rw [xiUnitDoubleFiniteEulerResponseQuadratic]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finite_cosine_translation_quadratic_eq_sq]

/-- Every finite Euler truncation supported on `n ≥ 2` is negative semidefinite. -/
theorem xiUnitDoubleFiniteEulerResponseQuadratic_nonpos
    {ι : Type*} (N : Finset ℕ) (I : Finset ι)
    (hN : ∀ n ∈ N, 2 ≤ n) (weight node : ι → ℝ) :
    xiUnitDoubleFiniteEulerResponseQuadratic N I weight node ≤ 0 := by
  rw [xiUnitDoubleFiniteEulerResponseQuadratic_eq_sq]
  exact Finset.sum_nonpos fun n hn =>
    mul_nonpos_of_nonpos_of_nonneg
      (xiUnitDoubleEulerResponseSpectralCoefficient_nonpos (hN n hn))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

end

end RHTower

