import GaloisForLFunctions.Core

/-!
# Finite prime--archimedean dual-Cauchy tensor sections

For finite positive alphabets `x_p` and `y_j`, the fermionic pair-product section

`product_(p,j) (1 + u x_p y_j)`

has only negative real zeros.  Its logarithmic power sums factor exactly into the prime and
archimedean power sums.  This is the finite algebraic core of the proposed dual-RSK/Fredholm RH
detour; no claim about the cofinal Xi comparison is made here.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The finite fermionic partition section on a prime alphabet and an archimedean alphabet. -/
def finitePrimeArchFermionSection {ι κ : Type*}
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ) (u : ℂ) : ℂ :=
  ∏ p ∈ P, ∏ j ∈ A, (1 + u * ((x p * y j : ℝ) : ℂ))

/-- The finite power sum of the pair-product alphabet. -/
def finitePrimeArchPairPowerSum {ι κ : Type*}
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, ∑ j ∈ A, (x p * y j) ^ n

/-- Pair-product power sums factor into the prime and archimedean power sums. -/
theorem finitePrimeArchPairPowerSum_eq_mul
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ) (n : ℕ) :
    finitePrimeArchPairPowerSum P A x y n =
      (∑ p ∈ P, x p ^ n) * (∑ j ∈ A, y j ^ n) := by
  classical
  rw [finitePrimeArchPairPowerSum]
  symm
  calc
    (∑ p ∈ P, x p ^ n) * (∑ j ∈ A, y j ^ n) =
        ∑ p ∈ P, x p ^ n * (∑ j ∈ A, y j ^ n) := by
          rw [Finset.sum_mul]
    _ = ∑ p ∈ P, ∑ j ∈ A, x p ^ n * y j ^ n := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ p ∈ P, ∑ j ∈ A, (x p * y j) ^ n := by
      simp only [mul_pow]

/-- Every zero of a finite positive two-alphabet fermionic section is a negative real number. -/
theorem finitePrimeArchFermionSection_zero_is_negativeReal
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : Finset ι) (A : Finset κ) (x : ι → ℝ) (y : κ → ℝ)
    (hx : ∀ p ∈ P, 0 < x p) (hy : ∀ j ∈ A, 0 < y j)
    {u : ℂ} (hu : finitePrimeArchFermionSection P A x y u = 0) :
    ∃ r : ℝ, r < 0 ∧ u = (r : ℂ) := by
  classical
  simp only [finitePrimeArchFermionSection, Finset.prod_eq_zero_iff] at hu
  obtain ⟨p, hp, j, hj, hzero⟩ := hu
  have hxy : 0 < x p * y j := mul_pos (hx p hp) (hy j hj)
  refine ⟨-(x p * y j)⁻¹, neg_lt_zero.mpr (inv_pos.mpr hxy), ?_⟩
  have hne : (((x p * y j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hxy.ne'
  apply (mul_right_cancel₀ hne)
  calc
    u * ((x p * y j : ℝ) : ℂ) = -1 := by linear_combination hzero
    _ = ((-(x p * y j)⁻¹ : ℝ) : ℂ) * ((x p * y j : ℝ) : ℂ) := by
      exact_mod_cast (show (-1 : ℝ) = (-(x p * y j)⁻¹) * (x p * y j) by
        rw [neg_mul, inv_mul_cancel₀ hxy.ne'])

end RHTower
