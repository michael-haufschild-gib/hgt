import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bernoulli character products and spectral decay

A Bernoulli factor at a group element has Fourier multiplier `(1 + χ(g))/2`.
Its squared modulus is `(1 + Re χ(g))/2`; each character value with real part
at most one half therefore contracts squared mass by at least three quarters.
Squaring the character gives the exact quadratic transformation of these local weights.
-/

open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

noncomputable section

/-- Fourier multiplier of an equal mixture of the identity and one group element. -/
def bernoulliMultiplier (z : Circle) : ℂ := (1 + (z : ℂ)) / 2

/-- The local squared multiplier is affine in the real part of the character value. -/
theorem bernoulliMultiplier_normSq (z : Circle) :
    Complex.normSq (bernoulliMultiplier z) = (1 + (z : ℂ).re) / 2 := by
  rw [bernoulliMultiplier, Complex.normSq_div, Complex.normSq_add]
  simp only [Complex.normSq_one, Circle.normSq_coe, Complex.normSq_ofNat,
    one_mul, Complex.conj_re]
  ring

/-- Every local Bernoulli multiplier has squared modulus at most one. -/
theorem bernoulliMultiplier_normSq_le_one (z : Circle) :
    Complex.normSq (bernoulliMultiplier z) ≤ 1 := by
  rw [bernoulliMultiplier_normSq]
  have hre := Complex.re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at hre
  linarith only [hre]

/-- Character squaring acts quadratically on the local squared multiplier. -/
theorem bernoulliMultiplier_square (z : Circle) :
    Complex.normSq (bernoulliMultiplier (z ^ 2)) =
      (2 * Complex.normSq (bernoulliMultiplier z) - 1) ^ 2 := by
  rw [bernoulliMultiplier_normSq, bernoulliMultiplier_normSq, Circle.coe_pow, pow_two,
    Complex.mul_re]
  have hunit := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hunit
  nlinarith only [hunit]

variable {G ι : Type*} [CommGroup G]

/-- Fourier multiplier of the convolution of indexed Bernoulli factors. -/
def bernoulliCharacterProduct (χ : G →* Circle) (q : ι → G) (I : Finset ι) : ℂ :=
  ∏ i ∈ I, bernoulliMultiplier (χ (q i))

/-- A character mode vanishes exactly when one Bernoulli factor is antipodal. -/
theorem bernoulliCharacterProduct_eq_zero_iff (χ : G →* Circle) (q : ι → G)
    (I : Finset ι) :
    bernoulliCharacterProduct χ q I = 0 ↔
      ∃ i ∈ I, ((χ (q i) : Circle) : ℂ) = -1 := by
  simp only [bernoulliCharacterProduct, prod_eq_zero_iff, bernoulliMultiplier,
    div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, add_comm (1 : ℂ),
    add_eq_zero_iff_eq_neg]

/-- Each character value outside the open half-plane contributes a factor of three quarters. -/
theorem bernoulliCharacterProduct_decay (χ : G →* Circle) (q : ι → G) (I : Finset ι) :
    Complex.normSq (bernoulliCharacterProduct χ q I) ≤
      (3 / 4 : ℝ) ^ (I.filter fun i => ((χ (q i) : Circle) : ℂ).re ≤ 1 / 2).card := by
  rw [bernoulliCharacterProduct, map_prod]
  calc
    _ ≤ ∏ i ∈ I, if ((χ (q i) : Circle) : ℂ).re ≤ 1 / 2 then (3 / 4 : ℝ) else 1 := by
      apply prod_le_prod (fun i _ => Complex.normSq_nonneg _)
      intro i _
      split_ifs with h
      · rw [bernoulliMultiplier_normSq]
        linarith only [h]
      · exact bernoulliMultiplier_normSq_le_one _
    _ = _ := by rw [prod_ite, prod_const, prod_const]; simp only [one_pow, mul_one]

/-- Symmetrizing the Bernoulli convolution squares its spectral decay. -/
theorem bernoulliCharacterProduct_fourth_decay (χ : G →* Circle) (q : ι → G) (I : Finset ι) :
    Complex.normSq (bernoulliCharacterProduct χ q I) ^ 2 ≤
      (9 / 16 : ℝ) ^ (I.filter fun i => ((χ (q i) : Circle) : ℂ).re ≤ 1 / 2).card := by
  have h := pow_le_pow_left₀ (Complex.normSq_nonneg _)
    (bernoulliCharacterProduct_decay χ q I) 2
  calc
    _ ≤ ((3 / 4 : ℝ) ^ (I.filter fun i => ((χ (q i) : Circle) : ℂ).re ≤ 1 / 2).card) ^ 2 := h
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

/-- The squared character multiplier is an exact product of quadratic local transforms. -/
theorem bernoulliCharacterProduct_square (χ : G →* Circle) (q : ι → G) (I : Finset ι) :
    Complex.normSq (bernoulliCharacterProduct (χ ^ 2) q I) =
      ∏ i ∈ I, (2 * Complex.normSq (bernoulliMultiplier (χ (q i))) - 1) ^ 2 := by
  rw [bernoulliCharacterProduct, map_prod]
  apply prod_congr rfl
  intro i _
  exact bernoulliMultiplier_square (χ (q i))

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.bernoulliCharacterProduct_decay
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.bernoulliCharacterProduct_fourth_decay
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.bernoulliCharacterProduct_square
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.bernoulliCharacterProduct_eq_zero_iff
