import Mathlib.Analysis.Fourier.ZMod

/-!
# Cubic frequencies in finite Gauss sums

Pulling a Gauss sum back along the cube map replaces its multiplicative character
by the inverse cube. At zero frequency the trivial character contributes the
number of units. Keeping that correction gives an identity for every character.

The inverse Fourier transform of the conjugated pullback is therefore a product
of two Gauss sums, plus an explicit constant correction. This is the finite
Fourier mechanism behind quartic reflection.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {F : Type*} [Field F] [Fintype F]

/-- Scaling a Gauss sum, including the exceptional trivial-character frequency. -/
theorem gaussSum_mulShift_with_zero_term (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (r : F) :
    gaussSum χ (ψ.mulShift r) = χ⁻¹ r * gaussSum χ ψ +
      if r = 0 ∧ χ = 1 then (Nat.card Fˣ : ℂ) else 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    have hshift : ψ.mulShift (0 : F) = 1 := by ext x; simp
    rw [hshift, MulChar.map_zero, zero_mul, zero_add]
    by_cases hχ : χ = 1
    · simp only [hχ, gaussSum_one_one, and_self, ite_true]
    · simp only [hχ, and_false, ite_false, gaussSum_one_right hχ]
  · rw [if_neg (fun h => hr h.1), add_zero]
    exact gaussSum_mulShift_eq χ ψ (Units.mk0 r hr)

/-- Cubic frequency pullback has the inverse-cube character away from its explicit
zero-frequency correction. -/
theorem gaussSum_cube_with_zero_term (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (r : F) :
    gaussSum χ (ψ.mulShift (r ^ 3)) = (χ⁻¹ r) ^ 3 * gaussSum χ ψ +
      if r = 0 ∧ χ = 1 then (Nat.card Fˣ : ℂ) else 0 := by
  rw [gaussSum_mulShift_with_zero_term, map_pow]
  simp only [pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)]

/-- Inverse Fourier transform of a conjugated Gauss sum sampled at cubic frequencies. -/
def reflectedCubicGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (u : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ r : F, star (gaussSum χ (ψ.mulShift (r ^ 3))) * ψ (-(r * u))

/-- Exact reflection for every character; the trivial character has a constant
correction, rather than a missing zero mode. -/
theorem reflectedCubicGauss_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (u : F) :
    reflectedCubicGauss χ ψ u = (Fintype.card F : ℂ)⁻¹ *
      (star (gaussSum χ ψ) * gaussSum (χ ^ 3) (ψ.mulShift (-u)) +
        if χ = 1 then (Nat.card Fˣ : ℂ) else 0) := by
  classical
  unfold reflectedCubicGauss
  congr 1
  simp_rw [gaussSum_cube_with_zero_term, star_add, star_mul, star_pow,
    MulChar.star_apply', inv_inv, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · conv_rhs => arg 2; rw [gaussSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [MulChar.pow_apply' _ (by norm_num), AddChar.mulShift_apply]
    rw [show -u * r = -(r * u) by ring]
    ring
  · by_cases hχ : χ = 1
    · simp [apply_ite, hχ]
    · simp [hχ]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
