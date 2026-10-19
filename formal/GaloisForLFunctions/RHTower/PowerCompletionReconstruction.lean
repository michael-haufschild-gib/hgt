import GaloisForLFunctions.HTGeometry.ArithmeticPowerDilation
import GaloisForLFunctions.RHTower.Sieve.HeathBrownIdentity
import GaloisForLFunctions.RHTower.ChenGuptaLiTailCoefficientBounds

/-!
# Power completion, sieve defects, and zero-detection tails

Lemma 5.3 of *The Quasi-Riemann Hypothesis* regroups the long part of a cube
inverse into a truncated Möbius divisor sum.  That coefficient is already
present in the finite zero detector, with the opposite sign after subtracting
the unit coefficient.  Here the identification is exact at every index.

The same algebra gives a finite geometric reconstruction for arbitrary
coefficients and completely multiplicative weights.  Its remainder after `k`
steps has no coefficient below `(L + 1) ^ (k * (m + 1))` for dilation exponent
`m + 1`; taking `m = 2` gives the cube case.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta Moebius

/-- Long and short divisor sums are complementary pieces of the Möbius inverse. -/
theorem sum_long_moebius_divisors_eq (X n : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => X + 1 < d), (moebius d : ℤ)) =
      (if n = 1 then 1 else 0) - zeroDetectionMobiusCoefficient X n := by
  have h := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun d => d ≤ X + 1) (fun d => (moebius d : ℤ))
  simp only [not_le] at h
  rw [sum_moebius_divisors] at h
  unfold zeroDetectionMobiusCoefficient
  omega

/-- The sieve truncation defect is the same long divisor coefficient. -/
theorem moebiusZetaDefect_eq_long_divisors (X n : ℕ) :
    Sieve.moebiusZetaDefect (X + 1) n =
      ((∑ d ∈ n.divisors.filter (fun d => X + 1 < d), (moebius d : ℤ)) : ℝ) := by
  rw [← Int.cast_sum, sum_long_moebius_divisors_eq]
  change (1 : ArithmeticFunction ℝ) n -
    (Sieve.truncatedMoebius (X + 1) * (ζ : ArithmeticFunction ℝ)) n = _
  simp only [ArithmeticFunction.one_apply, ArithmeticFunction.coe_mul_zeta_apply,
    Sieve.truncatedMoebius_apply, zeroDetectionMobiusCoefficient, Finset.sum_filter]
  push_cast
  rfl

/-- The character-weighted long coefficient is exactly the negative detector tail,
including the unit and zero indices. -/
theorem long_moebius_divisors_mul_character_eq_neg_detector_tail
    (X q n : ℕ) (χ : DirichletCharacter ℂ (q + 1)) :
    ((∑ d ∈ n.divisors.filter (fun d => X + 1 < d), (moebius d : ℤ)) : ℂ) * χ n =
      -cglDetectorTailCoefficient X q χ n := by
  rw [← Int.cast_sum, sum_long_moebius_divisors_eq, cglDetectorTailCoefficient,
    cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient_all,
    cglUnitCoefficient]
  by_cases hn : n = 1
  · subst n
    simp
  · simp [hn]

/-- The existing divisor bound controls the regrouped long completion coefficient. -/
theorem norm_long_moebius_divisors_mul_character_le (X q n : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) :
    ‖((∑ d ∈ n.divisors.filter (fun d => X + 1 < d), (moebius d : ℤ)) : ℂ) * χ n‖ ≤
      n.divisors.card := by
  rw [long_moebius_divisors_mul_character_eq_neg_detector_tail, norm_neg]
  exact norm_cglDetectorTailCoefficient_le_card_divisors X q χ n

/-- The short inverse and the regrouped long inverse reconstruct any input exactly. -/
theorem powerCompletion_short_remainder (L m : ℕ) (w : ℕ →* ℝ)
    (f : ArithmeticFunction ℝ) :
    f = powerTwistedDilation m w (Sieve.truncatedMoebius L) *
        (powerTwistedDilation m w (ζ : ArithmeticFunction ℝ) * f) +
      powerTwistedDilation m w (Sieve.moebiusZetaDefect L) * f := by
  simp only [Sieve.moebiusZetaDefect, map_sub, map_one, map_mul]
  ring

/-- Repeated short reconstruction leaves the exact `k`th power of the sieve defect. -/
theorem powerCompletion_geometric_reconstruction (L k m : ℕ) (w : ℕ →* ℝ)
    (f : ArithmeticFunction ℝ) :
    f = (powerTwistedDilation m w (Sieve.truncatedMoebius L) *
        ∑ j ∈ Finset.range k, (powerTwistedDilation m w (Sieve.moebiusZetaDefect L)) ^ j) *
        (powerTwistedDilation m w (ζ : ArithmeticFunction ℝ) * f) +
      (powerTwistedDilation m w (Sieve.moebiusZetaDefect L)) ^ k * f := by
  let E := powerTwistedDilation m w (Sieve.moebiusZetaDefect L)
  have hE : 1 - E = powerTwistedDilation m w (Sieve.truncatedMoebius L) *
      powerTwistedDilation m w (ζ : ArithmeticFunction ℝ) := by
    simp [E, Sieve.moebiusZetaDefect]
  calc
    f = (1 - E ^ k) * f + E ^ k * f := by ring
    _ = _ := by
      rw [← mul_neg_geom_sum E k, hE]
      ring

/-- Power dilation raises the existing defect support threshold to its exponent. -/
theorem powerCompletion_defect_pow_vanishesBelow (L k m : ℕ) (w : ℕ →* ℝ) :
    Sieve.VanishesBelow
      ((powerTwistedDilation m w (Sieve.moebiusZetaDefect L)) ^ k)
      ((L + 1) ^ (k * (m + 1))) := by
  intro n hn
  rw [← map_pow]
  by_cases hp : ∃ a, a ^ (m + 1) = n
  · obtain ⟨a, rfl⟩ := hp
    rw [powerTwistedDilation_apply_pow]
    have ha : a < (L + 1) ^ k := by
      by_contra h
      have hle := pow_le_pow_left' (Nat.le_of_not_gt h) (m + 1)
      rw [← pow_mul] at hle
      exact (not_le_of_gt hn hle).elim
    rw [Sieve.moebiusZetaDefect_pow_vanishesBelow L k a ha, mul_zero]
  · exact mPart_apply_of_forall_pow_ne _ _ (fun a ha => hp ⟨a, ha⟩)

/-- The geometric reconstruction is exact throughout its full finite support range. -/
theorem powerCompletion_geometric_exact_below (L k m : ℕ) (w : ℕ →* ℝ)
    (f : ArithmeticFunction ℝ) (n : Fin ((L + 1) ^ (k * (m + 1)))) :
    f n = ((powerTwistedDilation m w (Sieve.truncatedMoebius L) *
        ∑ j ∈ Finset.range k, (powerTwistedDilation m w (Sieve.moebiusZetaDefect L)) ^ j) *
        (powerTwistedDilation m w (ζ : ArithmeticFunction ℝ) * f)) n := by
  have hf : Sieve.VanishesBelow f 1 := by
    intro i hi
    have hi0 : i = 0 := by omega
    simp [hi0]
  have hrem := Sieve.vanishesBelow_mul
    (powerCompletion_defect_pow_vanishesBelow L k m w) hf
  have hn := hrem n (by simpa only [mul_one] using n.isLt)
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n)
    (powerCompletion_geometric_reconstruction L k m w f)
  simpa only [ArithmeticFunction.add_apply, hn, add_zero] using h

end RHTower
