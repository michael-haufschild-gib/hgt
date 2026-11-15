import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntrinsicRationalCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerExactPointCount


/-!
# Rational-point correction under normalization

The affine equation has one point over each branch zero. Normalization
replaces each nonzero branch point by `δ` rational primes. Adding infinity
therefore changes the literal affine count by `(q-1)(δ-1)+1`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Resolving the branch fibers and adding infinity gives the exact correction to the affine point count. -/
theorem normalizedKummerRationalChartPlaces_affine_correction :
    Nat.card (normalizedKummerRationalChartPlaces p d n r) =
      Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) +
        (p ^ (d + 1) - 1) *
          (Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1)) - 1) + 1 := by
  rw [normalizedKummerRationalChartPlaces_card, normalizedKummer_primePower_affine_card]
  let q := p ^ (d + 1)
  let Q := p ^ (kummerSquareIndex d n + 1)
  let δ := Nat.gcd (Q + 1) (kummerExponent q (r + 1))
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  have hδ : δ - 1 + 1 = δ := Nat.sub_add_cancel
    (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _))
  change (q * Q - 1 - (q - 1) * δ) * (Q + 1) + (q - 1) * δ + 2 =
    (q * Q - 1 - (q - 1) * δ) * (Q + 1) + q + (q - 1) * (δ - 1) + 1
  nlinarith only [hq, congrArg (fun x : ℕ => (q - 1) * x) hδ]

/-- The intrinsic rational-place count differs from the literal affine count by the exact normalization correction. -/
theorem normalizedKummerRationalPlaces_affine_correction :
    Nat.card (NormalizedKummerRationalPlaces p d n r) =
      Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) +
        (p ^ (d + 1) - 1) *
          (Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1)) - 1) + 1 := by
  rw [normalizedKummerRationalPlaces_card_eq_charts,
    normalizedKummerRationalChartPlaces_affine_correction]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
