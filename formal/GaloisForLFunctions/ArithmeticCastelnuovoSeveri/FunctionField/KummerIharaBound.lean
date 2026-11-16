import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerClosedPointDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialOrderPointCounts

/-!
# The Ihara genus bound from actual Kummer point counts

The degree-two extension contains at least as many points as the base field.
The maximal count formulas turn this inequality into `2g ≤ Q(Q-1)`, where
`g` is the dimension of the actual regular differentials. No independent
genus bound is assumed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis PolynomialOrderClosedPoints
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "A" => PrimePowerKummerThreePointAffineNormalization p d n r
local notation "Q" => p ^ (s + 1)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c₀ (q - 2) R))

/-- Actual Kummer rational-place counts increase under divisible constant extensions. -/
theorem primePowerKummerExtensionPointCount_mono {e f : ℕ} [NeZero e] [NeZero f]
    (hef : e ∣ f) :
    primePowerKummerExtensionPointCount p d n r e ≤
      primePowerKummerExtensionPointCount p d n r f := by
  rw [primePowerKummerExtensionPointCount_eq_algHom,
    primePowerKummerExtensionPointCount_eq_algHom]
  exact Nat.add_le_add_right (card_algHom_extension_mono K A p hef) 1

private theorem maximal_count_ihara_bound (u t a b : ℝ) (hu : 0 < u)
    (hA : a = u ^ 2 + 1 + t * u)
    (hB : b = u ^ 4 + 1 - t * u ^ 2) (hle : a ≤ b) :
    t ≤ u * (u - 1) := by
  have hfactor : u * (u + 1) * (u * (u - 1) - t) = b - a := by
    rw [hA, hB]
    ring
  have hpos : 0 < u * (u + 1) := mul_pos hu (by linarith only [hu])
  have hz : 0 ≤ u * (u + 1) * (u * (u - 1) - t) := by
    rw [hfactor]
    linarith only [hle]
  have hdiff := nonneg_of_mul_nonneg_right hz hpos
  linarith only [hdiff]

/-- The actual differential genus satisfies the sharp maximal-curve bound. -/
theorem primePowerKummer_genus_ihara_bound : 2 * g ≤ Q * (Q - 1) := by
  have hQnat : 0 < Q := pow_pos (Fact.out : p.Prime).pos _
  have hQ : 0 < (Q : ℝ) :=
    pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have h1c := primePowerKummerExtensionPointCount_eq p d n r 1
  simp only [pow_one, mul_neg, sub_neg_eq_add] at h1c
  have h1 : (primePowerKummerExtensionPointCount p d n r 1 : ℝ) =
      (Q : ℝ) ^ 2 + 1 + (2 * g : ℕ) * (Q : ℝ) := by exact_mod_cast h1c
  have h2c := primePowerKummerExtensionPointCount_eq p d n r 2
  have h2 : (primePowerKummerExtensionPointCount p d n r 2 : ℝ) =
      (Q : ℝ) ^ 4 + 1 - (2 * g : ℕ) * (Q : ℝ) ^ 2 := by
    rw [← pow_mul (Q : ℂ) 2 2, neg_sq] at h2c
    exact_mod_cast h2c
  have hle : (primePowerKummerExtensionPointCount p d n r 1 : ℝ) ≤
      (primePowerKummerExtensionPointCount p d n r 2 : ℝ) := by
    exact_mod_cast primePowerKummerExtensionPointCount_mono p d n r (one_dvd 2)
  have hbound := maximal_count_ihara_bound _ _ _ _ hQ h1 h2 hle
  have hbound' : ((2 * g : ℕ) : ℝ) ≤ ((Q * (Q - 1) : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ Q by omega),
      Nat.cast_one, Nat.cast_pow] using hbound
  exact_mod_cast hbound'

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
