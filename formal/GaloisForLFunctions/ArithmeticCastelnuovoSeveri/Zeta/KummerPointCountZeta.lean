import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExtensionCountSequence
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.MaximalPointCountSeries

/-!
# The zeta series of the actual Kummer extension counts

The rational places of every finite constant extension determine a
unique formal series with constant coefficient one. The signed count
formula gives its rational expression with numerator `(1+QT)^(2g)`,
where g is the dimension of the actual regular differentials.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis PowerSeries
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "Q" => p ^ (s + 1)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c₀ (q - 2) R))

/-- The actual extension point counts, regarded as a formal ghost series. -/
def primePowerKummerPointCountGhost : PowerSeries ℂ :=
  PowerSeries.mk fun e => (primePowerKummerExtensionPointCount p d n r e : ℂ)

/-- The actual point-count ghost series equals the repeated-eigenvalue signed expression. -/
theorem primePowerKummerPointCountGhost_eq :
    primePowerKummerPointCountGhost p d n r = maximalPointCountSeries (Q : ℂ) (2 * g) := by
  ext e
  simp only [primePowerKummerPointCountGhost, maximalPointCountSeries, coeff_mk]
  by_cases he : e = 0
  · subst e
    rw [primePowerKummerExtensionPointCount_zero]
    simp only [Nat.cast_zero, ite_true]
  · letI : NeZero e := ⟨he⟩
    rw [if_neg he, primePowerKummerExtensionPointCount_eq]

/-- The zeta series associated with all actual rational-place counts of the fixed Kummer curve. -/
def primePowerKummerZeta : PowerSeries ℂ := maximalPointCountZeta (Q : ℂ) (2 * g)

/-- The zeta series is normalized to have constant coefficient one. -/
theorem primePowerKummerZeta_constantCoeff : constantCoeff (primePowerKummerZeta p d n r) = 1 :=
  maximalPointCountZeta_constantCoeff _ _

/-- Every ghost coefficient is the actual number of rational places over that constant extension. -/
theorem primePowerKummerZeta_hasGhost :
    HasGhost (primePowerKummerZeta p d n r) (primePowerKummerPointCountGhost p d n r) := by
  rw [primePowerKummerPointCountGhost_eq]
  exact maximalPointCountZeta_hasGhost _ _

/-- All actual extension point counts and constant coefficient one determine this series uniquely. -/
theorem primePowerKummerZeta_unique (Z : PowerSeries ℂ) (h0 : constantCoeff Z = 1)
    (hZ : HasGhost Z (primePowerKummerPointCountGhost p d n r)) :
    Z = primePowerKummerZeta p d n r := by
  rw [primePowerKummerPointCountGhost_eq] at hZ
  exact maximalPointCountZeta_unique _ _ Z h0 hZ

/-- The zeta series has the exact rational numerator with multiplicity twice the differential dimension. -/
theorem primePowerKummerZeta_rational :
    ((1 - X) * (1 - C ((Q : ℂ) ^ 2) * X)) * primePowerKummerZeta p d n r =
      (1 + C (Q : ℂ) * X) ^ (2 * g) :=
  maximalPointCountZeta_rational _ _

/-- The zeta series determined by the actual extension counts has integral coefficients. -/
theorem primePowerKummerZeta_integral :
    ∃ Z : PowerSeries ℤ, constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Z = primePowerKummerZeta p d n r := by
  simpa only [primePowerKummerZeta, Nat.cast_pow] using
    maximalPointCountZeta_integral Q (2 * g)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
