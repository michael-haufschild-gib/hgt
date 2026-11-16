import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.KummerPointCountZeta

/-!
# A Frobenius datum for the actual Kummer extension counts

The signed point counts have repeated eigenvalue -Q, with multiplicity
twice the dimension of regular differentials. They therefore define a
unitary curve datum whose ghost and zeta series agree with the actual
constant-extension point counts. This is a point-count calibration of
the Frobenius-span model.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "Q" => p ^ (s + 1)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c₀ (q - 2) R))

/-- The curve datum calibrated by the signed counts of actual Kummer constant extensions. -/
def primePowerKummerCurveDatum : CurveDatum (Fin (2 * g)) where
  «q» := (Q : ℝ) ^ 2
  one_lt_q := by
    have hQ : 1 < (Q : ℝ) := by
      exact_mod_cast Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
    nlinarith only [hQ, sq_nonneg ((Q : ℝ) - 1)]
  β _ := -1
  conjPerm := Equiv.refl _
  β_conjPerm _ := by simp only [map_neg, map_one]
  fePerm := Equiv.refl _
  β_fePerm _ := by ring

/-- The square-root field size of the calibrated datum is the original prime power Q. -/
theorem primePowerKummerCurveDatum_sqrtq : (primePowerKummerCurveDatum p d n r).sqrtq = (Q : ℝ) :=
  Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg p) (s + 1))

/-- Every normalized eigenvalue in the actual point-count calibration has norm one. -/
theorem primePowerKummerCurveDatum_unitary (i : Fin (2 * g)) :
    ‖(primePowerKummerCurveDatum p d n r).β i‖ = 1 := by
  change ‖(-1 : ℂ)‖ = 1
  rw [norm_neg, norm_one]

/-- Every reciprocal Frobenius eigenvalue in the calibration is exactly -Q. -/
theorem primePowerKummerCurveDatum_alpha (i : Fin (2 * g)) :
    (primePowerKummerCurveDatum p d n r).alpha i = -(Q : ℂ) := by
  rw [CurveDatum.alpha, primePowerKummerCurveDatum_sqrtq]
  change (((Q : ℝ) : ℂ)) * (-1) = -(Q : ℂ)
  push_cast
  ring

/-- The calibrated Lefschetz number equals the actual rational-place count over every positive degree. -/
theorem primePowerKummerCurveDatum_pointCount (e : ℕ) [NeZero e] :
    ((primePowerKummerCurveDatum p d n r).pointCount e : ℂ) =
      (primePowerKummerExtensionPointCount p d n r e : ℂ) := by
  let D := primePowerKummerCurveDatum p d n r
  have ht : (D.trace e : ℂ) = (2 * g : ℕ) * (-1 : ℂ) ^ e := by
    rw [← D.powerSum_eq_trace]
    change (∑ _ : Fin (2 * g), (-1 : ℂ) ^ e) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (D.pointCount e : ℂ) = _
  rw [CurveDatum.pointCount]
  have hq : D.q = (Q : ℝ) ^ 2 := rfl
  have hs : D.sqrtq = (Q : ℝ) := primePowerKummerCurveDatum_sqrtq p d n r
  rw [hq, hs]
  push_cast
  rw [ht, primePowerKummerExtensionPointCount_eq, neg_pow]
  ring

/-- The curve datum's entire ghost series is the actual sequence of constant-extension point counts. -/
theorem primePowerKummerCurveDatum_ghostSeries :
    (primePowerKummerCurveDatum p d n r).ghostSeries = primePowerKummerPointCountGhost p d n r := by
  ext e
  simp only [CurveDatum.ghostSeries, primePowerKummerPointCountGhost, PowerSeries.coeff_mk]
  by_cases he : e = 0
  · subst e
    rw [primePowerKummerExtensionPointCount_zero]
    simp only [Nat.cast_zero, ite_true]
  · letI : NeZero e := ⟨he⟩
    rw [if_neg he, primePowerKummerCurveDatum_pointCount]

/-- The datum's formal zeta series is exactly the series determined by actual Kummer extension counts. -/
theorem primePowerKummerCurveDatum_zetaSeries :
    (primePowerKummerCurveDatum p d n r).zetaSeries = primePowerKummerZeta p d n r := by
  apply primePowerKummerZeta_unique p d n r
  · exact CurveDatum.constantCoeff_zetaSeries _
  · rw [← primePowerKummerCurveDatum_ghostSeries]
    exact CurveDatum.zetaSeries_hasGhost _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
