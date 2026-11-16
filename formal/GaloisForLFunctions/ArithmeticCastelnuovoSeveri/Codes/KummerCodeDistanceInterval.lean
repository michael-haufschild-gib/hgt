import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Codes.NormalizedKummerEvaluationCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.LinearSingletonBound

/-!
# Distance intervals for maximal Kummer evaluation codes

The designed distance and the linear Singleton bound put the minimum
nonzero weight in an interval of width at most the actual genus. The
evaluation length always exceeds twice the genus, so the family includes
the nontrivial code at pole allowance `2g` for every curve parameter.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "g" => Module.finrank K (NormalizedKummerRegularDifferentials p d n r)
local notation "N" => Q ^ 2 + 2 * Q * g
local notation "I" => NormalizedKummerAlgebraPoints p d n r
local instance : Fintype I := Fintype.ofFinite _

/-- Every maximal Kummer evaluation length exceeds twice the actual genus. -/
theorem normalizedKummer_code_length_gt_twice_genus : 2 * g < N := by
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero _)
    (Fact.out : p.Prime).one_lt
  have hQ2 : 1 < Q ^ 2 := Nat.one_lt_pow (Nat.succ_ne_zero 1) hQ
  have hmul := Nat.mul_le_mul_right g (Nat.mul_le_mul_left 2 (show 1 ≤ Q by omega))
  simp only [mul_one] at hmul
  omega

/-- A nonzero word occurs within genus of the designed distance, and none occurs below it. -/
theorem normalizedKummerEvaluationCode_distance_interval (a : Fin (N - 2 * g)) :
    (∀ w ∈ normalizedKummerEvaluationCode p d n r (2 * g + a.val),
      w ≠ 0 → N - (2 * g + a.val) ≤ Codes.weight w) ∧
    ∃ w ∈ normalizedKummerEvaluationCode p d n r (2 * g + a.val),
      w ≠ 0 ∧ Codes.weight w ≤ N - (2 * g + a.val) + g := by
  refine ⟨normalizedKummerEvaluationCode_weight_bound p d n r _, ?_⟩
  have hdim := normalizedKummerEvaluationCode_finrank p d n r a
  obtain ⟨w, hw, hw0, hbound⟩ := Codes.exists_nonzero_word_weight_le_singleton
    (normalizedKummerEvaluationCode p d n r (2 * g + a.val)) (by omega)
  rw [normalizedKummerEvaluationCode_length, hdim] at hbound
  have ha := a.isLt
  exact ⟨w, hw, hw0, by omega⟩

/-- Every curve supplies a positive-distance code of dimension `g+1` at pole allowance `2g`. -/
theorem normalizedKummerEvaluationCode_twice_genus_parameters :
    Module.finrank K (normalizedKummerEvaluationCode p d n r (2 * g)) = g + 1 ∧
    0 < N - 2 * g ∧
    ∀ w ∈ normalizedKummerEvaluationCode p d n r (2 * g),
      w ≠ 0 → N - 2 * g ≤ Codes.weight w := by
  have hlen := normalizedKummer_code_length_gt_twice_genus p d n r
  have hdim := normalizedKummerEvaluationCode_finrank p d n r
    ⟨0, by omega⟩
  refine ⟨?_, by omega, normalizedKummerEvaluationCode_weight_bound p d n r _⟩
  exact hdim

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
