import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.KummerCurveDatum

/-!
# The exact Frobenius defect of the Kummer point-count model

All normalized eigenvalues equal -1. The Toeplitz form therefore
collapses to one square, and the unnormalized Frobenius defect is
`2g * |sum d_k*(-Q)^k|²`. Its nullspace is exactly the vanishing of
that evaluation, apart from the genus-zero case where every defect
vanishes.
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
local notation "D" => primePowerKummerCurveDatum p d n r

/-- The point-count Toeplitz form is exactly one squared alternating sum with multiplicity 2g. -/
theorem primePowerKummerCurveDatum_toeplitz (S : Finset ℕ) (a : ℕ → ℝ) :
    (D).toeplitz S a = (2 * g : ℕ) * ‖∑ k ∈ S, (a k : ℂ) * (-1 : ℂ) ^ k‖ ^ 2 := by
  rw [(D).toeplitz_eq_sum_normSq (primePowerKummerCurveDatum_unitary p d n r)]
  change (∑ _ : Fin (2 * g), ‖∑ k ∈ S, (a k : ℂ) * (-1 : ℂ) ^ k‖ ^ 2) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The exact Frobenius defect is the square of evaluation at -Q, multiplied by twice the actual genus. -/
theorem primePowerKummerCurveDatum_spanDefect (S : Finset ℕ) (a : ℕ → ℝ) :
    (D).spanDefect S a = (2 * g : ℕ) * ‖∑ k ∈ S, (a k : ℂ) * (-(Q : ℂ)) ^ k‖ ^ 2 := by
  rw [(D).spanDefect_eq_toeplitz, primePowerKummerCurveDatum_toeplitz]
  apply congrArg (fun z : ℂ => ((2 * g : ℕ) : ℝ) * ‖z‖ ^ 2)
  apply Finset.sum_congr rfl
  intro k _
  rw [primePowerKummerCurveDatum_sqrtq]
  push_cast
  rw [neg_pow]
  ring

/-- The Frobenius defect vanishes exactly in genus zero or when the coefficient polynomial vanishes at -Q. -/
theorem primePowerKummerCurveDatum_spanDefect_eq_zero_iff (S : Finset ℕ) (a : ℕ → ℝ) :
    (D).spanDefect S a = 0 ↔ g = 0 ∨ (∑ k ∈ S, (a k : ℂ) * (-(Q : ℂ)) ^ k) = 0 := by
  rw [primePowerKummerCurveDatum_spanDefect, mul_eq_zero]
  constructor
  · rintro (hg | ha)
    · left
      have hg' : 2 * g = 0 := Nat.cast_eq_zero.mp hg
      omega
    · right
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero ha)
  · rintro (hg | ha)
    · left
      rw [hg, Nat.mul_zero, Nat.cast_zero]
    · right
      rw [ha, norm_zero, zero_pow (by omega : 2 ≠ 0)]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
