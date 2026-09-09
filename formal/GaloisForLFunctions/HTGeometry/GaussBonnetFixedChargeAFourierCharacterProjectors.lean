import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFourierGrid
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAFiveFourierModes
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTSpectralCalculus

/-!
Exact conversion of critical Gibbs characters into projectors of the existing QFT.
Negative harmonics are proved using periodicity of roots of unity, not approximation.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- QFT column projectors are normalized powers of the grid difference character. -/
theorem egbFixedChargeAFourierCharacter_projector
    (n : ℕ) (r i j : Fin (2 ^ n)) :
    ((2 : ℝ) ^ n : ℂ) * QFTMatrix n i r * star (QFTMatrix n j r) =
      egbFixedChargeAFourierCharacter n i j ^ r.val := by
  rw [QFT_entry, QFT_entry, star_mul', star_invSqrtN]
  calc
    _ = (((2 : ℝ) ^ n : ℂ) * (invSqrtN n * invSqrtN n)) *
        (omega n ^ (i.val * r.val) * star (omega n ^ (j.val * r.val))) := by ring
    _ = omega n ^ (i.val * r.val) * star (omega n ^ (j.val * r.val)) := by
      rw [invSqrtN_mul_self]
      simp only [Complex.ofReal_pow, Complex.ofReal_ofNat,
        mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]
    _ = _ := by simp only [egbFixedChargeAFourierCharacter, mul_pow, star_pow, pow_mul]

/-- A full grid period makes every difference character equal to one. -/
theorem egbFixedChargeAFourierCharacter_period
    (n : ℕ) (i j : Fin (2 ^ n)) :
    egbFixedChargeAFourierCharacter n i j ^ (2 ^ n) = 1 := by
  have hp (k : ℕ) : (omega n ^ k) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, Nat.mul_comm k, pow_mul, omega_pow_eq_one, one_pow]
  simp only [egbFixedChargeAFourierCharacter, mul_pow, ← star_pow, hp, star_one, mul_one]

/-- Conjugation reverses the difference character. -/
theorem egbFixedChargeAFourierCharacter_star_inv
    (n : ℕ) (i j : Fin (2 ^ n)) :
    star (egbFixedChargeAFourierCharacter n i j) =
      (egbFixedChargeAFourierCharacter n i j)⁻¹ := by
  simp only [egbFixedChargeAFourierCharacter, star_mul', star_pow,
    star_omega, mul_inv_rev, inv_pow, star_inv₀, inv_inv]
  ring

/-- The five chosen QFT modes are exactly the five Laurent characters. -/
theorem egbFixedChargeAFourierCharacter_modes
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    (fun k : Fin 5 => egbFixedChargeAFourierCharacter (n + 3) i j ^
      (egbFixedChargeAFiveFourierModes n k).val) =
      ![1, egbFixedChargeAFourierCharacter (n + 3) i j,
        egbFixedChargeAFourierCharacter (n + 3) i j ^ 2,
        star (egbFixedChargeAFourierCharacter (n + 3) i j) ^ 2,
        star (egbFixedChargeAFourierCharacter (n + 3) i j)] := by
  have hb : 8 ≤ 2 ^ (n + 3) := by
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
    rw [pow_add]
    norm_num
    omega
  have hn : egbFixedChargeAFourierCharacter (n + 3) i j ≠ 0 := by
    unfold egbFixedChargeAFourierCharacter
    exact mul_ne_zero (pow_ne_zero _ (omega_ne_zero _))
      (by rw [star_pow, star_omega]; exact pow_ne_zero _ (inv_ne_zero (omega_ne_zero _)))
  funext k
  fin_cases k <;> norm_num [egbFixedChargeAFiveFourierModes]
  · change egbFixedChargeAFourierCharacter (n + 3) i j ^ (2 ^ (n + 3) - 2) =
      star (egbFixedChargeAFourierCharacter (n + 3) i j) ^ 2
    rw [pow_sub₀ _ hn (by omega), egbFixedChargeAFourierCharacter_period,
      one_mul, ← inv_pow, egbFixedChargeAFourierCharacter_star_inv]
  · change egbFixedChargeAFourierCharacter (n + 3) i j ^ (2 ^ (n + 3) - 1) =
      star (egbFixedChargeAFourierCharacter (n + 3) i j)
    rw [pow_sub₀ _ hn (by omega), egbFixedChargeAFourierCharacter_period,
      one_mul, pow_one, egbFixedChargeAFourierCharacter_star_inv]

end

end GaloisForLFunctions.HTGeometry
