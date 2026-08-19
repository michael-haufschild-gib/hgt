import GaloisForLFunctions.RHTower.Sieve.RouteTScheduleHats

/-!
# Polynomial majorants for the two threshold prefactors

Both prefactors of `Sieve/RouteTScheduleWorstCase` are a constant times a power of `L` times
`(1 + log L)²`, once the reciprocal-width budget is replaced by its polylogarithmic size.  Recording
them separately keeps the threshold limits to a single application of
`Sieve/PolylogRpowDomination`.
-/

namespace RHTower.Sieve

noncomputable section

theorem one_le_one_add_log_sq {L : ℝ} (hL : 1 ≤ L) : (1 : ℝ) ≤ (1 + Real.log L) ^ 2 := by
  have hlog : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  nlinarith [hlog]

theorem rpow_le_rpow_exp {L a b : ℝ} (hL : 1 ≤ L) (hab : a ≤ b) : L ^ a ≤ L ^ b :=
  Real.rpow_le_rpow_of_exponent_le hL hab

theorem self_le_rpow {L b : ℝ} (hL : 1 ≤ L) (hb : 1 ≤ b) : L ≤ L ^ b := by
  have h1 : L ^ (1 : ℝ) ≤ L ^ b := Real.rpow_le_rpow_of_exponent_le hL hb
  rwa [Real.rpow_one] at h1

/-- **The contour prefactor's inner bracket.** -/
theorem contour_bracket_le {L G G1 : ℝ} (hL : 1 ≤ L) (hG0 : 0 < G) (hG1 : 0 < G1)
    (hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2) :
    1 + (4 + 2 * L) * G + 2 * L ≤ (3 + 6 * G1) * (L ^ (1.9 : ℝ) * (1 + Real.log L) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq := one_le_one_add_log_sq hL
  have hmul : L * L ^ (0.9 : ℝ) = L ^ (1.9 : ℝ) := by
    rw [show (1.9 : ℝ) = 1 + 0.9 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hLb : L ≤ L ^ (1.9 : ℝ) := self_le_rpow hL (by norm_num)
  have hL1b : (1 : ℝ) ≤ L ^ (1.9 : ℝ) := le_trans hL hLb
  have hfac : (4 : ℝ) + 2 * L ≤ 6 * L := by linarith
  have hstep : (4 + 2 * L) * G ≤ 6 * L * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2) :=
    mul_le_mul hfac hGle hG0.le (by linarith)
  have hrw : 6 * L * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2)
      = 6 * G1 * (L ^ (1.9 : ℝ) * (1 + Real.log L) ^ 2) := by
    rw [← hmul]; ring
  rw [hrw] at hstep
  have hG1' : (0 : ℝ) ≤ 6 * G1 := by linarith
  nlinarith [hstep, hLb, hL1b, hsq, hG1']

/-- **The contour prefactor.** -/
theorem contour_prefactor_le {C L G G1 : ℝ} (hC : 0 < C) (hL : 1 ≤ L) (hG0 : 0 < G)
    (hG1 : 0 < G1) (hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2) :
    9 * C * (1 + (4 + 2 * L) * G + 2 * L) * (9 * (2 + L))
      ≤ 243 * C * (3 + 6 * G1) * L ^ (2.9 : ℝ) * (1 + Real.log L) ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq := one_le_one_add_log_sq hL
  have hbr := contour_bracket_le hL hG0 hG1 hGle
  have hmul : L ^ (1.9 : ℝ) * L = L ^ (2.9 : ℝ) := by
    rw [show (2.9 : ℝ) = 1.9 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hbr0 : (0 : ℝ) ≤ 1 + (4 + 2 * L) * G + 2 * L := by positivity
  have h5 : (9 : ℝ) * (2 + L) ≤ 27 * L := by linarith
  have hleft : 9 * C * (1 + (4 + 2 * L) * G + 2 * L)
      ≤ 9 * C * ((3 + 6 * G1) * (L ^ (1.9 : ℝ) * (1 + Real.log L) ^ 2)) := by
    nlinarith [hbr, hC]
  have hleft0 : (0 : ℝ) ≤ 9 * C * (1 + (4 + 2 * L) * G + 2 * L) := by positivity
  have hprod := mul_le_mul hleft h5 (by linarith) (by positivity)
  refine hprod.trans (le_of_eq ?_)
  rw [← hmul]; ring

/-- **The truncation prefactor's inner bracket.** -/
theorem trunc_bracket_le {L G G1 : ℝ} (hL : 1 ≤ L) (hG0 : 0 < G) (hG1 : 0 < G1)
    (hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2) :
    2 + L ^ 2 + (4 + 2 * L) * G ≤ (3 + 6 * G1) * (L ^ 2 * (1 + Real.log L) ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq := one_le_one_add_log_sq hL
  have hmul : L * L ^ (0.9 : ℝ) = L ^ (1.9 : ℝ) := by
    rw [show (1.9 : ℝ) = 1 + 0.9 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hnat : L ^ (2 : ℝ) = L ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hLb : L ^ (1.9 : ℝ) ≤ L ^ 2 := by
    rw [← hnat]; exact rpow_le_rpow_exp hL (by norm_num)
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith [hL]
  have hfac : (4 : ℝ) + 2 * L ≤ 6 * L := by linarith
  have hstep : (4 + 2 * L) * G ≤ 6 * L * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2) :=
    mul_le_mul hfac hGle hG0.le (by linarith)
  have hrw : 6 * L * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2)
      = 6 * G1 * (L ^ (1.9 : ℝ) * (1 + Real.log L) ^ 2) := by
    rw [← hmul]; ring
  rw [hrw] at hstep
  have hcoef : (0 : ℝ) ≤ 6 * G1 * (1 + Real.log L) ^ 2 := by positivity
  have e1 : 6 * G1 * (L ^ (1.9 : ℝ) * (1 + Real.log L) ^ 2)
      ≤ 6 * G1 * (L ^ 2 * (1 + Real.log L) ^ 2) := by nlinarith [hLb, hcoef]
  have e2 : (2 : ℝ) ≤ 2 * (L ^ 2 * (1 + Real.log L) ^ 2) := by nlinarith [hL2, hsq]
  have e3 : L ^ 2 ≤ L ^ 2 * (1 + Real.log L) ^ 2 := by nlinarith [hsq, hL2]
  nlinarith [hstep, e1, e2, e3]

/-- **The truncation prefactor.** -/
theorem trunc_prefactor_le {C L G G1 v : ℝ} (hC : 0 < C) (hL : 1 ≤ L) (hG0 : 0 < G)
    (hG1 : 0 < G1) (hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2)
    (hv : (3 : ℝ) ^ v ≤ 3) :
    9 * C * (3 : ℝ) ^ v * (2 + L ^ 2 + (4 + 2 * L) * G) * (9 * (2 + L))
      ≤ 729 * C * (3 + 6 * G1) * L ^ (3 : ℝ) * (1 + Real.log L) ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hsq := one_le_one_add_log_sq hL
  have hbr := trunc_bracket_le hL hG0 hG1 hGle
  have hnat3 : L ^ (3 : ℝ) = L ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hbr0 : (0 : ℝ) ≤ 2 + L ^ 2 + (4 + 2 * L) * G := by positivity
  have h5 : (9 : ℝ) * (2 + L) ≤ 27 * L := by linarith
  have hcoef : 9 * C * (3 : ℝ) ^ v ≤ 27 * C := by nlinarith [hv, hC]
  have hleft : 9 * C * (3 : ℝ) ^ v * (2 + L ^ 2 + (4 + 2 * L) * G)
      ≤ 27 * C * ((3 + 6 * G1) * (L ^ 2 * (1 + Real.log L) ^ 2)) := by
    exact mul_le_mul hcoef hbr hbr0 (by linarith)
  have hleft0 : (0 : ℝ) ≤ 9 * C * (3 : ℝ) ^ v * (2 + L ^ 2 + (4 + 2 * L) * G) := by positivity
  have hprod := mul_le_mul hleft h5 (by linarith) (by positivity)
  refine hprod.trans (le_of_eq ?_)
  rw [hnat3]; ring

end

end RHTower.Sieve
