import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast

/-!
# Uniform coefficient-index bounds for centrally masked pairs

Completing the square reduces the entire growing family of heat coefficient signs to one
quadratic in the integer index. An explicit floor detects negativity below `1/(8m+10)`;
every index is positive above `1/(8m+5)`. Both statements retain the exact multiplicity.
-/

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The quadratic index weight controlling every even heated coefficient of a centrally
masked adverse pair. The dimensionless heat is `t=s/a`. -/
def maskedHeatIndex (m : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * (k + 1) - 2 * ((2 * m + 2 : ℝ) * (2 * m + 1)) * (k + 1) * t +
    ((2 * m + 2 : ℝ) * (2 * m + 1)) * ((2 * m + 4 : ℝ) * (2 * m + 3)) * t ^ 2

theorem maskedHeatIndex_square (m k : ℕ) (t : ℝ) :
    maskedHeatIndex m t k =
      ((k : ℝ) - ((2 * m + 2 : ℝ) * (2 * m + 1)) * t + 1 / 2) ^ 2 +
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * (8 * m + 10) * t ^ 2 -
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * t - 1 / 4 := by
  unfold maskedHeatIndex
  ring

private theorem positive_quadratic_remainder {B e t : ℝ} (hB : 0 < B) (he : 0 < e)
    (hgap : e ^ 2 < 20 * B) (ht : 1 ≤ e * t) :
    0 < B * (e + 5) * t ^ 2 - B * t - 1 / 4 := by
  have htpos : 0 < t := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos he.le (le_of_not_gt hn)
    linarith only [hp, ht]
  have hsq : 1 ≤ e ^ 2 * t ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ e * t + 1 by linarith)
    nlinarith only [hh]
  have hstrict := mul_pos (sub_pos.mpr hgap) (sq_pos_of_pos htpos)
  have hprod := mul_nonneg (show 0 ≤ B * t by positivity) (sub_nonneg.mpr ht)
  nlinarith only [hsq, hstrict, hprod]

/-- A rational upper bound makes every index weight positive, uniformly in multiplicity. -/
theorem maskedHeatIndex_pos_of_upper (m k : ℕ) {t : ℝ}
    (ht : 1 ≤ (8 * m + 5 : ℝ) * t) : 0 < maskedHeatIndex m t k := by
  have hB : 0 < (2 * m + 2 : ℝ) * (2 * m + 1) := by positivity
  have he : 0 < (8 * m + 5 : ℝ) := by positivity
  have hgap : (8 * m + 5 : ℝ) ^ 2 < 20 * ((2 * m + 2 : ℝ) * (2 * m + 1)) := by
    nlinarith only [sq_nonneg (m : ℝ), Nat.cast_nonneg m]
  have hrem := positive_quadratic_remainder hB he hgap ht
  rw [maskedHeatIndex_square]
  have hs := sq_nonneg ((k : ℝ) - ((2 * m + 2 : ℝ) * (2 * m + 1)) * t + 1 / 2)
  nlinarith only [hrem, hs]

/-- Rounding incurs at most one quarter in the completed square, leaving an explicit
signed margin for the detecting coefficient. -/
theorem maskedHeatIndex_floor_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    maskedHeatIndex m t (Nat.floor (((2 * m + 2 : ℝ) * (2 * m + 1)) * t)) ≤
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * t * ((8 * m + 10 : ℝ) * t - 1) := by
  let x : ℝ := ((2 * m + 2 : ℝ) * (2 * m + 1)) * t
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  have hp := mul_nonneg (sub_nonneg.mpr hlo)
    (show 0 ≤ (Nat.floor x : ℝ) + 1 - x by linarith only [hhi])
  have hsq : ((Nat.floor x : ℝ) - x + 1 / 2) ^ 2 ≤ 1 / 4 := by
    nlinarith only [hp]
  dsimp only [x] at hsq
  rw [maskedHeatIndex_square]
  nlinarith only [hsq]

/-- Rounding the completed-square minimizer gives an explicit negative coefficient below
inverse multiplicity scale. The detecting index always remains inside the actual degree. -/
theorem maskedHeatIndex_floor_neg (m : ℕ) {t : ℝ} (ht : 0 < t)
    (hsmall : (8 * m + 10 : ℝ) * t < 1) :
    let k := Nat.floor (((2 * m + 2 : ℝ) * (2 * m + 1)) * t)
    k ≤ m + 1 ∧ maskedHeatIndex m t k < 0 := by
  let B : ℝ := (2 * m + 2 : ℝ) * (2 * m + 1)
  let d : ℝ := 8 * m + 10
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBd : B < d * (m + 1 : ℝ) := by
    dsimp only [B, d]
    nlinarith only [sq_nonneg (m : ℝ), Nat.cast_nonneg m]
  have hx : 0 < B * t := mul_pos hB ht
  have hlo := Nat.floor_le hx.le
  have hbound : B * t < (m + 1 : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hBd ht
    have hmul' := mul_lt_mul_of_pos_left hsmall (show (0 : ℝ) < m + 1 by positivity)
    dsimp only [d] at hmul
    nlinarith only [hmul, hmul']
  have hk : Nat.floor (B * t) ≤ m + 1 := by
    have hh : (Nat.floor (B * t) : ℝ) ≤ (m + 1 : ℝ) := hlo.trans hbound.le
    exact_mod_cast hh
  refine ⟨hk, ?_⟩
  change maskedHeatIndex m t (Nat.floor (B * t)) < 0
  have hnegative := mul_neg_of_pos_of_neg hx (show d * t - 1 < 0 from sub_neg.mpr hsmall)
  exact (maskedHeatIndex_floor_le m ht.le).trans_lt hnegative

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
