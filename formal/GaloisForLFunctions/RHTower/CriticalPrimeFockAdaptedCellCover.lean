import GaloisForLFunctions.RHTower.CriticalPrimeFockAdaptedCellMass
import GaloisForLFunctions.HTGeometry.RpowConcavity

namespace RHTower

noncomputable section

/-- Index of the unit adapted-metric cell containing `x`. -/
def criticalPrimeFockAdaptedCellIndex (m x : ℝ) : ℕ :=
  ⌊ x ^ (m / 2) ⌋₊

theorem criticalPrimeFockAdaptedCellIndex_pos
    {m x : ℝ} (hm : 0 < m) (hx : 1 ≤ x) :
    0 < criticalPrimeFockAdaptedCellIndex m x := by
  rw [criticalPrimeFockAdaptedCellIndex, Nat.floor_pos]
  exact Real.one_le_rpow hx (by positivity)

theorem criticalPrimeFockAdaptedCellCenter_index_le
    {m x : ℝ} (hm : 0 < m) (hx : 1 ≤ x) :
    criticalPrimeFockAdaptedCellCenter m
      (criticalPrimeFockAdaptedCellIndex m x) ≤ x := by
  let a : ℝ := x ^ (m / 2)
  let n : ℕ := criticalPrimeFockAdaptedCellIndex m x
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have ha0 : 0 ≤ a := Real.rpow_nonneg hx0 _
  have hnle : (n : ℝ) ≤ a := by
    simpa [n, a, criticalPrimeFockAdaptedCellIndex] using Nat.floor_le ha0
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n) hnle
    (by positivity : 0 ≤ 2 / m)
  have hcancel : a ^ (2 / m) = x := by
    dsimp [a]
    rw [← Real.rpow_mul hx0]
    have : m / 2 * (2 / m) = 1 := by field_simp
    rw [this, Real.rpow_one]
  simpa [criticalPrimeFockAdaptedCellCenter, n, hcancel] using hpow

theorem criticalPrimeFockRadius_adaptedCellCenter_eq
    {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) :
    criticalPrimeFockRadius m (criticalPrimeFockAdaptedCellCenter m n) =
      (n : ℝ) ^ (2 / m - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold criticalPrimeFockAdaptedCellCenter
  rw [criticalPrimeFockRadius_eq_rpow
      (Real.rpow_nonneg hnR.le (2 / m)),
    ← Real.rpow_mul hnR.le]
  congr 1
  field_simp

theorem sub_adaptedCellCenter_index_lt_radius
    {m x : ℝ} (hm : 2 ≤ m) (hx : 1 ≤ x) :
    x - criticalPrimeFockAdaptedCellCenter m
        (criticalPrimeFockAdaptedCellIndex m x) <
      criticalPrimeFockRadius m
        (criticalPrimeFockAdaptedCellCenter m
          (criticalPrimeFockAdaptedCellIndex m x)) := by
  let α : ℝ := 2 / m
  let a : ℝ := x ^ (m / 2)
  let n : ℕ := criticalPrimeFockAdaptedCellIndex m x
  let c : ℝ := a - n
  have hm0 : 0 < m := by linarith
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have ha0 : 0 ≤ a := Real.rpow_nonneg hx0 _
  have hnpos : 0 < n := by
    simpa [n] using criticalPrimeFockAdaptedCellIndex_pos hm0 hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnle : (n : ℝ) ≤ a := by
    simpa [n, a, criticalPrimeFockAdaptedCellIndex] using Nat.floor_le ha0
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c < 1 := by
    have h := Nat.lt_floor_add_one a
    dsimp [c, n, criticalPrimeFockAdaptedCellIndex]
    linarith
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_one hm0]
    linarith
  have hconc := GaloisForLFunctions.HTGeometry.rpow_sub_rpow_le
    (A := a) (c := c) (β := α) hα1 hc0 (by simpa [c] using hnR)
  have haCancel : a ^ α = x := by
    dsimp [a, α]
    rw [← Real.rpow_mul hx0]
    have : m / 2 * (2 / m) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hsub : a - c = n := by dsimp [c]; ring
  have hrpos : 0 < (n : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos hnR _
  have hstrict : c * (n : ℝ) ^ (α - 1) <
      (n : ℝ) ^ (α - 1) := by nlinarith
  rw [hsub, haCancel] at hconc
  rw [criticalPrimeFockRadius_adaptedCellCenter_eq hm0 hnpos]
  change x - (n : ℝ) ^ α < (n : ℝ) ^ (α - 1)
  exact hconc.trans_lt hstrict

theorem abs_sub_adaptedCellCenter_index_lt_radius
    {m x : ℝ} (hm : 2 ≤ m) (hx : 1 ≤ x) :
    |x - criticalPrimeFockAdaptedCellCenter m
        (criticalPrimeFockAdaptedCellIndex m x)| <
      criticalPrimeFockRadius m
        (criticalPrimeFockAdaptedCellCenter m
          (criticalPrimeFockAdaptedCellIndex m x)) := by
  rw [abs_of_nonneg (sub_nonneg.mpr
    (criticalPrimeFockAdaptedCellCenter_index_le (by linarith) hx))]
  exact sub_adaptedCellCenter_index_lt_radius hm hx

end

end RHTower
