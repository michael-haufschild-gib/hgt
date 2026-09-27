import GaloisForLFunctions.RHTower.XiGlobalPacketDensity
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Actual divisor cells indexed by absolute height, retaining all multiplicities -/

open Complex
noncomputable section
namespace RHTower

def xiAbsoluteHeightCell (j : ℕ) : Finset XiZeroCopy :=
  ((finite_xiZeroCopy_band 0 (show 0 ≤ (j : ℝ) + 1 by positivity)).toFinset).filter
    (fun q => ⌊|(q.1 : ℂ).im|⌋₊ = j)

theorem mem_xiAbsoluteHeightCell (j : ℕ) (q : XiZeroCopy) :
    q ∈ xiAbsoluteHeightCell j ↔ ⌊|(q.1 : ℂ).im|⌋₊ = j := by
  classical
  simp only [xiAbsoluteHeightCell, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, sub_zero]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have ht := Nat.lt_floor_add_one |(q.1 : ℂ).im|
    rw [h] at ht
    exact ht.le

/-- Absolute-height cells retain both reflected packets and satisfy a global logarithmic bound. -/
theorem exists_xiAbsoluteHeightCell_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      ((xiAbsoluteHeightCell j).card : ℝ) ≤ C * (1 + Real.log (3 + (j : ℝ))) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_xiUnitHeightPacket_global_log_bound
  refine ⟨2 * C, by positivity, fun j => ?_⟩
  let T := (j : ℝ) + 1 / 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hsub : xiAbsoluteHeightCell j ⊆ xiUnitHeightPacket T ∪ xiUnitHeightPacket (-T) := by
    intro q hq
    have hj := (mem_xiAbsoluteHeightCell j q).mp hq
    have hlo := Nat.floor_le (abs_nonneg (q.1 : ℂ).im)
    have hhi := Nat.lt_floor_add_one |(q.1 : ℂ).im|
    rw [hj] at hlo hhi
    rcases le_total 0 (q.1 : ℂ).im with hp | hn
    · apply Finset.mem_union.mpr
      left
      rw [mem_xiUnitHeightPacket, abs_le]
      rw [abs_of_nonneg hp] at hlo hhi
      dsimp only [T]
      constructor <;> linarith only [hlo, hhi]
    · apply Finset.mem_union.mpr
      right
      rw [mem_xiUnitHeightPacket, abs_le]
      rw [abs_of_nonpos hn] at hlo hhi
      dsimp only [T]
      constructor <;> linarith only [hlo, hhi]
  have hc : ((xiAbsoluteHeightCell j).card : ℝ) ≤
      ((xiUnitHeightPacket T).card : ℝ) + ((xiUnitHeightPacket (-T)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have ht := hbound T
  have hn := hbound (-T)
  rw [abs_neg] at hn
  have hl : Real.log (2 + |T|) ≤ Real.log (3 + (j : ℝ)) := by
    rw [abs_of_pos hT]
    apply Real.log_le_log (by positivity)
    dsimp [T]
    linarith
  have hs := mul_le_mul_of_nonneg_left hl hC.le
  nlinarith only [hc, ht, hn, hs]

end RHTower
