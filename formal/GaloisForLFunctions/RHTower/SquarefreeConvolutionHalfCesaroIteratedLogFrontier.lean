import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroFastScheduleNoGo
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfIteratedLogSchedule
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Iterated-log Cesàro schedule frontier

The canonical iterated-logarithmic Cayley schedule is cofinal, but its boundary amplification grows
too slowly to satisfy `CesaroPoleScheduleFast`.  It therefore survives the general fast-schedule
no-go.  This is only a sharp boundary statement: local boundedness of the scheduled Cesàro family
remains the exact open analytic input.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- The canonical iterated-log degree lies strictly outside the fast-schedule no-go. -/
theorem not_cesaroPoleScheduleFast_iteratedLogarithmicCayleySchedule :
    ¬ CesaroPoleScheduleFast iteratedLogarithmicCayleySchedule := by
  rintro ⟨B, hB, N₀, hfast⟩
  have hscale := eventually_iteratedLogarithmicCayleySchedule_fixedBaseScale_le
    (q := 5) (by norm_num) (δ := (6 / 11 : ℝ)) (by norm_num)
  have hdomReal := RHTower.Sieve.eventually_const_mul_rpow_polylog_le_rpow
    (C := 2 * B) (α := (6 / 11 : ℝ)) (β := (1 : ℝ)) 0 (by norm_num)
  have hdom := tendsto_natCast_atTop_atTop.eventually hdomReal
  obtain ⟨N, hscaleN, hdomN, hN⟩ :=
    (hscale.and (hdom.and (eventually_ge_atTop (max N₀ 1)))).exists
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨_, hfastN⟩ := hfast N hNN₀
  obtain ⟨_, hfastSucc⟩ := hfast (N + 1) (by omega)
  have hfastMin :
      (N : ℝ) ≤ B * (5 : ℝ) ^ min (iteratedLogarithmicCayleySchedule N - 24)
        (iteratedLogarithmicCayleySchedule (N + 1) - 24) := by
    rcases le_total (iteratedLogarithmicCayleySchedule N - 24)
      (iteratedLogarithmicCayleySchedule (N + 1) - 24) with hle | hle
    · simpa [min_eq_left hle] using hfastN
    · have hcast : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.le_succ N
      simpa [min_eq_right hle] using hcast.trans hfastSucc
  have hscaleMin :
      (5 : ℝ) ^ min (iteratedLogarithmicCayleySchedule N - 24)
        (iteratedLogarithmicCayleySchedule (N + 1) - 24) ≤
        (N : ℝ) ^ (6 / 11 : ℝ) := hscaleN
  have hfastPower : (N : ℝ) ≤ B * (N : ℝ) ^ (6 / 11 : ℝ) :=
    hfastMin.trans (mul_le_mul_of_nonneg_left hscaleMin hB)
  have hdomSimple : 2 * B * (N : ℝ) ^ (6 / 11 : ℝ) ≤ (N : ℝ) := by
    simpa using hdomN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hdouble : 2 * (N : ℝ) ≤ (N : ℝ) := by
    calc
      2 * (N : ℝ) ≤ 2 * (B * (N : ℝ) ^ (6 / 11 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfastPower (by norm_num)
      _ = 2 * B * (N : ℝ) ^ (6 / 11 : ℝ) := by ring
      _ ≤ (N : ℝ) := hdomSimple
  have h21 : (2 : ℝ) ≤ 1 :=
    (mul_le_mul_iff_of_pos_right hNpos).mp (by simpa using hdouble)
  norm_num at h21

/-- Concrete surviving criterion: bounded iterated-log Cesàro transport gives rung one. -/
theorem rhLadder_one_of_iteratedLogarithmicCesaroSchedule_locallyBounded
    (hloc : PoleClearedFirstTraceCesaroScheduledLocallyBounded
      iteratedLogarithmicCayleySchedule) :
    RHLadder 1 :=
  rhLadder_one_of_poleClearedFirstTraceCesaroScheduledLocallyBounded
    tendsto_iteratedLogarithmicCayleySchedule_atTop hloc

end

end RHTower
