/-
Closed form for the van der Corput tower, and its scale-by-scale optimality.

Iterating the `A`-process from `B(0,1) = (1/2, 1/2)` produces the classical tower

    (1/6, 2/3) , (1/14, 11/14) , (1/30, 13/15) , (1/62, 57/62) , …

whose entries have the closed form, with `N_k = 2^(k+2) - 2`,

    **κ_k = 1/N_k** ,   **λ_k = 1 - (k+1)/N_k** ,

so that

    **μ_k = 1/4 - k/(2 N_k)**   (increasing to the convexity bound `1/4`),
    **threshold_k = 1/(k+2)**   (decreasing to `0`),
    **displacement_k = 1/2 - (k+2)/N_k** .

The deficit of the `k`-th entry at block scale `c` is `κ_k + (λ_k - κ_k - 1/2)·c`, and consecutive
entries exchange optimality at

    **c_k = 2^(k+2) / ((k+1)·2^(k+2) + 2)** ,

which for `k = 1, 2, 3` is `4/9`, `8/25`, `16/65`, decreasing like `1/(k+1)`.  The first of these,
`4/9`, is exactly the `A`-productivity threshold of Weyl's pair computed earlier — the two
calculations agree.

The tower therefore trades in one direction only: it drives the deficit to zero at small scales while
its subconvexity exponents climb from `1/6` to `1/4`, reaching the *trivial* value exactly in the
limit.  At the critical scale the best member is the first one, Weyl's.
-/
import GaloisForLFunctions.HTGeometry.TowerCoversAllScales

namespace HTGeometry

/-! ### Closed forms -/

/-- The denominator `2^(k+2) - 2` of the tower's entries. -/
def towerDen (k : ℕ) : ℚ := 2 ^ (k + 2) - 2

/-- First coordinate of the `k`-th tower entry. -/
def towerKappa (k : ℕ) : ℚ := 1 / towerDen k

/-- Second coordinate. -/
def towerLambda (k : ℕ) : ℚ := 1 - (k + 1) / towerDen k

/-- Its subconvexity exponent. -/
def towerMu (k : ℕ) : ℚ := 1 / 4 - k / (2 * towerDen k)

/-- Its nontriviality threshold at the block scales. -/
def towerThr (k : ℕ) : ℚ := 1 / (k + 2)

/-- The denominators at the first four levels. -/
theorem towerDen_values :
    towerDen 1 = 6 ∧ towerDen 2 = 14 ∧ towerDen 3 = 30 ∧ towerDen 4 = 62 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold towerDen; norm_num)

/-- **The first four entries are the classical tower.** -/
theorem tower_entries :
    (towerKappa 1, towerLambda 1) = ((1 : ℚ) / 6, (2 : ℚ) / 3) ∧
      (towerKappa 2, towerLambda 2) = ((1 : ℚ) / 14, (11 : ℚ) / 14) ∧
      (towerKappa 3, towerLambda 3) = ((1 : ℚ) / 30, (13 : ℚ) / 15) ∧
      (towerKappa 4, towerLambda 4) = ((1 : ℚ) / 62, (57 : ℚ) / 62) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold towerKappa towerLambda towerDen; norm_num)

/-- **The closed form for the subconvexity exponents.** -/
theorem towerMu_values :
    towerMu 1 = 1 / 6 ∧ towerMu 2 = 5 / 28 ∧ towerMu 3 = 1 / 5 ∧ towerMu 4 = 27 / 124 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold towerMu towerDen; norm_num)

/-- **They agree with the exponent-pair formula.** -/
theorem towerMu_eq_epMu (k : ℕ) : towerMu k = epMu (towerKappa k) (towerLambda k) := by
  unfold towerMu epMu towerKappa towerLambda
  have h : towerDen k ≠ 0 := by
    unfold towerDen
    have : (2 : ℚ) ^ (k + 2) ≥ 4 := by
      calc (2 : ℚ) ^ (k + 2) ≥ 2 ^ 2 := by
            apply pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4 := by norm_num
    intro hc; linarith
  field_simp
  ring

/-- **The exponents increase toward the convexity bound.** -/
theorem towerMu_increasing :
    towerMu 1 < towerMu 2 ∧ towerMu 2 < towerMu 3 ∧ towerMu 3 < towerMu 4 ∧
      towerMu 4 < 1 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := towerMu_values
  rw [h1, h2, h3, h4]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The thresholds decrease to zero.** -/
theorem towerThr_values :
    towerThr 1 = 1 / 3 ∧ towerThr 2 = 1 / 4 ∧ towerThr 3 = 1 / 5 ∧ towerThr 4 = 1 / 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold towerThr; norm_num)

/-- And they agree with the threshold computed from the pair. -/
theorem towerThr_eq_towerThreshold :
    towerThr 1 = towerThreshold (towerKappa 1) (towerLambda 1) ∧
      towerThr 2 = towerThreshold (towerKappa 2) (towerLambda 2) ∧
      towerThr 3 = towerThreshold (towerKappa 3) (towerLambda 3) ∧
      towerThr 4 = towerThreshold (towerKappa 4) (towerLambda 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold towerThr towerThreshold towerKappa towerLambda towerDen; norm_num)

/-! ### Where consecutive entries exchange optimality -/

/-- The scale at which the `k`-th and `(k+1)`-st entries have equal deficit. -/
def towerSwitch (k : ℕ) : ℚ := 2 ^ (k + 2) / ((k + 1) * 2 ^ (k + 2) + 2)

/-- **The first three switching scales.** -/
theorem towerSwitch_values :
    towerSwitch 1 = 4 / 9 ∧ towerSwitch 2 = 8 / 25 ∧ towerSwitch 3 = 16 / 65 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold towerSwitch; norm_num)

/-- **They decrease.** -/
theorem towerSwitch_decreasing :
    towerSwitch 3 < towerSwitch 2 ∧ towerSwitch 2 < towerSwitch 1 := by
  obtain ⟨h1, h2, h3⟩ := towerSwitch_values
  rw [h1, h2, h3]
  constructor <;> norm_num

/-- **The first switching scale is Weyl's `A`-productivity threshold**, computed independently
earlier. -/
theorem towerSwitch_one_is_weyl_threshold :
    towerSwitch 1 = aProductivityThreshold weylKappa := by
  rw [aThreshold_weyl]
  unfold towerSwitch; norm_num

/-- **At the switching scale the two entries have equal deficit.** -/
theorem deficits_equal_at_switch :
    scaleDeficit (towerKappa 1) (towerLambda 1) (towerSwitch 1)
      = scaleDeficit (towerKappa 2) (towerLambda 2) (towerSwitch 1) := by
  obtain ⟨h1, h2, -, -⟩ := tower_entries
  have e1 : towerKappa 1 = 1 / 6 := congrArg Prod.fst h1
  have e2 : towerLambda 1 = 2 / 3 := congrArg Prod.snd h1
  have e3 : towerKappa 2 = 1 / 14 := congrArg Prod.fst h2
  have e4 : towerLambda 2 = 11 / 14 := congrArg Prod.snd h2
  rw [e1, e2, e3, e4, towerSwitch_values.1]
  unfold scaleDeficit; norm_num

/-! ### The trade -/

/-- **At the critical scale the best tower member is the first.** -/
theorem weyl_best_at_critical :
    scaleDeficit (towerKappa 1) (towerLambda 1) (1 / 2)
      < scaleDeficit (towerKappa 2) (towerLambda 2) (1 / 2) := by
  rw [scaleDeficit_at_critical, scaleDeficit_at_critical, ← towerMu_eq_epMu, ← towerMu_eq_epMu]
  exact towerMu_increasing.1

/-- **At scale zero the best is the last**, and the deficits descend to zero. -/
theorem later_best_at_zero :
    scaleDeficit (towerKappa 4) (towerLambda 4) 0
      < scaleDeficit (towerKappa 1) (towerLambda 1) 0 := by
  simp only [scaleDeficit_at_zero]
  unfold towerKappa towerDen; norm_num

/-- **The tower's trade, stated.**  It drives the deficit to zero at small scales while its
subconvexity exponents climb from `1/6` toward the trivial value `1/4`. -/
theorem tower_trade :
    towerMu 1 = 1 / 6 ∧ towerMu 4 = 27 / 124 ∧ towerMu 1 < towerMu 4 ∧
      towerKappa 4 < towerKappa 1 := by
  obtain ⟨h1, -, -, h4⟩ := towerMu_values
  refine ⟨h1, h4, ?_, ?_⟩
  · rw [h1, h4]; norm_num
  · unfold towerKappa towerDen; norm_num

end HTGeometry
