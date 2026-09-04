import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicProductCostBounds
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicTruncatedLadderError

/-!
# Final-shell harmonic product schedule

This file discharges, uniformly over every literal final-range ladder step, the endpoint and
positivity conditions needed by the explicit one-block harmonic product estimate.  The resulting
eventual theorem is closed: no asymptotic side condition remains as an external hypothesis.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Eventually every literal final-range ladder step satisfies all arithmetic conditions required
by the explicit harmonic product-cost bound. -/
theorem eventually_menonFinalRangeProductCost_conditions :
    ∀ᶠ x : ℝ in atTop,
      Real.exp 1 ≤ x ∧
      0 < menonFinalRangeLadderBase x ∧
      0 ≤ menonFinalRangeLadderEta x ∧
      menonFinalRangeLadderEta x ≤ 1 ∧
      ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        1 ≤ menonFinalRangeLadderBase x *
            (1 + menonFinalRangeLadderEta x) ^ j ∧
        menonFinalRangeLadderBase x *
            (1 + menonFinalRangeLadderEta x) ^ j ≤ 3 * x ∧
        1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) /
          (menonFinalRangeLadderBase x *
            (1 + menonFinalRangeLadderEta x) ^ j)⌋₊ := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
    eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangeLadder_cofactor_endpoints,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten] with x hx hbasic hend hetaBound
  rcases hbasic with ⟨hxone, _hH, hbase, _htop, heta, _hsteps⟩
  have heta1 : menonFinalRangeLadderEta x ≤ 1 := by linarith [hetaBound.2.2]
  refine ⟨hx, zero_lt_one.trans hbase, heta, heta1, ?_⟩
  intro j hj
  let q : ℝ := menonFinalRangeLadderBase x *
    (1 + menonFinalRangeLadderEta x) ^ j
  have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    have hp : 1 ≤ (1 + menonFinalRangeLadderEta x) ^ j := one_le_pow₀ hstep
    nlinarith
  have hq0 : 0 < q := zero_lt_one.trans_le hqOne
  have hN := (hend j hj).2
  have hfloor : ((⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ : ℕ) : ℝ) ≤
      (menonFinalRangeTopNat x : ℝ) / q := Nat.floor_le (by positivity)
  have honeFloor : (1 : ℝ) ≤
      ((⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hqTopNat : q ≤ (menonFinalRangeTopNat x : ℝ) := by
    have honeDiv : (1 : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) / q :=
      honeFloor.trans hfloor
    rw [le_div_iff₀ hq0, one_mul] at honeDiv
    exact honeDiv
  have htopThree : (menonFinalRangeTopNat x : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  exact ⟨by simpa only [q] using hqOne,
    by simpa only [q] using hqTopNat.trans htopThree,
    by simpa only [q] using hN⟩

/-- Menon's literal final-shell schedule satisfies the complete explicit one-block product estimate,
uniformly in the designated prime set, amplitude, exposed volume, and ladder step. -/
theorem eventually_menonFinalShellProductCostVolume_le_explicit :
    ∀ᶠ x : ℝ in atTop, ∀ (P : Finset ℕ) (V volE : ℝ)
      (j : ℕ), j ∈ Finset.range (menonFinalRangeLadderSteps x) → 0 ≤ volE →
      menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) x V volE j ≤
        V ^ 2 * ((2 * Real.pi)⁻¹ *
          (24 * (6 +
            80000 * Real.sqrt x * Real.log x * (2 * Real.pi * volE) *
              (menonFinalRangeLadderBase x *
                (1 + menonFinalRangeLadderEta x) ^ j) / x +
            144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * x))))) := by
  filter_upwards [eventually_menonFinalRangeProductCost_conditions] with x hx
  intro P V volE j hj hvolE
  rcases hx with ⟨hx, hQ, heta, heta1, hsteps⟩
  rcases hsteps j hj with ⟨hQjOne, hQjTop, hN⟩
  exact menonFinalShellProductCostVolume_le_explicit
    hx hQ heta heta1 hvolE j hQjOne hQjTop hN

end

end RHTower.Sieve
