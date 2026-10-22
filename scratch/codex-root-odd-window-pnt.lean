import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileOddWindowMismatchMass
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

namespace RHTower

/-- PNT prime supply on the same literal canonical odd-log windows as the
completed-source mismatch law. -/
theorem eventually_ccmOddLogWindow_primeCount_ge_pnt :
    ∀ᶠ t : ℕ in Filter.atTop,
      (Real.exp (1 / 4 : ℝ) - 1) / 2 *
          (Real.exp ((2 * t + 1 : ℕ) : ℝ) /
            Real.log (Real.exp ((2 * t + 1 : ℕ) : ℝ))) ≤
        (((Finset.Icc (ccmOddLogWindowLower t)
          (ccmOddLogWindowUpper t)).filter Nat.Prime).card : ℝ) := by
  let K : ℝ := Real.exp (1 / 4 : ℝ)
  have hK : 1 < K := by
    dsimp [K]
    exact Real.one_lt_exp_iff.mpr (by norm_num)
  have hlin : Filter.Tendsto
      (fun t : ℕ => ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono
      (fun t : ℕ => by exact_mod_cast (show t ≤ 2 * t + 1 by omega))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxTop : Filter.Tendsto
      (fun t : ℕ => Real.exp ((2 * t + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hlin
  have hpnt := hxTop.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hK)
  filter_upwards [hpnt, hxTop.eventually_ge_atTop (1 / (K - 1))]
    with t hpnt hlarge
  let x : ℝ := Real.exp ((2 * t + 1 : ℕ) : ℝ)
  let A : ℕ := ccmOddLogWindowLower t
  let B : ℕ := ccmOddLogWindowUpper t
  have hx0 : 0 < x := Real.exp_pos _
  have hAreal : (A : ℝ) ≤ x + 1 := by
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    change ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ x + 1
    push_cast
    linarith
  have hgap : x + 1 ≤ K * x := by
    have hKdiff : 0 < K - 1 := by linarith
    have hlarge' : 1 / (K - 1) ≤ x := hlarge
    have hh : (1 : ℝ) ≤ x * (K - 1) :=
      (div_le_iff₀ hKdiff).mp hlarge'
    nlinarith
  have hAB : A ≤ B := by
    dsimp only [B, ccmOddLogWindowUpper]
    apply Nat.le_floor
    rw [Real.exp_add]
    simpa only [x, K, mul_comm] using hAreal.trans hgap
  have hBfloor : B = ⌊K * x⌋₊ := by
    change ⌊Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4)⌋₊ =
      ⌊Real.exp (1 / 4 : ℝ) * Real.exp ((2 * t + 1 : ℕ) : ℝ)⌋₊
    rw [Real.exp_add, mul_comm]
  have hcard :
      ((Finset.Icc A B).filter Nat.Prime).card =
        (GaloisForLFunctions.HTGeometry.primesInIoc ⌊x⌋₊ B).card := by
    change ((Finset.Icc (⌊x⌋₊ + 1) B).filter Nat.Prime).card =
      ((Finset.Ioc ⌊x⌋₊ B).filter Nat.Prime).card
    rw [Finset.Icc_add_one_left_eq_Ioc]
  have hfloorB : ⌊x⌋₊ ≤ B := by
    change ⌊x⌋₊ + 1 ≤ B at hAB
    omega
  have hcount := GaloisForLFunctions.HTGeometry.card_primesInIoc hfloorB
  change (K - 1) / 2 * (x / Real.log x) ≤ _
  rw [hcard, hcount, hBfloor]
  exact hpnt

end RHTower
