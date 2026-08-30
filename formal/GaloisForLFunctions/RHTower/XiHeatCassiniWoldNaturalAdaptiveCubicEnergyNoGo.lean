import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldCriticalResidualDivisorCarrier
import GaloisForLFunctions.RHTower.Sieve.CardLengthGap

/-!
# Adaptive cubic Wold energy transfer and the supercritical no-go

For the literal centered natural-cutoff Wold residual, logarithmic persistence and weighted
square energy balance on the adaptive radius

`H_N = ceil(N^(1 - 2t/3))`.

This gives the endpoint pointwise rate `N^(-2t/3)`, with no epsilon loss.  Prime-clock
transport and the unconditional half-density obstruction then exclude every square-energy
radius `t > 3/4`.  Thus the apparent fixed-window quarter-power loss is not intrinsic:
the source-specific interpolation law is cubic.
-/

open Finset Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

private def woldNatResidualAdaptiveCubicExponent (t : ℝ) : ℝ := 1 - 2 * t / 3

private def woldNatResidualAdaptiveCubicRadius (t : ℝ) (N : ℕ) : ℕ :=
  ⌈(N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t⌉₊

private theorem eventually_woldNatResidualAdaptiveCubicRadius_bounds {t : ℝ}
    (htHalf : 1 / 2 < t) (htThreeHalves : t < 3 / 2) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ woldNatResidualAdaptiveCubicRadius t N ∧
      woldNatResidualAdaptiveCubicRadius t N ≤ N / 2 := by
  have ha0 : 0 < woldNatResidualAdaptiveCubicExponent t := by
    unfold woldNatResidualAdaptiveCubicExponent
    linarith
  have ha1 : woldNatResidualAdaptiveCubicExponent t < 1 := by
    unfold woldNatResidualAdaptiveCubicExponent
    linarith
  let b : ℝ := (woldNatResidualAdaptiveCubicExponent t + 1) / 2
  have hab : woldNatResidualAdaptiveCubicExponent t < b := by
    dsimp only [b]
    linarith
  have hb1 : b < 1 := by
    dsimp only [b]
    linarith
  have hABreal := Sieve.eventually_rpow_le_half hab
  have hB1real := Sieve.eventually_rpow_le_half hb1
  have hAB := tendsto_natCast_atTop_atTop.eventually hABreal
  have hB1 := tendsto_natCast_atTop_atTop.eventually hB1real
  filter_upwards [hAB, hB1, eventually_ge_atTop 8] with N hABN hB1N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpowPos : 0 < (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t :=
    Real.rpow_pos_of_pos hNpos _
  have hpowBNonneg : 0 ≤ (N : ℝ) ^ b := Real.rpow_nonneg (by positivity) _
  have hpowQuarter :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (1 / 4 : ℝ) * N := by
    have hNpowOne : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := by simp
    rw [hNpowOne] at hB1N
    nlinarith
  have hdivNat : N ≤ 2 * (N / 2) + 1 := by omega
  have hdivReal : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hdivNat
  have hNReal : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hpowHalf : (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ ((N / 2 : ℕ) : ℝ) := by
    calc
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (1 / 4 : ℝ) * N := hpowQuarter
      _ ≤ ((N : ℝ) - 1) / 2 := by norm_num; linarith
      _ ≤ ((N / 2 : ℕ) : ℝ) := by linarith
  constructor
  · exact Nat.one_le_ceil_iff.mpr hpowPos
  · exact Nat.ceil_le.mpr hpowHalf

private theorem woldNatResidual_right_adaptive_persistence {N H n : ℕ}
    (hN : 1 ≤ N) (hnLeft : N ≤ n) (hnRight : n ≤ N + H) :
    xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
        (H : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := hNpos.trans_le (by exact_mod_cast hnLeft)
  have hp := woldNatResidual_log_persistence hnLeft
  have hlog : Real.log (n : ℝ) - Real.log (N : ℝ) ≤ (H : ℝ) / N := by
    calc
      Real.log (n : ℝ) - Real.log (N : ℝ) =
          Real.log ((n : ℝ) / (N : ℝ)) := by
        rw [Real.log_div hnpos.ne' hNpos.ne']
      _ ≤ (n : ℝ) / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hnpos hNpos)
      _ = ((n : ℝ) - (N : ℝ)) / (N : ℝ) := by field_simp
      _ ≤ (H : ℝ) / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ hNpos.le
        rw [← Nat.cast_sub hnLeft]
        exact_mod_cast (by omega : n - N ≤ H)
  linarith [le_abs_self (xiHeatCassiniWoldNatResidualLogDiscrepancy n)]

private theorem woldNatResidual_left_adaptive_persistence {N H n : ℕ}
    (hN : 1 ≤ N) (hHalf : H ≤ N / 2)
    (hnLeft : N - H ≤ n) (hnRight : n ≤ N) :
    -xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
        2 * (H : ℝ) / N := by
  have hnNat : N / 2 ≤ n := by omega
  have hnPosNat : 0 < n := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hp := woldNatResidual_log_persistence hnRight
  have hNle2n : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : N ≤ 2 * n)
  have hsub : (N : ℝ) - (n : ℝ) ≤ (H : ℝ) := by
    rw [← Nat.cast_sub hnRight]
    exact_mod_cast (by omega : N - n ≤ H)
  have hlog : Real.log (N : ℝ) - Real.log (n : ℝ) ≤ 2 * (H : ℝ) / N := by
    calc
      Real.log (N : ℝ) - Real.log (n : ℝ) =
          Real.log ((N : ℝ) / (n : ℝ)) := by
        rw [Real.log_div hNpos.ne' hnpos.ne']
      _ ≤ (N : ℝ) / (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hNpos hnpos)
      _ = ((N : ℝ) - (n : ℝ)) / (n : ℝ) := by field_simp
      _ ≤ (H : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsub hnpos.le
      _ ≤ 2 * (H : ℝ) / (N : ℝ) := by
        rw [div_le_div_iff₀ hnpos hNpos]
        have hH : (0 : ℝ) ≤ H := by positivity
        nlinarith
  linarith [neg_le_abs (xiHeatCassiniWoldNatResidualLogDiscrepancy n)]

private theorem woldNatResidualAdaptiveWindow_mean_abs_le
    {t : ℝ} (htHalf : 1 / 2 < t)
    (hEnergy : WoldNatResidualSquareEnergy t)
    {N : ℕ} (hN : 1 ≤ N) {W : Finset ℕ}
    (hWnonempty : W.Nonempty)
    (hIndex : ∀ n ∈ W, N ≤ 2 * n)
    (hCardPow :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (W.card : ℝ)) :
    (∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) /
        (W.card : ℝ) ≤
      Real.sqrt ((2 : ℝ) ^ (2 * t - 1) *
        ∑' n : ℕ, (n : ℝ) ^ (2 * t - 1) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2) *
        (N : ℝ) ^ (-(2 * t / 3)) := by
  let energy : ℕ → ℝ := fun n =>
    (n : ℝ) ^ (2 * t - 1) *
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2
  let Q : ℝ := ∑' n : ℕ, energy n
  let K : ℝ := (2 : ℝ) ^ (2 * t - 1) * Q
  let S : ℝ := ∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  let C : ℝ := W.card
  let r : ℝ := 2 * t / 3
  have hEnergy' : Summable energy := hEnergy
  have hEnergyNonneg : ∀ n, 0 ≤ energy n := by
    intro n
    dsimp only [energy]
    positivity
  have hQNonneg : 0 ≤ Q := by
    dsimp only [Q]
    exact tsum_nonneg hEnergyNonneg
  have hKNonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hSNonneg : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCpos : 0 < C := by
    dsimp only [C]
    exact_mod_cast hWnonempty.card_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < 2 * t - 1 := by linarith
  have hrpos : 0 < r := by
    dsimp only [r]
    linarith
  have hterm : ∀ n ∈ W,
      (N : ℝ) ^ (2 * t - 1) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 ≤
        (2 : ℝ) ^ (2 * t - 1) * energy n := by
    intro n hn
    have hnposNat : 0 < n := by
      have := hIndex n hn
      omega
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    have hN2n : (N : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hIndex n hn
    have hp := Real.rpow_le_rpow (by positivity) hN2n hqpos.le
    have hmulPow :
        (2 * (n : ℝ)) ^ (2 * t - 1) =
          (2 : ℝ) ^ (2 * t - 1) * (n : ℝ) ^ (2 * t - 1) := by
      rw [Real.mul_rpow (by positivity) hnnonneg]
    rw [hmulPow] at hp
    have hsquare :
        0 ≤ |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right hp hsquare
    simpa only [energy, mul_assoc] using this
  have hWeightedEnergy :
      (N : ℝ) ^ (2 * t - 1) *
          ∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 ≤
        K := by
    calc
      (N : ℝ) ^ (2 * t - 1) *
          ∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 =
          ∑ n ∈ W, (N : ℝ) ^ (2 * t - 1) *
            |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := by
              rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ W, (2 : ℝ) ^ (2 * t - 1) * energy n :=
        Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ (2 * t - 1) * ∑ n ∈ W, energy n := by
        rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (2 * t - 1) * Q := by
        gcongr
        exact hEnergy'.sum_le_tsum W (fun n _ => hEnergyNonneg n)
      _ = K := by rfl
  have hcs : S ^ 2 ≤ C *
      ∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := by
    dsimp only [S, C]
    exact sq_sum_le_card_mul_sum_sq
  have hBase :
      (N : ℝ) ^ (2 * t - 1) * S ^ 2 ≤ C * K := by
    calc
      (N : ℝ) ^ (2 * t - 1) * S ^ 2 ≤
          (N : ℝ) ^ (2 * t - 1) *
            (C * ∑ n ∈ W,
              |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (Real.rpow_nonneg (by positivity) _)
      _ = C * ((N : ℝ) ^ (2 * t - 1) *
          ∑ n ∈ W, |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2) := by ring
      _ ≤ C * K := mul_le_mul_of_nonneg_left hWeightedEnergy hCpos.le
  have hApos : 0 < (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t :=
    Real.rpow_pos_of_pos hNpos _
  have hScaledRaw :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t *
          ((N : ℝ) ^ (2 * t - 1) * S ^ 2) ≤ C ^ 2 * K := by
    calc
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t *
          ((N : ℝ) ^ (2 * t - 1) * S ^ 2) ≤
          (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t * (C * K) :=
        mul_le_mul_of_nonneg_left hBase hApos.le
      _ ≤ C * (C * K) := by
        gcongr
      _ = C ^ 2 * K := by ring
  have hExponent : woldNatResidualAdaptiveCubicExponent t + (2 * t - 1) = 2 * r := by
    dsimp only [woldNatResidualAdaptiveCubicExponent, r]
    ring
  have hScaled :
      (N : ℝ) ^ (2 * r) * S ^ 2 ≤ C ^ 2 * K := by
    calc
      (N : ℝ) ^ (2 * r) * S ^ 2 =
          ((N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t *
            (N : ℝ) ^ (2 * t - 1)) * S ^ 2 := by
              rw [← Real.rpow_add hNpos, hExponent]
      _ = (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t *
          ((N : ℝ) ^ (2 * t - 1) * S ^ 2) := by ring
      _ ≤ C ^ 2 * K := hScaledRaw
  have hInvNonneg : 0 ≤ (N : ℝ) ^ (-(2 * r)) :=
    Real.rpow_nonneg (by positivity) _
  have hScaledInv := mul_le_mul_of_nonneg_left hScaled hInvNonneg
  have hcancel :
      (N : ℝ) ^ (-(2 * r)) * (N : ℝ) ^ (2 * r) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hSqPower :
      ((N : ℝ) ^ (-r)) ^ 2 = (N : ℝ) ^ (-(2 * r)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    congr 1
    ring
  have hRootSq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKNonneg
  have hSq :
      S ^ 2 ≤ (C * Real.sqrt K * (N : ℝ) ^ (-r)) ^ 2 := by
    calc
      S ^ 2 = (N : ℝ) ^ (-(2 * r)) *
          ((N : ℝ) ^ (2 * r) * S ^ 2) := by
            calc
              S ^ 2 = 1 * S ^ 2 := by ring
              _ = ((N : ℝ) ^ (-(2 * r)) * (N : ℝ) ^ (2 * r)) * S ^ 2 := by
                rw [hcancel]
              _ = _ := by ring
      _ ≤ (N : ℝ) ^ (-(2 * r)) * (C ^ 2 * K) := hScaledInv
      _ = (C * Real.sqrt K * (N : ℝ) ^ (-r)) ^ 2 := by
        rw [mul_pow, mul_pow, hRootSq, hSqPower]
        ring
  have hTargetNonneg :
      0 ≤ C * Real.sqrt K * (N : ℝ) ^ (-r) := by positivity
  have hLinear : S ≤ C * Real.sqrt K * (N : ℝ) ^ (-r) := by
    nlinarith [sq_nonneg (S + C * Real.sqrt K * (N : ℝ) ^ (-r))]
  change S / C ≤ Real.sqrt K * (N : ℝ) ^ (-r)
  exact (div_le_iff₀ hCpos).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hLinear)

/-- **Adaptive cubic persistence transfer.**  Square energy at radius `t` controls the exact
endpoint natural Wold rate `2t/3`; the averaging loss and logarithmic drift have been balanced
by the forced window radius `N^(1-2t/3)`. -/
theorem exists_woldNatResidual_power_rate_twoThirds_of_squareEnergy
    {t : ℝ} (htHalf : 1 / 2 < t) (htThreeHalves : t < 3 / 2)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(2 * t / 3)) := by
  let energy : ℕ → ℝ := fun n =>
    (n : ℝ) ^ (2 * t - 1) *
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2
  let Q : ℝ := ∑' n : ℕ, energy n
  let A : ℝ := Real.sqrt ((2 : ℝ) ^ (2 * t - 1) * Q)
  let B : ℝ := A + 4
  have hEnergy' : Summable energy := hEnergy
  have hEnergyNonneg : ∀ n, 0 ≤ energy n := by
    intro n
    dsimp only [energy]
    positivity
  have hQNonneg : 0 ≤ Q := by
    dsimp only [Q]
    exact tsum_nonneg hEnergyNonneg
  have hANonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [eventually_woldNatResidualAdaptiveCubicRadius_bounds htHalf htThreeHalves,
    eventually_ge_atTop 8] with N hRadius hN
  let H : ℕ := woldNatResidualAdaptiveCubicRadius t N
  let U : Finset ℕ := Finset.Icc N (N + H)
  let L : Finset ℕ := Finset.Icc (N - H) N
  let R : ℝ := xiHeatCassiniWoldNatResidualLogDiscrepancy N
  let C : ℝ := (H + 1 : ℕ)
  let SU : ℝ := ∑ n ∈ U, |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  let SL : ℝ := ∑ n ∈ L, |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  have hHpos : 1 ≤ H := by simpa only [H] using hRadius.1
  have hHalf : H ≤ N / 2 := by simpa only [H] using hRadius.2
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hcardU : U.card = H + 1 := by
    dsimp only [U]
    rw [Nat.card_Icc]
    omega
  have hcardL : L.card = H + 1 := by
    dsimp only [L]
    rw [Nat.card_Icc]
    omega
  have hUnonempty : U.Nonempty := by
    refine ⟨N, ?_⟩
    simp only [U, Finset.mem_Icc]
    omega
  have hLnonempty : L.Nonempty := by
    refine ⟨N, ?_⟩
    simp only [L, Finset.mem_Icc]
    omega
  have hIndexU : ∀ n ∈ U, N ≤ 2 * n := by
    intro n hn
    have hnBounds := Finset.mem_Icc.1 (by simpa only [U] using hn)
    omega
  have hIndexL : ∀ n ∈ L, N ≤ 2 * n := by
    intro n hn
    have hnBounds := Finset.mem_Icc.1 (by simpa only [L] using hn)
    omega
  have hPowRadius :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (H : ℝ) := by
    dsimp only [H, woldNatResidualAdaptiveCubicRadius]
    exact Nat.le_ceil _
  have hCardPowU :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (U.card : ℝ) := by
    rw [hcardU]
    push_cast
    linarith
  have hCardPowL :
      (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t ≤ (L.card : ℝ) := by
    rw [hcardL]
    push_cast
    linarith
  have hMeanU := woldNatResidualAdaptiveWindow_mean_abs_le htHalf hEnergy hN1
    hUnonempty hIndexU hCardPowU
  have hMeanL := woldNatResidualAdaptiveWindow_mean_abs_le htHalf hEnergy hN1
    hLnonempty hIndexL hCardPowL
  have hMeanU' :
      SU / C ≤ A * (N : ℝ) ^ (-(2 * t / 3)) := by
    simpa only [SU, C, hcardU, A, Q, energy] using hMeanU
  have hMeanL' :
      SL / C ≤ A * (N : ℝ) ^ (-(2 * t / 3)) := by
    simpa only [SL, C, hcardL, A, Q, energy] using hMeanL
  have ha0 : 0 < woldNatResidualAdaptiveCubicExponent t := by
    dsimp only [woldNatResidualAdaptiveCubicExponent]
    linarith
  have hpowOne :
      (1 : ℝ) ≤ (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t :=
    Real.one_le_rpow hNbase ha0.le
  have hceilNat :
      H ≤ ⌊(N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t⌋₊ + 1 := by
    dsimp only [H, woldNatResidualAdaptiveCubicRadius]
    exact Nat.ceil_le_floor_add_one _
  have hceilCast :
      (H : ℝ) ≤
        ((⌊(N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hceilNat
  have hfloorCast :
      ((⌊(N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t⌋₊ : ℕ) : ℝ) ≤
        (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hHCast :
      (H : ℝ) ≤ 2 * (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t := by
    linarith
  have hDrift :
      2 * (H : ℝ) / (N : ℝ) ≤
        4 * (N : ℝ) ^ (-(2 * t / 3)) := by
    calc
      2 * (H : ℝ) / (N : ℝ) ≤
          2 * (2 * (N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hHCast (by norm_num)) hNpos.le
      _ = 4 * ((N : ℝ) ^ woldNatResidualAdaptiveCubicExponent t / (N : ℝ) ^ (1 : ℝ)) := by
        simp only [Real.rpow_one]
        ring
      _ = 4 * (N : ℝ) ^ (woldNatResidualAdaptiveCubicExponent t - 1) := by
        rw [Real.rpow_sub hNpos]
      _ = 4 * (N : ℝ) ^ (-(2 * t / 3)) := by
        congr 2
        dsimp only [woldNatResidualAdaptiveCubicExponent]
        ring
  by_cases hR : 0 ≤ R
  · have hsum :
        ∑ _n ∈ U, R ≤
          ∑ n ∈ U, (|xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
            (H : ℝ) / N) := by
      apply Finset.sum_le_sum
      intro n hn
      exact woldNatResidual_right_adaptive_persistence hN1
        (Finset.mem_Icc.1 (by simpa only [U] using hn)).1
        (Finset.mem_Icc.1 (by simpa only [U] using hn)).2
    have hsum' : C * R ≤ SU + C * ((H : ℝ) / N) := by
      simpa only [C, SU, hcardU, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hsum
    have hpoint : R ≤ SU / C + (H : ℝ) / N := by
      have hsub : (R - (H : ℝ) / N) * C ≤ SU := by
        nlinarith
      have := (le_div_iff₀ hCpos).2 hsub
      linarith
    rw [abs_of_nonneg hR]
    calc
      R ≤ SU / C + (H : ℝ) / N := hpoint
      _ ≤ A * (N : ℝ) ^ (-(2 * t / 3)) +
          2 * (H : ℝ) / N := by
        have hHnonneg : (0 : ℝ) ≤ H := by positivity
        have hdivNonneg : 0 ≤ (H : ℝ) / N := div_nonneg hHnonneg hNpos.le
        apply add_le_add hMeanU'
        calc
          (H : ℝ) / N ≤ (H : ℝ) / N + (H : ℝ) / N :=
            le_add_of_nonneg_right hdivNonneg
          _ = 2 * (H : ℝ) / N := by ring
      _ ≤ A * (N : ℝ) ^ (-(2 * t / 3)) +
          4 * (N : ℝ) ^ (-(2 * t / 3)) := by
        exact add_le_add le_rfl hDrift
      _ = B * (N : ℝ) ^ (-(2 * t / 3)) := by
        dsimp only [B]
        ring
  · have hRneg : R < 0 := lt_of_not_ge hR
    have hsum :
        ∑ _n ∈ L, (-R) ≤
          ∑ n ∈ L, (|xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
            2 * (H : ℝ) / N) := by
      apply Finset.sum_le_sum
      intro n hn
      exact woldNatResidual_left_adaptive_persistence hN1 hHalf
        (Finset.mem_Icc.1 (by simpa only [L] using hn)).1
        (Finset.mem_Icc.1 (by simpa only [L] using hn)).2
    have hsum' : C * (-R) ≤ SL + C * (2 * (H : ℝ) / N) := by
      simpa only [C, SL, hcardL, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hsum
    have hpoint : -R ≤ SL / C + 2 * (H : ℝ) / N := by
      have hsub : (-R - 2 * (H : ℝ) / N) * C ≤ SL := by
        nlinarith
      have := (le_div_iff₀ hCpos).2 hsub
      linarith
    rw [abs_of_neg hRneg]
    calc
      -R ≤ SL / C + 2 * (H : ℝ) / N := hpoint
      _ ≤ A * (N : ℝ) ^ (-(2 * t / 3)) +
          2 * (H : ℝ) / N := add_le_add hMeanL' le_rfl
      _ ≤ A * (N : ℝ) ^ (-(2 * t / 3)) +
          4 * (N : ℝ) ^ (-(2 * t / 3)) := by
        exact add_le_add le_rfl hDrift
      _ = B * (N : ℝ) ^ (-(2 * t / 3)) := by
        dsimp only [B]
        ring

/-- Natural Wold square energy is downward closed in every positive-weight radius. -/
theorem woldNatResidualSquareEnergy_mono {u t : ℝ} (hu : 1 / 2 < u) (hut : u ≤ t)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    WoldNatResidualSquareEnergy u := by
  unfold WoldNatResidualSquareEnergy at hEnergy ⊢
  refine Summable.of_nonneg_of_le (f := fun N : ℕ =>
      (N : ℝ) ^ (2 * t - 1) *
        |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ^ 2)
    (g := fun N : ℕ =>
      (N : ℝ) ^ (2 * u - 1) *
        |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ^ 2) ?_ ?_ hEnergy
  · intro N
    positivity
  · intro N
    by_cases hN : N = 0
    · subst N
      simp [Real.zero_rpow (by linarith : 2 * u - 1 ≠ 0),
        Real.zero_rpow (by linarith : 2 * t - 1 ≠ 0)]
    · have hbase : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have hp : (N : ℝ) ^ (2 * u - 1) ≤ (N : ℝ) ^ (2 * t - 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

private theorem woldNatResidual_nthPrime_eq_ordered (N : ℕ) :
    xiHeatCassiniWoldNatResidualLogDiscrepancy (nthPrimeSubtype N) =
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy N := by
  simp only [xiHeatCassiniWoldNatResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
    xiMassNthPrimeLogHeight]

private theorem orderedWoldResidual_exp_height_rate_of_woldNatResidual_power_rate {c B : ℝ}
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤ B * (N : ℝ) ^ (-c)) :
    ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N) := by
  have h := nthPrimeSubtype_strictMono.tendsto_atTop.eventually hrate
  filter_upwards [h] with N hN
  have hp0 : (0 : ℝ) < nthPrimeSubtype N := nthPrimeSubtype_pos N
  rw [← woldNatResidual_nthPrime_eq_ordered]
  calc
    |xiHeatCassiniWoldNatResidualLogDiscrepancy (nthPrimeSubtype N)| ≤
        B * (nthPrimeSubtype N : ℝ) ^ (-c) := hN
    _ = B * Real.exp (-c * xiMassNthPrimeLogHeight N) := by
      rw [Real.rpow_def_of_pos hp0]
      unfold xiMassNthPrimeLogHeight
      congr 2
      ring

/-- **Closed supercritical T2 no-go.**  The genuine natural Wold residual has no weighted square
energy at any radius strictly above `3/4`: adaptive cubic transfer would force an ordered-prime
decay exponent strictly beyond the unconditional half-density wall. -/
theorem not_woldNatResidualSquareEnergy_of_threeQuarter_lt {t : ℝ} (ht : 3 / 4 < t) :
    ¬ WoldNatResidualSquareEnergy t := by
  intro hEnergy
  let u : ℝ := (3 / 4 + min t 1) / 2
  have hmin : 3 / 4 < min t 1 := lt_min ht (by norm_num)
  have huQuarter : 3 / 4 < u := by
    dsimp only [u]
    linarith
  have huOne : u < 1 := by
    have hminOne : min t 1 ≤ 1 := min_le_right _ _
    dsimp only [u]
    linarith
  have huHalf : 1 / 2 < u := by linarith
  have huThreeHalves : u < 3 / 2 := by linarith
  have hu_le_t : u ≤ t := by
    have hminT : min t 1 ≤ t := min_le_left _ _
    dsimp only [u]
    linarith
  have hEnergyU : WoldNatResidualSquareEnergy u :=
    woldNatResidualSquareEnergy_mono huHalf hu_le_t hEnergy
  obtain ⟨B, hB, hrate⟩ :=
    exists_woldNatResidual_power_rate_twoThirds_of_squareEnergy huHalf huThreeHalves hEnergyU
  have hOrdered := orderedWoldResidual_exp_height_rate_of_woldNatResidual_power_rate hrate
  exact
    not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt
      (c := 2 * u / 3) (B := B) (by linarith) hB.le hOrdered

end
end RHTower
