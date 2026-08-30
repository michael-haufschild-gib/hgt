import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalSqrtMeanSpectrum

/-!
# Natural Wold square energy and the three-quarter RH threshold

For the literal centered natural-cutoff Wold residual `R N`, define the global energy

`E(t) = ∑ N, N^(2t-1) |R N|²`.

The critical square-root persistence law recovers one quarter power from this Hilbert energy:
`E(t) < ∞` forces every pointwise residual rate below `t - 1/4`.  Hence energies at every
radius strictly below `3/4` force all strict half-power rates and therefore RH.

This closes T2's terminal-control and height-cofinal zero-width transfer burdens.  It does not
assert the remaining producer, namely finiteness of the cofinal literal-source energies.
-/

open Finset Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Global natural-cutoff square energy of the genuine centered Wold residual at radius `t`. -/
def WoldNatResidualSquareEnergy (t : ℝ) : Prop :=
  Summable (fun N : ℕ =>
    (N : ℝ) ^ (2 * t - 1) *
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ^ 2)

private theorem sqrt_nat_le_two_mul_sqrtWindow_card
    {N n : ℕ} (hn : n ∈ woldNatResidualSqrtWindow N) :
    Real.sqrt (n : ℝ) ≤ 2 * (woldNatResidualSqrtWindow N).card := by
  have hs : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
  have hnUpper : n ≤ 2 * N := by
    have hn' := Finset.mem_Icc.1 hn
    omega
  have hroot : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  have hnUpperR : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hnUpper
  have hrootR : (N : ℝ) <
      ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) := by
    exact_mod_cast hroot
  have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtBound : Real.sqrt (n : ℝ) ≤ 2 * ((Nat.sqrt N : ℝ) + 1) := by
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) + 2 * ((Nat.sqrt N : ℝ) + 1))]
  rw [woldNatResidualSqrtWindow_card]
  push_cast
  nlinarith

private theorem woldNatResidualSqrtWeightedMean_le_of_squareEnergy
    {t c : ℝ} (_hc0 : 0 < c) (hct : c < t - 1 / 4)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      woldNatResidualSqrtWeightedMean c N ≤ B := by
  let energy : ℕ → ℝ := fun n =>
    (n : ℝ) ^ (2 * t - 1) *
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2
  let Q : ℝ := ∑' n : ℕ, energy n
  have hEnergy' : Summable energy := hEnergy
  have hEnergyNonneg : ∀ n, 0 ≤ energy n := by
    intro n
    dsimp only [energy]
    positivity
  have hQNonneg : 0 ≤ Q := by
    dsimp only [Q]
    exact tsum_nonneg hEnergyNonneg
  let B : ℝ := Real.sqrt (2 * Q) + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop 4] with N hN
  let W : Finset ℕ := woldNatResidualSqrtWindow N
  let S : ℝ := ∑ n ∈ W,
    (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  let C : ℝ := W.card
  have hCpos : 0 < C := by
    dsimp only [C, W]
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  have hSnonneg : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun n _ => mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (abs_nonneg _)
  have hd : 2 * c - (2 * t - 1) < 1 / 2 := by linarith
  have hweight : ∀ n ∈ W,
      (n : ℝ) ^ (2 * c) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 ≤
        (2 * C) * energy n := by
    intro n hn
    have hnBounds : N - Nat.sqrt N ≤ n ∧ n ≤ N + Nat.sqrt N := by
      simpa only [W, woldNatResidualSqrtWindow] using Finset.mem_Icc.1 hn
    have hsHalf : Nat.sqrt N ≤ N / 2 := by
      have hs' := Nat.sqrt_le' N
      by_cases hsmall : Nat.sqrt N ≤ 1
      · omega
      · have htwo : 2 ≤ Nat.sqrt N := by omega
        have hmul : 2 * Nat.sqrt N ≤ (Nat.sqrt N) ^ 2 := by nlinarith
        omega
    have hnNatPos : 0 < n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNatPos
    have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast hnNatPos
    have hrpowD : (n : ℝ) ^ (2 * c - (2 * t - 1)) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hnbase hd.le
    have hsqrt := sqrt_nat_le_two_mul_sqrtWindow_card (by simpa only [W] using hn)
    have hrpowCard : (n : ℝ) ^ (2 * c - (2 * t - 1)) ≤ 2 * C := by
      exact hrpowD.trans (by simpa only [C, W] using hsqrt)
    have hsplit : (n : ℝ) ^ (2 * c) =
        (n : ℝ) ^ (2 * t - 1) *
          (n : ℝ) ^ (2 * c - (2 * t - 1)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    rw [hsplit]
    dsimp only [energy]
    have hmul := mul_le_mul_of_nonneg_left hrpowCard
      (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (2 * t - 1))
    have hmul' := mul_le_mul_of_nonneg_right hmul
      (sq_nonneg |xiHeatCassiniWoldNatResidualLogDiscrepancy n|)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
  have hWindowEnergy :
      (∑ n ∈ W, (n : ℝ) ^ (2 * c) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2) ≤
        (2 * C) * Q := by
    calc
      (∑ n ∈ W, (n : ℝ) ^ (2 * c) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2) ≤
          ∑ n ∈ W, (2 * C) * energy n := Finset.sum_le_sum hweight
      _ = (2 * C) * ∑ n ∈ W, energy n := by rw [Finset.mul_sum]
      _ ≤ (2 * C) * Q := by
        gcongr
        exact hEnergy'.sum_le_tsum W (fun n _ => hEnergyNonneg n)
  have hcsRaw : S ^ 2 ≤ C * ∑ n ∈ W,
      ((n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) ^ 2 := by
    dsimp only [S, C]
    exact sq_sum_le_card_mul_sum_sq
  have hcs : S ^ 2 ≤ C * ∑ n ∈ W,
      (n : ℝ) ^ (2 * c) *
        |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := by
    calc
      S ^ 2 ≤ C * ∑ n ∈ W,
          ((n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) ^ 2 := hcsRaw
      _ = C * ∑ n ∈ W, (n : ℝ) ^ (2 * c) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnBounds : N - Nat.sqrt N ≤ n ∧ n ≤ N + Nat.sqrt N := by
          simpa only [W, woldNatResidualSqrtWindow] using Finset.mem_Icc.1 hn
        have hsHalf : Nat.sqrt N ≤ N / 2 := by
          have hs' := Nat.sqrt_le' N
          by_cases hsmall : Nat.sqrt N ≤ 1
          · omega
          · have htwo : 2 ≤ Nat.sqrt N := by omega
            have hmul : 2 * Nat.sqrt N ≤ (Nat.sqrt N) ^ 2 := by nlinarith
            omega
        have hnNatPos : 0 < n := by omega
        have hnnonneg : (0 : ℝ) ≤ n := by positivity
        rw [mul_pow, sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hnnonneg]
        congr 2
        norm_num
        ring
  have hsq : S ^ 2 ≤ C ^ 2 * (2 * Q) := by
    calc
      S ^ 2 ≤ C * ∑ n ∈ W, (n : ℝ) ^ (2 * c) *
          |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ^ 2 := hcs
      _ ≤ C * ((2 * C) * Q) := mul_le_mul_of_nonneg_left hWindowEnergy hCpos.le
      _ = C ^ 2 * (2 * Q) := by ring
  have hrootSq : Real.sqrt (2 * Q) ^ 2 = 2 * Q :=
    Real.sq_sqrt (by positivity)
  have htargetSq : (C * Real.sqrt (2 * Q)) ^ 2 = C ^ 2 * (2 * Q) := by
    rw [mul_pow, hrootSq]
  have htargetNonneg : 0 ≤ C * Real.sqrt (2 * Q) := by positivity
  have hlinear : S ≤ C * Real.sqrt (2 * Q) := by
    nlinarith [sq_nonneg (S + C * Real.sqrt (2 * Q))]
  rw [woldNatResidualSqrtWeightedMean]
  change S / C ≤ B
  calc
    S / C ≤ Real.sqrt (2 * Q) :=
      (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hlinear)
    _ ≤ B := by dsimp only [B]; linarith

/-- One natural square-energy radius controls the exact complementary Wold mean width. -/
theorem woldNatResidualSqrtMeanSpectrum_of_squareEnergy
    {t : ℝ} (_htQuarter : 1 / 4 < t) (_htThreeQuarter : t ≤ 3 / 4)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    WoldNatResidualSqrtMeanSpectrum (3 / 4 - t) := by
  intro c hc0 hcFrontier
  apply woldNatResidualSqrtWeightedMean_le_of_squareEnergy hc0 (by linarith) hEnergy

/-- One natural square-energy radius controls the exact complementary pointwise Wold width. -/
theorem woldNatResidualPowerSpectrum_of_squareEnergy
    {t : ℝ} (htQuarter : 1 / 4 < t) (htThreeQuarter : t ≤ 3 / 4)
    (hEnergy : WoldNatResidualSquareEnergy t) :
    WoldNatResidualPowerSpectrum (3 / 4 - t) := by
  apply woldNatResidualPowerSpectrum_of_sqrtMeanSpectrum (by linarith)
  exact woldNatResidualSqrtMeanSpectrum_of_squareEnergy htQuarter htThreeQuarter hEnergy

/-- Cofinal natural square energies below the three-quarter radius discharge the complete T2
terminal-control and zero-width transfer burden. -/
theorem riemannHypothesis_of_woldNatResidualSquareEnergy_cofinal_threeQuarter
    (hEnergy : ∀ t : ℝ, 1 / 4 < t → t < 3 / 4 →
      WoldNatResidualSquareEnergy t) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_woldNatResidualPowerSpectrum_zero.2
  intro c hc0 hcHalf
  let t : ℝ := (c + 1) / 2
  have htQuarter : 1 / 4 < t := by dsimp only [t]; linarith
  have htThreeQuarter : t < 3 / 4 := by dsimp only [t]; linarith
  have hSpectrum := woldNatResidualPowerSpectrum_of_squareEnergy
    htQuarter htThreeQuarter.le (hEnergy t htQuarter htThreeQuarter)
  exact hSpectrum c hc0 (by dsimp only [t]; linarith)

end

end RHTower
