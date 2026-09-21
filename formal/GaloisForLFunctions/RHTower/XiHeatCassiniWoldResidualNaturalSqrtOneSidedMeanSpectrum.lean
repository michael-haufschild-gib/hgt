import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalSqrtMeanSpectrum

/-!
# Directed critical-window spectrum for natural Wold residual

The natural Wold residual is a monotone arithmetic mass minus a logarithm. Its positive spikes
persist only forward and its negative spikes only backward. This module proves that these two
directed, sign-separated square-root-window means are exactly equivalent to the natural Wold power
spectrum, hence to every zero-width bound and to RH at width zero. It is strictly weaker than the
prior symmetric absolute local-mean criterion and exposes the direction a source law must control.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def woldNatResidualSqrtRightPositiveMean (c : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc N (N + Nat.sqrt N),
      (n : ℝ) ^ c * max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) /
    (woldNatResidualSqrtWindow N).card

def woldNatResidualSqrtLeftNegativeMean (c : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (N - Nat.sqrt N) N,
      (n : ℝ) ^ c * max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) /
    (woldNatResidualSqrtWindow N).card

def WoldNatResidualSqrtOneSidedMeanSpectrum (alpha : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 2 - alpha →
    ∃ Bplus Bminus : ℝ, 0 < Bplus ∧ 0 < Bminus ∧ ∀ᶠ N : ℕ in atTop,
      woldNatResidualSqrtRightPositiveMean c N ≤ Bplus ∧
        woldNatResidualSqrtLeftNegativeMean c N ≤ Bminus

theorem woldNatResidualSqrtOneSidedMeanSpectrum_of_powerSpectrum
    {alpha : ℝ} (hPower : WoldNatResidualPowerSpectrum alpha) :
    WoldNatResidualSqrtOneSidedMeanSpectrum alpha := by
  intro c hc0 hcFrontier
  obtain ⟨B, hB, hMean⟩ :=
    woldNatResidualSqrtMeanSpectrum_of_powerSpectrum hPower c hc0 hcFrontier
  refine ⟨B, B, hB, hB, ?_⟩
  filter_upwards [hMean] with N hMeanN
  let W : Finset ℕ := woldNatResidualSqrtWindow N
  let U : Finset ℕ := Finset.Icc N (N + Nat.sqrt N)
  let L : Finset ℕ := Finset.Icc (N - Nat.sqrt N) N
  let S : ℝ := ∑ n ∈ W,
    (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  have hWpos : (0 : ℝ) < W.card := by
    dsimp only [W]
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  have hMeanRewrite : S / (W.card : ℝ) ≤ B := by
    simpa only [woldNatResidualSqrtWeightedMean, W, S] using hMeanN
  have hS : S ≤ B * W.card := (div_le_iff₀ hWpos).mp hMeanRewrite
  have hUsub : U ⊆ W := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨by omega, hn'.2⟩
  have hLsub : L ⊆ W := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨hn'.1, by omega⟩
  constructor
  · rw [woldNatResidualSqrtRightPositiveMean]
    apply (div_le_iff₀ hWpos).2
    calc
      (∑ n ∈ U,
          (n : ℝ) ^ c * max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) ≤
          ∑ n ∈ W,
            (n : ℝ) ^ c * max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hUsub
        intro n hnW hnU
        positivity
      _ ≤ S := by
        dsimp only [S]
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
        exact max_le (le_abs_self _) (abs_nonneg _)
      _ ≤ B * W.card := hS
  · rw [woldNatResidualSqrtLeftNegativeMean]
    apply (div_le_iff₀ hWpos).2
    calc
      (∑ n ∈ L,
          (n : ℝ) ^ c * max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) ≤
          ∑ n ∈ W,
            (n : ℝ) ^ c * max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hLsub
        intro n hnW hnL
        positivity
      _ ≤ S := by
        dsimp only [S]
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
        exact max_le (neg_le_abs _) (abs_nonneg _)
      _ ≤ B * W.card := hS

private theorem natSqrt_cast_le_realSqrt' (N : ℕ) :
    ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hs : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' N
  have hs' : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hs
  calc
    ((Nat.sqrt N : ℕ) : ℝ) =
        Real.sqrt (((Nat.sqrt N : ℕ) : ℝ) ^ 2) := by
      rw [Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hs'

private theorem sqrt_div_self_eq_rpow_neg_half' {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  field_simp
  simpa [pow_two] using hsq

theorem woldNatResidual_right_sqrt_positive_persistence
    {N n : ℕ} (hN : 1 ≤ N) (hnLeft : N ≤ n)
    (hnRight : n ≤ N + Nat.sqrt N) :
    xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
        (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := hNpos.trans_le (by exact_mod_cast hnLeft)
  have hp := woldNatResidual_log_persistence hnLeft
  have hlog : Real.log (n : ℝ) - Real.log (N : ℝ) ≤
      (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      Real.log (n : ℝ) - Real.log (N : ℝ) =
          Real.log ((n : ℝ) / (N : ℝ)) := by
        rw [Real.log_div hnpos.ne' hNpos.ne']
      _ ≤ (n : ℝ) / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hnpos hNpos)
      _ = ((n : ℝ) - (N : ℝ)) / (N : ℝ) := by field_simp
      _ ≤ ((Nat.sqrt N : ℕ) : ℝ) / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ hNpos.le
        rw [← Nat.cast_sub hnLeft]
        exact_mod_cast (by omega : n - N ≤ Nat.sqrt N)
      _ ≤ Real.sqrt (N : ℝ) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right (natSqrt_cast_le_realSqrt' N) hNpos.le
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
        sqrt_div_self_eq_rpow_neg_half' hNpos
  linarith [le_max_left (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0]

theorem woldNatResidual_left_sqrt_negative_persistence
    {N n : ℕ} (hN : 4 ≤ N) (hnLeft : N - Nat.sqrt N ≤ n)
    (hnRight : n ≤ N) :
    -xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
        2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hsHalf : Nat.sqrt N ≤ N / 2 := by
    have hs := Nat.sqrt_le' N
    by_cases hsmall : Nat.sqrt N ≤ 1
    · omega
    · have htwo : 2 ≤ Nat.sqrt N := by omega
      have hmul : 2 * Nat.sqrt N ≤ (Nat.sqrt N) ^ 2 := by nlinarith
      omega
  have hnNat : N / 2 ≤ n := by omega
  have hnPosNat : 0 < n := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hp := woldNatResidual_log_persistence hnRight
  have hNle2n : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : N ≤ 2 * n)
  have hsub : (N : ℝ) - (n : ℝ) ≤ (Nat.sqrt N : ℝ) := by
    rw [← Nat.cast_sub hnRight]
    exact_mod_cast (by omega : N - n ≤ Nat.sqrt N)
  have hlog : Real.log (N : ℝ) - Real.log (n : ℝ) ≤
      2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      Real.log (N : ℝ) - Real.log (n : ℝ) =
          Real.log ((N : ℝ) / (n : ℝ)) := by
        rw [Real.log_div hNpos.ne' hnpos.ne']
      _ ≤ (N : ℝ) / (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hNpos hnpos)
      _ = ((N : ℝ) - (n : ℝ)) / (n : ℝ) := by field_simp
      _ ≤ (Nat.sqrt N : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsub hnpos.le
      _ ≤ (2 * Real.sqrt (N : ℝ)) / (N : ℝ) := by
        rw [div_le_div_iff₀ hnpos hNpos]
        have hs := natSqrt_cast_le_realSqrt' N
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      _ = 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [mul_div_assoc, sqrt_div_self_eq_rpow_neg_half' hNpos]
  linarith [le_max_left (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0]

theorem woldNatResidualPowerSpectrum_of_sqrtOneSidedMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hMeanSpectrum : WoldNatResidualSqrtOneSidedMeanSpectrum alpha) :
    WoldNatResidualPowerSpectrum alpha := by
  intro c hc0 hcFrontier
  have hcHalf : c < 1 / 2 := by linarith
  obtain ⟨Bplus, Bminus, hBplus, hBminus, hMean⟩ :=
    hMeanSpectrum c hc0 hcFrontier
  let C : ℝ := (2 : ℝ) ^ (c + 1) * Bminus + 2 * Bplus + 2
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hMean, eventually_ge_atTop 4] with N hMeanN hN
  let H : ℕ := Nat.sqrt N
  let W : Finset ℕ := woldNatResidualSqrtWindow N
  let L : Finset ℕ := Finset.Icc (N - H) N
  let U : Finset ℕ := Finset.Icc N (N + H)
  let R : ℝ := xiHeatCassiniWoldNatResidualLogDiscrepancy N
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hWpos : (0 : ℝ) < W.card := by
    dsimp only [W]
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  have hUmean :
      (∑ n ∈ U, (n : ℝ) ^ c *
        max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) /
          (W.card : ℝ) ≤ Bplus := by
    simpa only [woldNatResidualSqrtRightPositiveMean, W, U] using hMeanN.1
  have hLmean :
      (∑ n ∈ L, (n : ℝ) ^ c *
        max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) /
          (W.card : ℝ) ≤ Bminus := by
    simpa only [woldNatResidualSqrtLeftNegativeMean, W, L] using hMeanN.2
  have hUsum :
      (∑ n ∈ U, (n : ℝ) ^ c *
        max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) ≤ Bplus * W.card :=
    (div_le_iff₀ hWpos).mp hUmean
  have hLsum :
      (∑ n ∈ L, (n : ℝ) ^ c *
        max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) ≤ Bminus * W.card :=
    (div_le_iff₀ hWpos).mp hLmean
  have hHle : H ≤ N := by
    dsimp only [H]
    exact Nat.sqrt_le_self N
  have hcardW : W.card = 2 * H + 1 := by
    dsimp only [W, H]
    exact woldNatResidualSqrtWindow_card N
  have hcardL : L.card = H + 1 := by
    dsimp only [L]
    rw [Nat.card_Icc]
    omega
  have hcardU : U.card = H + 1 := by
    dsimp only [U]
    rw [Nat.card_Icc]
    omega
  have hcritical :
      (N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    calc
      (N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ)) =
          (N : ℝ) ^ (c - 1 / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
      _ ≤ (N : ℝ) ^ 0 :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hcHalf])
      _ = 1 := Real.rpow_zero _
  have hscaled : (N : ℝ) ^ c * |R| ≤ C := by
    by_cases hR : 0 ≤ R
    · have hpoint : ∀ n ∈ U,
          (N : ℝ) ^ c * R ≤
            (n : ℝ) ^ c *
                max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 + 1 := by
        intro n hn
        have hnBounds := Finset.mem_Icc.1 hn
        have hp := woldNatResidual_right_sqrt_positive_persistence hN1 hnBounds.1
          (by simpa only [H] using hnBounds.2)
        have hpow : (N : ℝ) ^ c ≤ (n : ℝ) ^ c :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnBounds.1) hc0.le
        calc
          (N : ℝ) ^ c * R ≤
              (N : ℝ) ^ c *
                (max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
                  (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by positivity) _)
          _ = (N : ℝ) ^ c * max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
              (N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (n : ℝ) ^ c * max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 + 1 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hpow (by positivity)
            · exact hcritical
      have hsumPoint :
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
            (∑ n ∈ U, (n : ℝ) ^ c *
              max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + U.card := by
        calc
          (U.card : ℝ) * ((N : ℝ) ^ c * R) =
              ∑ _n ∈ U, (N : ℝ) ^ c * R := by simp
          _ ≤ ∑ n ∈ U,
              ((n : ℝ) ^ c *
                max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 + 1) := by
            exact Finset.sum_le_sum hpoint
          _ = (∑ n ∈ U, (n : ℝ) ^ c *
                max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + U.card := by
            rw [Finset.sum_add_distrib]
            simp
      have hcardCompare : (W.card : ℝ) ≤ 2 * U.card := by
        exact_mod_cast (by omega : W.card ≤ 2 * U.card)
      have hupper :
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
            (U.card : ℝ) * (2 * Bplus + 1) := by
        calc
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
              (∑ n ∈ U, (n : ℝ) ^ c *
                max (xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + U.card := hsumPoint
          _ ≤ Bplus * W.card + U.card := add_le_add hUsum le_rfl
          _ ≤ Bplus * (2 * U.card) + U.card := by gcongr
          _ = (U.card : ℝ) * (2 * Bplus + 1) := by ring
      have hUpos : (0 : ℝ) < U.card := by
        rw [hcardU]
        positivity
      have hcentral : (N : ℝ) ^ c * R ≤ 2 * Bplus + 1 := by
        nlinarith
      rw [abs_of_nonneg hR]
      dsimp only [C]
      have htail : 0 ≤ (2 : ℝ) ^ (c + 1) * Bminus := by positivity
      linarith
    · have hRnonpos : R ≤ 0 := le_of_not_ge hR
      have hpoint : ∀ n ∈ L,
          (N : ℝ) ^ c * (-R) ≤
            (2 : ℝ) ^ c *
              ((n : ℝ) ^ c *
                max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + 2 := by
        intro n hn
        have hnBounds := Finset.mem_Icc.1 hn
        have hp := woldNatResidual_left_sqrt_negative_persistence hN
          (by simpa only [H] using hnBounds.1) hnBounds.2
        have hsHalf : Nat.sqrt N ≤ N / 2 := by
          have hs := Nat.sqrt_le' N
          by_cases hsmall : Nat.sqrt N ≤ 1
          · omega
          · have htwo : 2 ≤ Nat.sqrt N := by omega
            have hmul : 2 * Nat.sqrt N ≤ (Nat.sqrt N) ^ 2 := by nlinarith
            omega
        have hnHalf : N ≤ 2 * n := by omega
        have hpow : (N : ℝ) ^ c ≤ (2 : ℝ) ^ c * (n : ℝ) ^ c := by
          calc
            (N : ℝ) ^ c ≤ (2 * (n : ℝ)) ^ c :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnHalf) hc0.le
            _ = (2 : ℝ) ^ c * (n : ℝ) ^ c :=
              Real.mul_rpow (by norm_num) (by positivity)
        calc
          (N : ℝ) ^ c * (-R) ≤
              (N : ℝ) ^ c *
                (max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
                  2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by positivity) _)
          _ = (N : ℝ) ^ c * max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 +
              2 * ((N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ ((2 : ℝ) ^ c * (n : ℝ) ^ c) *
                max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0 + 2 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hpow (by positivity)
            · nlinarith [hcritical]
          _ = (2 : ℝ) ^ c *
                ((n : ℝ) ^ c *
                  max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + 2 := by ring
      have hsumPoint :
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
            (2 : ℝ) ^ c *
              (∑ n ∈ L, (n : ℝ) ^ c *
                max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) +
              2 * L.card := by
        calc
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) =
              ∑ _n ∈ L, (N : ℝ) ^ c * (-R) := by simp
          _ ≤ ∑ n ∈ L,
              ((2 : ℝ) ^ c *
                ((n : ℝ) ^ c *
                  max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) + 2) := by
            exact Finset.sum_le_sum hpoint
          _ = (2 : ℝ) ^ c *
              (∑ n ∈ L, (n : ℝ) ^ c *
                max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) +
              2 * L.card := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp
            ring
      have hcardCompare : (W.card : ℝ) ≤ 2 * L.card := by
        exact_mod_cast (by omega : W.card ≤ 2 * L.card)
      have hupper :
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
            (L.card : ℝ) * ((2 : ℝ) ^ (c + 1) * Bminus + 2) := by
        calc
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
              (2 : ℝ) ^ c *
                (∑ n ∈ L, (n : ℝ) ^ c *
                  max (-xiHeatCassiniWoldNatResidualLogDiscrepancy n) 0) +
                2 * L.card := hsumPoint
          _ ≤ (2 : ℝ) ^ c * (Bminus * W.card) + 2 * L.card := by gcongr
          _ ≤ (2 : ℝ) ^ c * (Bminus * (2 * L.card)) + 2 * L.card := by gcongr
          _ = (L.card : ℝ) * ((2 : ℝ) ^ (c + 1) * Bminus + 2) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
            ring
      have hLpos : (0 : ℝ) < L.card := by
        rw [hcardL]
        positivity
      have hcentral :
          (N : ℝ) ^ c * (-R) ≤ (2 : ℝ) ^ (c + 1) * Bminus + 2 := by
        nlinarith
      rw [abs_of_nonpos hRnonpos]
      dsimp only [C]
      have htail : 0 ≤ 2 * Bplus := by positivity
      linarith
  have hpowpos : (N : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hNpos c).ne'
  calc
    |xiHeatCassiniWoldNatResidualLogDiscrepancy N| =
        (N : ℝ) ^ (-c) *
          ((N : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy N|) := by
      rw [Real.rpow_neg hNpos.le]
      field_simp
    _ ≤ (N : ℝ) ^ (-c) * C :=
      mul_le_mul_of_nonneg_left (by simpa only [R] using hscaled)
        (Real.rpow_nonneg (by positivity) _)
    _ = C * (N : ℝ) ^ (-c) := by ring

theorem woldNatResidualPowerSpectrum_iff_sqrtOneSidedMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    WoldNatResidualPowerSpectrum alpha ↔
      WoldNatResidualSqrtOneSidedMeanSpectrum alpha := by
  constructor
  · exact woldNatResidualSqrtOneSidedMeanSpectrum_of_powerSpectrum
  · exact woldNatResidualPowerSpectrum_of_sqrtOneSidedMeanSpectrum halpha

theorem xiZeroHalfPlaneBound_iff_woldNatResidualSqrtOneSidedMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2) :
    XiZeroHalfPlaneBound alpha ↔
      WoldNatResidualSqrtOneSidedMeanSpectrum alpha := by
  rw [xiZeroHalfPlaneBound_iff_woldNatResidualPowerSpectrum halpha halphaHalf]
  exact woldNatResidualPowerSpectrum_iff_sqrtOneSidedMeanSpectrum halpha

theorem riemannHypothesis_iff_woldNatResidualSqrtOneSidedMeanSpectrum_zero :
    RiemannHypothesis ↔ WoldNatResidualSqrtOneSidedMeanSpectrum 0 := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh]
  exact xiZeroHalfPlaneBound_iff_woldNatResidualSqrtOneSidedMeanSpectrum
    (by norm_num) (by norm_num)

end

end RHTower
