import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalWidthSpectrum

/-!
# Exact critical-window local mean spectrum for the natural Wold residual

The natural Wold residual is a monotone positive arithmetic mass minus `log N` and a constant.
Consequently positive residual spikes persist to the right, while negative spikes persist to the
left. On the symmetric square-root window the logarithmic drift is only at the critical
half-power. This source-specific one-sided persistence converts a diffuse local `L¹` mean into
pointwise decay at every strict sub-half exponent.

For every `0 ≤ alpha < 1/2`, this proves an exact all-width law:

```text
XiZeroHalfPlaneBound alpha
  ↔ every normalized square-root-window Wold residual mean below 1/2-alpha is bounded.
```

At `alpha = 0` the result is a closed local-average criterion equivalent to RH. Each window has
`2 sqrt(N)+1` nodes, so the central node has vanishing relative mass; reverse recovery is not a
pointwise estimate hidden in the definition.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section


/-- Symmetric natural cutoff window of critical square-root radius. -/
def woldNatResidualSqrtWindow (N : ℕ) : Finset ℕ :=
  Finset.Icc (N - Nat.sqrt N) (N + Nat.sqrt N)

/-- Local `L¹` mean of the power-normalized natural Wold residual. -/
def woldNatResidualSqrtWeightedMean (c : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ woldNatResidualSqrtWindow N,
      (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) /
    (woldNatResidualSqrtWindow N).card

/-- Every strict complementary power normalization has bounded critical-window local mean. -/
def WoldNatResidualSqrtMeanSpectrum (alpha : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 2 - alpha →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      woldNatResidualSqrtWeightedMean c N ≤ B

/-- Exact size of the symmetric critical window. -/
theorem woldNatResidualSqrtWindow_card (N : ℕ) :
    (woldNatResidualSqrtWindow N).card = 2 * Nat.sqrt N + 1 := by
  rw [woldNatResidualSqrtWindow, Nat.card_Icc]
  have hs : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
  omega

/-- The critical window always contains its center. -/
theorem woldNatResidualSqrtWindow_nonempty (N : ℕ) :
    (woldNatResidualSqrtWindow N).Nonempty := by
  refine ⟨N, ?_⟩
  simp only [woldNatResidualSqrtWindow, Finset.mem_Icc]
  omega

/-- Natural Wold cumulative mass is monotone because every local Wold weight is nonnegative. -/
theorem woldNatWeightSum_mono {M N : ℕ} (hMN : M ≤ N) :
    xiHeatCassiniWoldNatWeightSum M ≤ xiHeatCassiniWoldNatWeightSum N := by
  rw [xiHeatCassiniWoldNatWeightSum, xiHeatCassiniWoldNatWeightSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hMN
  · intro n hnN hnM
    by_cases hn : n.Prime
    · simp only [xiHeatCassiniWoldNatWeight, dif_pos hn]
      exact woldCoeff_nonneg 1 ⟨n, hn⟩
    · simp [xiHeatCassiniWoldNatWeight, hn]

/-- One-sided logarithmic persistence law for the centered natural Wold residual. -/
theorem woldNatResidual_log_persistence {M N : ℕ} (hMN : M ≤ N) :
    xiHeatCassiniWoldNatResidualLogDiscrepancy M ≤
      xiHeatCassiniWoldNatResidualLogDiscrepancy N +
        (Real.log N - Real.log M) := by
  have hW := woldNatWeightSum_mono hMN
  rw [xiHeatCassiniWoldNatResidualLogDiscrepancy,
    xiHeatCassiniWoldNatResidualLogDiscrepancy]
  linarith

private theorem natSqrt_le_half {N : ℕ} (hN : 4 ≤ N) : Nat.sqrt N ≤ N / 2 := by
  have hs := Nat.sqrt_le' N
  by_cases hsmall : Nat.sqrt N ≤ 1
  · omega
  · have htwo : 2 ≤ Nat.sqrt N := by omega
    have hmul : 2 * Nat.sqrt N ≤ (Nat.sqrt N) ^ 2 := by nlinarith
    omega

private theorem tendsto_nat_sub_sqrt_atTop :
    Tendsto (fun N : ℕ => N - Nat.sqrt N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro K
  filter_upwards [eventually_ge_atTop (max 4 (2 * (K + 1)))] with N hN
  have h4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have h2K : 2 * (K + 1) ≤ N := le_trans (le_max_right _ _) hN
  have hs := natSqrt_le_half h4
  omega

/-- Pointwise natural Wold power spectrum bounds every normalized critical-window mean. -/
theorem woldNatResidualSqrtMeanSpectrum_of_powerSpectrum
    {alpha : ℝ} (hPower : WoldNatResidualPowerSpectrum alpha) :
    WoldNatResidualSqrtMeanSpectrum alpha := by
  intro c hc0 hcFrontier
  obtain ⟨B, hB, hrate⟩ := hPower c hc0 hcFrontier
  refine ⟨B, hB, ?_⟩
  rcases eventually_atTop.1 hrate with ⟨K, hK⟩
  filter_upwards [eventually_ge_atTop (max 4 (2 * (K + 1)))] with N hN
  have h4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have h2K : 2 * (K + 1) ≤ N := le_trans (le_max_right _ _) hN
  have hs := natSqrt_le_half h4
  have hlower : K + 1 ≤ N - Nat.sqrt N := by omega
  have hcard : (0 : ℝ) < (woldNatResidualSqrtWindow N).card := by
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  rw [woldNatResidualSqrtWeightedMean]
  apply (div_le_iff₀ hcard).2
  calc
    (∑ n ∈ woldNatResidualSqrtWindow N,
        (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) ≤
        ∑ _n ∈ woldNatResidualSqrtWindow N, B := by
      apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Icc.1 hn
      have hKn : K ≤ n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hb := hK n hKn
      calc
        (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n| ≤
            (n : ℝ) ^ c * (B * (n : ℝ) ^ (-c)) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)
        _ = B := by
          rw [Real.rpow_neg hnpos.le]
          have hpow : (n : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hnpos c).ne'
          field_simp
    _ = (woldNatResidualSqrtWindow N).card * B := by simp
    _ = B * (woldNatResidualSqrtWindow N).card := by ring

private theorem natSqrt_cast_le_realSqrt (N : ℕ) :
    ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hs : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' N
  have hs' : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hs
  calc
    ((Nat.sqrt N : ℕ) : ℝ) =
        Real.sqrt (((Nat.sqrt N : ℕ) : ℝ) ^ 2) := by
      rw [Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hs'

private theorem sqrt_div_self_eq_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x / x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  field_simp
  simpa [pow_two] using hsq

/-- Positive spikes persist across the right half of the critical square-root window. -/
theorem woldNatResidual_right_sqrt_persistence
    {N n : ℕ} (hN : 1 ≤ N) (hnLeft : N ≤ n)
    (hnRight : n ≤ N + Nat.sqrt N) :
    xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
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
        exact div_le_div_of_nonneg_right (natSqrt_cast_le_realSqrt N) hNpos.le
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
        sqrt_div_self_eq_rpow_neg_half hNpos
  linarith [le_abs_self (xiHeatCassiniWoldNatResidualLogDiscrepancy n)]

/-- Negative spikes persist across the left half of the critical square-root window. -/
theorem woldNatResidual_left_sqrt_persistence
    {N n : ℕ} (hN : 4 ≤ N) (hnLeft : N - Nat.sqrt N ≤ n)
    (hnRight : n ≤ N) :
    -xiHeatCassiniWoldNatResidualLogDiscrepancy N ≤
      |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
        2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hsHalf := natSqrt_le_half hN
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
        have hs := natSqrt_cast_le_realSqrt N
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      _ = 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [mul_div_assoc, sqrt_div_self_eq_rpow_neg_half hNpos]
  linarith [neg_le_abs (xiHeatCassiniWoldNatResidualLogDiscrepancy n)]

/-- Bounded critical-window means recover every strict natural Wold pointwise power rate. -/
theorem woldNatResidualPowerSpectrum_of_sqrtMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hMeanSpectrum : WoldNatResidualSqrtMeanSpectrum alpha) :
    WoldNatResidualPowerSpectrum alpha := by
  intro c hc0 hcFrontier
  have hcHalf : c < 1 / 2 := by linarith
  obtain ⟨B, hB, hMean⟩ := hMeanSpectrum c hc0 hcFrontier
  let C : ℝ := (2 : ℝ) ^ (c + 1) * B + 2
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
  let S : ℝ := ∑ n ∈ W,
    (n : ℝ) ^ c * |xiHeatCassiniWoldNatResidualLogDiscrepancy n|
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hcardWpos : (0 : ℝ) < W.card := by
    dsimp only [W]
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  have hMeanRewrite : S / (W.card : ℝ) ≤ B := by
    simpa only [woldNatResidualSqrtWeightedMean, W, S] using hMeanN
  have hSum : S ≤ B * W.card := (div_le_iff₀ hcardWpos).mp hMeanRewrite
  have hHle : H ≤ N := by dsimp only [H]; exact Nat.sqrt_le_self N
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
  have hLsubset : L ⊆ W := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨hn'.1, hn'.2.trans (by omega)⟩
  have hUsubset : U ⊆ W := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    exact Finset.mem_Icc.2 ⟨(by omega), hn'.2⟩
  have hLsum :
      (∑ n ∈ L, (n : ℝ) ^ c *
        |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) ≤ S := by
    dsimp only [S]
    apply Finset.sum_le_sum_of_subset_of_nonneg hLsubset
    intro n hnW hnL
    positivity
  have hUsum :
      (∑ n ∈ U, (n : ℝ) ^ c *
        |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) ≤ S := by
    dsimp only [S]
    apply Finset.sum_le_sum_of_subset_of_nonneg hUsubset
    intro n hnW hnU
    positivity
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
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| + 1 := by
        intro n hn
        have hnBounds := Finset.mem_Icc.1 hn
        have hp := woldNatResidual_right_sqrt_persistence hN1 hnBounds.1 hnBounds.2
        have hpow : (N : ℝ) ^ c ≤ (n : ℝ) ^ c :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnBounds.1) hc0.le
        calc
          (N : ℝ) ^ c * R ≤
              (N : ℝ) ^ c *
                (|xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
                  (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by positivity) _)
          _ = (N : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
              (N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| + 1 :=
            add_le_add
              (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) hcritical
      have hsumPoint :
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
            (∑ n ∈ U, (n : ℝ) ^ c *
              |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + U.card := by
        calc
          (U.card : ℝ) * ((N : ℝ) ^ c * R) =
              ∑ _n ∈ U, (N : ℝ) ^ c * R := by simp
          _ ≤ ∑ n ∈ U,
              ((n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| + 1) := by
            exact Finset.sum_le_sum hpoint
          _ = (∑ n ∈ U, (n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + U.card := by
            rw [Finset.sum_add_distrib]
            simp
      have hcardCompare : (W.card : ℝ) ≤ 2 * U.card := by
        exact_mod_cast (by omega : W.card ≤ 2 * U.card)
      have hupper :
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
            (U.card : ℝ) * (2 * B + 1) := by
        calc
          (U.card : ℝ) * ((N : ℝ) ^ c * R) ≤
              (∑ n ∈ U, (n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + U.card := hsumPoint
          _ ≤ S + U.card := add_le_add hUsum le_rfl
          _ ≤ B * W.card + U.card := add_le_add hSum le_rfl
          _ ≤ B * (2 * U.card) + U.card := by
            gcongr
          _ = (U.card : ℝ) * (2 * B + 1) := by ring
      have hUpos : (0 : ℝ) < U.card := by
        rw [hcardU]
        positivity
      have hcentral : (N : ℝ) ^ c * R ≤ 2 * B + 1 := by
        nlinarith
      rw [abs_of_nonneg hR]
      dsimp only [C]
      have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (c + 1) := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ (c + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      nlinarith
    · have hRnonpos : R ≤ 0 := le_of_not_ge hR
      have hpoint : ∀ n ∈ L,
          (N : ℝ) ^ c * (-R) ≤
            (2 : ℝ) ^ c *
              ((n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + 2 := by
        intro n hn
        have hnBounds := Finset.mem_Icc.1 hn
        have hp := woldNatResidual_left_sqrt_persistence hN hnBounds.1 hnBounds.2
        have hsHalf := natSqrt_le_half hN
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
                (|xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
                  2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by positivity) _)
          _ = (N : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| +
              2 * ((N : ℝ) ^ c * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ ((2 : ℝ) ^ c * (n : ℝ) ^ c) *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n| + 2 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
            · nlinarith [hcritical]
          _ = (2 : ℝ) ^ c *
                ((n : ℝ) ^ c *
                  |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + 2 := by ring
      have hsumPoint :
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
            (2 : ℝ) ^ c *
              (∑ n ∈ L, (n : ℝ) ^ c *
                |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) +
              2 * L.card := by
        calc
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) =
              ∑ _n ∈ L, (N : ℝ) ^ c * (-R) := by simp
          _ ≤ ∑ n ∈ L,
              ((2 : ℝ) ^ c *
                ((n : ℝ) ^ c *
                  |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) + 2) := by
            exact Finset.sum_le_sum hpoint
          _ = (2 : ℝ) ^ c *
                (∑ n ∈ L, (n : ℝ) ^ c *
                  |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) +
              2 * L.card := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp
            ring
      have hcardCompare : (W.card : ℝ) ≤ 2 * L.card := by
        exact_mod_cast (by omega : W.card ≤ 2 * L.card)
      have hupper :
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
            (L.card : ℝ) * ((2 : ℝ) ^ (c + 1) * B + 2) := by
        calc
          (L.card : ℝ) * ((N : ℝ) ^ c * (-R)) ≤
              (2 : ℝ) ^ c *
                (∑ n ∈ L, (n : ℝ) ^ c *
                  |xiHeatCassiniWoldNatResidualLogDiscrepancy n|) +
                2 * L.card := hsumPoint
          _ ≤ (2 : ℝ) ^ c * S + 2 * L.card := by
            gcongr
          _ ≤ (2 : ℝ) ^ c * (B * W.card) + 2 * L.card := by
            gcongr
          _ ≤ (2 : ℝ) ^ c * (B * (2 * L.card)) + 2 * L.card := by
            gcongr
          _ = (L.card : ℝ) * ((2 : ℝ) ^ (c + 1) * B + 2) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
            ring
      have hLpos : (0 : ℝ) < L.card := by
        rw [hcardL]
        positivity
      have hcentral :
          (N : ℝ) ^ c * (-R) ≤ (2 : ℝ) ^ (c + 1) * B + 2 := by
        nlinarith
      rw [abs_of_nonpos hRnonpos]
      exact hcentral
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

/-- Exact equivalence of pointwise and critical-window natural Wold spectra. -/
theorem woldNatResidualPowerSpectrum_iff_sqrtMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    WoldNatResidualPowerSpectrum alpha ↔
      WoldNatResidualSqrtMeanSpectrum alpha := by
  constructor
  · exact woldNatResidualSqrtMeanSpectrum_of_powerSpectrum
  · exact woldNatResidualPowerSpectrum_of_sqrtMeanSpectrum halpha

/-- Exact all-width critical-window local-mean law. -/
theorem xiZeroHalfPlaneBound_iff_woldNatResidualSqrtMeanSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2) :
    XiZeroHalfPlaneBound alpha ↔
      WoldNatResidualSqrtMeanSpectrum alpha := by
  rw [xiZeroHalfPlaneBound_iff_woldNatResidualPowerSpectrum halpha halphaHalf]
  exact woldNatResidualPowerSpectrum_iff_sqrtMeanSpectrum halpha

/-- Zero width specializes the critical-window local-mean law to RH. -/
theorem riemannHypothesis_iff_woldNatResidualSqrtMeanSpectrum_zero :
    RiemannHypothesis ↔ WoldNatResidualSqrtMeanSpectrum 0 := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh]
  exact xiZeroHalfPlaneBound_iff_woldNatResidualSqrtMeanSpectrum
    (by norm_num) (by norm_num)

end
end RHTower
