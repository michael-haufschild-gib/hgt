import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthAllSourceGraphNoGo
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalSqrtOneSidedMeanSpectrum
import GaloisForLFunctions.RHTower.RoutePTwoStepWildSaddleTraceClassRelocation

/-!
# T2 all-source graph-to-directed-mean no-go

The T2 receiver needs a directed, natural-index square-root-window estimate: positive residual
mass to the right and negative residual mass to the left. This is strictly weaker than the prior
symmetric absolute criterion, but it still cannot follow from every polynomial graph norm of the
currently available harmonic, activation-Fisher, and literal essential-edge sources, even when
one includes the fixed height-`1/10` Bohr increment datum.

The existing positive counter-residual is `r_N = p_N^(-1/20)`. On every right square-root
half-window it is monotone and the unconditional prime upper bound yields
`p_(N + sqrt N) ≤ 8 N^2`. Hence its `c = 1/4` directed positive mean is bounded below by a
positive constant times `N^(3/20)` and diverges.

The positive survivor is precise: a T2 producer for the directed spectrum must supply a
physical-scale local arithmetic law or source regularity stronger than all finite polynomial graph
norms. It cannot be assembled from the current graph norms plus the fixed Bohr datum.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive residual mass on the right half of the natural square-root window, normalized by
the full window cardinality. -/
def t2PrimeClockSqrtRightPositiveMean (r : ℕ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc N (N + Nat.sqrt N),
      (n : ℝ) ^ c * max (r n) 0) /
    (woldNatResidualSqrtWindow N).card

private theorem tendsto_index_sqrtRight_atTop :
    Tendsto (fun N : ℕ => N + Nat.sqrt N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

private theorem eventually_nthPrime_sqrtRight_le_eight_mul_sq :
    ∀ᶠ N : ℕ in atTop,
      (nthPrimeSubtype (N + Nat.sqrt N) : ℝ) ≤ 8 * (N : ℝ) ^ 2 := by
  filter_upwards [tendsto_index_sqrtRight_atTop.eventually
      eventually_nthPrime_le_two_mul_nat_log, eventually_ge_atTop 1] with N hp hN
  let m : ℕ := N + Nat.sqrt N
  have hNnat : 1 ≤ N := by exact_mod_cast hN
  have hNposNat : 0 < N := by omega
  have hmN : N ≤ m := by dsimp only [m]; omega
  have hmposNat : 0 < m := lt_of_lt_of_le hNposNat hmN
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast hmposNat
  have hmle : (m : ℝ) ≤ 2 * (N : ℝ) := by
    dsimp only [m]
    exact_mod_cast (show N + Nat.sqrt N ≤ 2 * N by
      have hs := Nat.sqrt_le_self N
      omega)
  have hlog : Real.log (m : ℝ) ≤ (m : ℝ) :=
    (Real.log_le_sub_one_of_pos hmpos).trans (by linarith)
  calc
    (nthPrimeSubtype m : ℝ) ≤ 2 * (m : ℝ) * Real.log (m : ℝ) := by
      simpa only [nthPrimeSubtype] using hp
    _ ≤ 2 * (m : ℝ) * (m : ℝ) := by gcongr
    _ ≤ 8 * (N : ℝ) ^ 2 := by nlinarith

private theorem t2BohrTerminalCounterResidual_eq_rpow (N : ℕ) :
    t2BohrTerminalCounterResidual N =
      (nthPrimeSubtype N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  rw [t2BohrTerminalCounterResidual, xiMassNthPrimeLogHeight,
    Real.rpow_def_of_pos (nthPrimeSubtype_pos N)]
  congr 1
  ring

private theorem t2BohrTerminalCounterResidual_antitone :
    Antitone t2BohrTerminalCounterResidual := by
  intro a b hab
  apply Real.exp_le_exp.mpr
  change -xiMassNthPrimeLogHeight b / 20 ≤
    -xiMassNthPrimeLogHeight a / 20
  have hheight : xiMassNthPrimeLogHeight a ≤ xiMassNthPrimeLogHeight b := by
    simpa only [xiMassNthPrimeLogHeight] using
      nthPrimeSubtype_log_strictMono.monotone hab
  linarith

private theorem t2BohrTerminalCounterResidual_sqrtRight_lower (N : ℕ)
    (hprime : (nthPrimeSubtype (N + Nat.sqrt N) : ℝ) ≤ 8 * (N : ℝ) ^ 2) :
    (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ)) ≤
      t2BohrTerminalCounterResidual (N + Nat.sqrt N) := by
  have hp : 0 < (nthPrimeSubtype (N + Nat.sqrt N) : ℝ) :=
    nthPrimeSubtype_pos _
  have hmajor : 0 < 8 * (N : ℝ) ^ 2 := hp.trans_le hprime
  rw [t2BohrTerminalCounterResidual_eq_rpow]
  have hpow : (nthPrimeSubtype (N + Nat.sqrt N) : ℝ) ^ (1 / 20 : ℝ) ≤
      (8 * (N : ℝ) ^ 2) ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow hp.le hprime (by norm_num)
  have hinv := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hp (1 / 20 : ℝ)) hpow
  rw [Real.rpow_neg hmajor.le, Real.rpow_neg hp.le]
  simpa only [one_div] using hinv

private theorem t2PrimeClockSqrtRightPositiveMean_lower (N : ℕ)
    (hprime : (nthPrimeSubtype (N + Nat.sqrt N) : ℝ) ≤ 8 * (N : ℝ) ^ 2) :
    (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
        (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ)) ≤
      t2PrimeClockSqrtRightPositiveMean t2BohrTerminalCounterResidual (1 / 4) N := by
  have hWpos : (0 : ℝ) < (woldNatResidualSqrtWindow N).card := by
    exact_mod_cast (woldNatResidualSqrtWindow_nonempty N).card_pos
  rw [t2PrimeClockSqrtRightPositiveMean]
  apply (le_div_iff₀ hWpos).2
  let U : Finset ℕ := Finset.Icc N (N + Nat.sqrt N)
  let b : ℝ := (N : ℝ) ^ (1 / 4 : ℝ) *
    (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ))
  have hbn : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hpoint : ∀ n ∈ U, b ≤ (n : ℝ) ^ (1 / 4 : ℝ) *
      max (t2BohrTerminalCounterResidual n) 0 := by
    intro n hn
    have hnm := (Finset.mem_Icc.1 hn).2
    have hnN := (Finset.mem_Icc.1 hn).1
    have hendpoint := t2BohrTerminalCounterResidual_sqrtRight_lower N hprime
    have hmono := t2BohrTerminalCounterResidual_antitone hnm
    have hpow : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) (by norm_num)
    have hresn : 0 ≤ t2BohrTerminalCounterResidual n := by
      unfold t2BohrTerminalCounterResidual
      positivity
    have hendpointPos : 0 ≤ t2BohrTerminalCounterResidual (N + Nat.sqrt N) := by
      unfold t2BohrTerminalCounterResidual
      positivity
    dsimp only [b]
    rw [max_eq_left hresn]
    calc
      (N : ℝ) ^ (1 / 4 : ℝ) *
          (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ)) ≤
        (N : ℝ) ^ (1 / 4 : ℝ) *
          t2BohrTerminalCounterResidual (N + Nat.sqrt N) :=
        mul_le_mul_of_nonneg_left hendpoint (by positivity)
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) *
          t2BohrTerminalCounterResidual (N + Nat.sqrt N) :=
        mul_le_mul_of_nonneg_right hpow hendpointPos
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * t2BohrTerminalCounterResidual n :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsum : (U.card : ℝ) * b ≤
      ∑ n ∈ U, (n : ℝ) ^ (1 / 4 : ℝ) *
        max (t2BohrTerminalCounterResidual n) 0 := by
    calc
      (U.card : ℝ) * b = ∑ _n ∈ U, b := by simp
      _ ≤ ∑ n ∈ U, (n : ℝ) ^ (1 / 4 : ℝ) *
          max (t2BohrTerminalCounterResidual n) 0 := Finset.sum_le_sum hpoint
  have hcard : ((woldNatResidualSqrtWindow N).card : ℝ) ≤ 2 * U.card := by
    have hcardNat : (woldNatResidualSqrtWindow N).card ≤ 2 * U.card := by
      rw [woldNatResidualSqrtWindow_card]
      dsimp only [U]
      rw [Nat.card_Icc]
      omega
    exact_mod_cast hcardNat
  have hscale : ((woldNatResidualSqrtWindow N).card : ℝ) * ((1 / 2 : ℝ) * b) ≤
      (U.card : ℝ) * b := by
    nlinarith [mul_le_mul_of_nonneg_right hcard hbn]
  calc
    ((1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
        (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ))) *
        ((woldNatResidualSqrtWindow N).card : ℝ) =
        ((woldNatResidualSqrtWindow N).card : ℝ) *
          ((1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
            (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ))) := by ring
    _ =
        ((woldNatResidualSqrtWindow N).card : ℝ) * ((1 / 2 : ℝ) * b) := by
      dsimp only [b]
      ring
    _ ≤ (U.card : ℝ) * b := hscale
    _ ≤ ∑ n ∈ U, (n : ℝ) ^ (1 / 4 : ℝ) *
        max (t2BohrTerminalCounterResidual n) 0 := hsum

private theorem tendsto_t2PrimeClockSqrtRightPositiveMean_lower_atTop :
    Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
        (8 * (N : ℝ) ^ 2) ^ (-(1 / 20 : ℝ))) atTop atTop := by
  let C : ℝ := (1 / 2 : ℝ) * (8 : ℝ) ^ (-(1 / 20 : ℝ))
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (3 / 20 : ℝ)) atTop atTop :=
    hpower.const_mul_atTop hC
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  dsimp only [C]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
    (sq_nonneg (N : ℝ)), ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hexp : (3 / 20 : ℝ) = 1 / 4 + 2 * (-(1 / 20 : ℝ)) := by ring
  rw [hexp, Real.rpow_add hNpos]
  ring_nf

/-- The established all-source graph counter-residual has divergent right-directed natural
square-root mean at admissible exponent `1/4`. -/
theorem tendsto_t2PrimeClockSqrtRightPositiveMean_counter_atTop :
    Tendsto
      (t2PrimeClockSqrtRightPositiveMean t2BohrTerminalCounterResidual (1 / 4))
      atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  filter_upwards [eventually_nthPrime_sqrtRight_le_eight_mul_sq,
      tendsto_t2PrimeClockSqrtRightPositiveMean_lower_atTop
        (eventually_ge_atTop B)] with N hprime hlarge
  exact hlarge.trans (t2PrimeClockSqrtRightPositiveMean_lower N hprime)

/-- Proposed reconstruction from all currently proved polynomial source graph laws and the fixed
Bohr datum to every admissible right-directed natural square-root mean bound. -/
def T2PrimeClockBohrAllSourceGraphDirectedMeanLandingPrinciple : Prop :=
  ∀ r : ℕ → ℝ,
    Tendsto r atTop (𝓝 0) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) * r N ^ 2)) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeActivationOccupancyFisherDensity (nthPrimeSubtype N) * r N ^ 2)) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate (nthPrimeSubtype N) * r N ^ 2)) →
    Summable (fun N : ℕ =>
      ‖(((r (N + 1) - r N : ℝ) : ℂ) *
        (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ))‖ ^ 2) →
    ∀ c : ℝ, 0 < c → c < 1 / 2 →
      ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
        t2PrimeClockSqrtRightPositiveMean r c N ≤ B

/-- **T2 all-source graph-to-directed-mean no-go.** Every currently formalized polynomial source
graph law and the fixed height-`1/10` Bohr datum are compatible with failure of even the
right-directed square-root mean required by the weaker T2 receiver criterion. -/
theorem not_T2PrimeClockBohrAllSourceGraphDirectedMeanLandingPrinciple :
    ¬ T2PrimeClockBohrAllSourceGraphDirectedMeanLandingPrinciple := by
  intro hlanding
  obtain ⟨B, hB, hbound⟩ := hlanding t2BohrTerminalCounterResidual
    t2BohrTerminalCounterResidual_tendsto_zero
    summable_t2BohrTerminalCounterResidual_allLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_activationFisherAllLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_actualEssentialEdgeAllLogGraphEnergy
    summable_norm_sq_t2BohrTerminalCounterCoefficient
    (1 / 4) (by norm_num) (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      B < t2PrimeClockSqrtRightPositiveMean t2BohrTerminalCounterResidual (1 / 4) N :=
    tendsto_t2PrimeClockSqrtRightPositiveMean_counter_atTop (eventually_gt_atTop B)
  obtain ⟨N, hNbound, hNlarge⟩ := (hbound.and hlarge).exists
  linarith

end

end RHTower
