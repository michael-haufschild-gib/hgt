import GaloisForLFunctions.RHTower.Sieve.MaynardReceiverMargin
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTAllAmplitudeCount

/-!
# Receiver-normalized Route-T count across every selected-cell amplitude

The low, middle, and endpoint regions preserve different power reserves.  This module proves that
the exact harmonic factor and every fixed logarithmic loss are absorbed uniformly by half of the
appropriate moving reserve.  It then composes that fact with the all-amplitude count capstone.

The conclusion has the two forms used in Maynard's gap-moment receiver: the first count may be
multiplied by an arbitrary fixed logarithmic power, while the second count retains a strict power
reserve.  No additive-energy `R*` alternative is needed.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- A harmonic finite-set factor and any fixed logarithmic power are absorbed by every fixed
positive power. -/
theorem eventually_maynardHarmonicFixedLogCost_absorbed
    {r : ℝ} (hr : 0 < r) (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ K : ℕ, ∀ delta : ℝ,
      (K : ℝ) ≤ T → 1 ≤ delta →
      maynardHarmonicFactor K delta * (Real.log T) ^ q ≤ T ^ r := by
  let eps : ℝ := r / 2
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have hconst : ∀ᶠ T : ℝ in atTop, (100 : ℝ) ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop 100
  filter_upwards [RHTower.burnolEventually_log_pow_le_rpow heps (q + 1), hconst,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with T hlogPow hconstT hlogT hT
  intro K delta hK hdelta
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := le_trans (by norm_num) hlogT
  have hHF := maynardHarmonicFactor_le_hundred_log hT hlogT hK hdelta
  have hmul := mul_le_mul_of_nonneg_right hHF (pow_nonneg hlog0 q)
  have hpowNonneg : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    maynardHarmonicFactor K delta * (Real.log T) ^ q ≤
        (100 * Real.log T) * (Real.log T) ^ q := hmul
    _ = 100 * (Real.log T) ^ (q + 1) := by rw [pow_succ]; ring
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogPow (pow_nonneg hlog0 _) hpowNonneg
    _ = T ^ r := by
      rw [← Real.rpow_add hTpos]
      dsimp only [eps]
      congr 1
      ring

/-- Half of the region-adapted low/middle/high reserve uniformly absorbs the harmonic factor and
any fixed logarithmic receiver loss. -/
theorem eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed
    (A : ℝ) (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ alpha : ℝ, ∀ K : ℕ, ∀ delta : ℝ,
      (K : ℝ) ≤ T → 1 ≤ delta →
      maynardHarmonicFactor K delta * (Real.log T) ^ q ≤
        T ^ (routeTSelectedCellAmplitudeReserve A T alpha / 2) := by
  filter_upwards [eventually_maynardHarmonicFixedLogCost_absorbed
      (r := 1 / 400) (by norm_num) q,
    eventually_maynardHarmonicFixedLogCost_absorbed
      (r := maynardLongGlobalAmplitudeDeficit / 8000)
      (by positivity [maynardLongGlobalAmplitudeDeficit_pos]) q,
    eventually_maynardHarmonicLogCost_absorbed A q] with T hlow hmiddle hhigh
  intro alpha K delta hK hdelta
  by_cases halphaLow : alpha ≤ 19 / 25
  · rw [routeTSelectedCellAmplitudeReserve, if_pos halphaLow]
    convert hlow K delta hK hdelta using 1 <;> norm_num
  · by_cases halphaMiddle : alpha ≤ 997 / 1000
    · rw [routeTSelectedCellAmplitudeReserve, if_neg halphaLow, if_pos halphaMiddle]
      convert hmiddle K delta hK hdelta using 1 <;> ring
    · rw [routeTSelectedCellAmplitudeReserve, if_neg halphaLow, if_neg halphaMiddle]
      convert hhigh K delta hK hdelta using 1 <;> ring

/-- Generic form of the preserved-margin calculation: a multiplier absorbed by half of reserve
leaves the other half as a strict power saving. -/
theorem maynard_count_receiver_margin_general
    {R T e d H : ℝ} {q : ℕ}
    (hT : 1 ≤ T)
    (hR : R ≤ H * T ^ (e - d))
    (hcost : H * (Real.log T) ^ q ≤ T ^ (d / 2)) :
    R * (Real.log T) ^ q ≤ T ^ (e - d / 2) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hpow0 : 0 ≤ T ^ (e - d) := Real.rpow_nonneg hT0.le _
  calc
    R * (Real.log T) ^ q ≤
        (H * T ^ (e - d)) * (Real.log T) ^ q :=
      mul_le_mul_of_nonneg_right hR (pow_nonneg hlog0 q)
    _ = (H * (Real.log T) ^ q) * T ^ (e - d) := by ring
    _ ≤ T ^ (d / 2) * T ^ (e - d) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = T ^ (e - d / 2) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

/-- **Receiver-normalized all-amplitude capstone.**  The first alternative absorbs `q` logarithms;
the second alternative retains half of the positive region reserve. -/
theorem exists_eventually_routeT_selectedCell_all_amplitude_receiver
    (q : ℕ) :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {X K : ℕ} {mu N0 c alpha V delta : ℝ},
      1 ≤ X → (X : ℝ) ≤ T ^ mu →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 3 / 4 ≤ alpha →
      0 < V → 1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ r ∈ S,
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxWindowRelevant N0 X 60 box →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤ V) →
      ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
        (L : ℝ) ≤ T ^ (mu / 60) ∧
        (((S.card : ℝ) * (Real.log T) ^ q ≤
            T ^ (mu * (1 - alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha / 2)) ∨
          (S.card : ℝ) ≤
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha / 2)) := by
  obtain ⟨A, hcount⟩ :=
    exists_eventually_routeT_selectedCell_all_amplitude_first_or_second
  refine ⟨A, ?_⟩
  filter_upwards [hcount,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A q,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    eventually_ge_atTop (1 : ℝ)] with T hcountT hcostQ hcostZero hT
  intro X K mu N0 c alpha V delta hX hXscale hmuLo hmuHi hc halpha hV
    hdelta hdeltaHi hK S hS lam hband hgap hdiam haggregate hreserve
  obtain ⟨L, hL, hXL, hLscale, hfirst | hsecond⟩ :=
    hcountT hX hXscale hmuLo hmuHi hc halpha hV (lt_of_lt_of_le zero_lt_one hdelta)
      hdeltaHi S hS lam hband hgap hdiam haggregate hreserve
  · refine ⟨L, hL, hXL, hLscale, Or.inl ?_⟩
    exact maynard_count_receiver_margin_general hT hfirst
      (hcostQ alpha K delta hK hdelta)
  · refine ⟨L, hL, hXL, hLscale, Or.inr ?_⟩
    have hmargin := maynard_count_receiver_margin_general hT hsecond
      (hcostZero alpha K delta hK hdelta)
    simpa using hmargin

end RHTower.Sieve
