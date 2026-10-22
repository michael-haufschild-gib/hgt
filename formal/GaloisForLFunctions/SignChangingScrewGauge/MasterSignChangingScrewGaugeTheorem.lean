import GaloisForLFunctions.SignChangingScrewGauge.SignChangingCollarGaugeLedger
import GaloisForLFunctions.SignChangingScrewGauge.NetPrimeAutocorrelationAndEdgeTentResolution
import GaloisForLFunctions.SignChangingScrewGauge.ScrewResonantCollarAndPoleCalibration

/-!
# Master Theorem: Sign-Changing Screw-Resonant Gauges in GlobalIncidenceAllocation

This module packages the four-leg formalization of Mechanism 3 of Project Argon
(`docs/reports/review-2110/argon.md`, §1.4) into a single unconditional master theorem
(`sign_changing_screw_gauge_master_theorem`):

1. **Leg 1 — Unconditional Sign-Changing Collar Gauge Commutator, Prime-Shift Cancellation, and Collar Conservation:**
   - Commutator summation by parts `∫ x, F x * P x * shiftCommutator P F t x = gaugeJumpProfile P F t`
     and the collar conservation law `gaugeJumpProfile P F L - ∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L)) = -2 * autoCorr F L`
     hold for **every** continuous gauge `P` (with no `0 ≤ P` or `P ≤ 1` constraint) and any continuous
     compactly supported `F` with `P = 1` on `supp F`.
   - For an even gauge `P` vanishing at `log n` (`n ≥ 3`), a negative collar value `P (log 2) < 0`
     makes `profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (log 2) < 0` and strictly boosts
     `-poleFreeWeilOperator P 0 c_arch` above its prime-free baseline.

2. **Leg 2 — Bilateral Net Prime-Autocorrelation Accounting & Sign-Change Rigidity:**
   For every continuous odd `F` supported in `[−r, r]` with `0 ≤ F` on `[0, ∞)` and every
   trans-half-width shift `r ≤ Real.log n`, `0 ≤ netPrimeStripBalance F r n`; conversely, any prime
   deficit `evenStripGain F r n < oddStripCost F r n` at `r ≤ Real.log n` forces `F` to take both
   strictly positive and strictly negative values on `[0, ∞)`.

3. **Leg 3 — Complete Resolution of the Edge-Tent Sharing Obstruction:**
   For any edge-supported profile `F` vanishing on `(−(r − ε), r − ε)` (`0 < ε`), on every finite
   band `S` of shifts in `[r, 2 * (r - ε)]`, `∑ n ∈ S, netPrimeStripBalance F r n = 0` identically.

4. **Leg 4 — Screw-Resonant Kernel Unification, Plastic Crossover Dichotomy, and Collar Moment Calibration:**
   - For every `t > 0`, `screwRegularKernel t = 2 * Real.cosh (t / 2) - archLevyDensity t`, crossing
     zero at `screwSignThreshold = Real.log plasticRoot ∈ (1/10, log 2)`.
   - When `0 ≤ P` and `2 * R ≤ screwSignThreshold`, `0 ≤ screwResonantJumpEnergy P F`.
   - For any plateau `P₀` and sign-changing collar `P_col` with `evenPoleMoment P_col = -evenPoleMoment P₀`,
     `evenPoleMoment (fun y => P₀ y + P_col y) = 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.SignChangingScrewGauge

/-- **Master Theorem: Sign-Changing Screw-Resonant Gauges in GlobalIncidenceAllocation.**
Unconditional synthesis of:
1. Unconditional sign-changing collar gauge commutator summation by parts, collar conservation law,
   and prime-shift subsolution escape via `P (log 2) < 0`;
2. Half-line single-sign trans-horizon positivity (`0 ≤ netPrimeStripBalance F r n` for all `r ≤ log n`
   whenever `F ≥ 0` on `[0, ∞)`) and sign-change necessity for trans-half-width prime deficits;
3. Complete resolution of the Edge-Tent Sharing Obstruction (`∑_{n ∈ S} netPrimeStripBalance F r n = 0`
   on every thin band `S ⊆ [r, 2(r - ε)]` for any profile `F` vanishing on `(−(r − ε), r − ε)`);
4. Exact screw-resonant kernel unification (`screwRegularKernel t = 2 cosh(t/2) - archLevyDensity t`),
   plastic crossover dichotomy across `screwSignThreshold = Real.log plasticRoot ∈ (1/10, log 2)`,
   sub-plastic positivity of `screwResonantJumpEnergy`, and sign-changing collar `cosh`-moment
   neutralization (`evenPoleMoment (P₀ + P_col) = 0`). -/
theorem sign_changing_screw_gauge_master_theorem :
    -- (1) Unconditional sign-changing collar gauge commutator, conservation law & prime-shift escape
    ((∀ (P F : ℝ → ℝ) (L : ℝ),
        Continuous P → Continuous F → HasCompactSupport F →
        (∀ x, F x ≠ 0 → P x = 1) →
        (∫ x, F x * P x * shiftCommutator P F L x) = gaugeJumpProfile P F L ∧
          gaugeJumpProfile P F L - ∫ x, F x ^ 2 * P x * (P (x + L) + P (x - L)) =
            -2 * autoCorr F L) ∧
      (∀ (P : ℝ → ℝ) (c_arch : ℝ),
        (∀ y, P (-y) = P y) → (∀ n : ℕ, 3 ≤ n → P (Real.log n) = 0) →
        P (Real.log 2) < 0 →
        profilePrimeSum P 0 = 2 * vonMangoldtAtom 2 * P (Real.log 2) ∧
          profilePrimeSum P 0 < 0 ∧
          -(1 / 2) * profileArchTerm P 0 - c_arch < -poleFreeWeilOperator P 0 c_arch)) ∧
    -- (2) Half-line single-sign trans-horizon positivity & sign-change necessity
    ((∀ (F : ℝ → ℝ) (r : ℝ) (n : ℕ),
        0 < r → Continuous F → (∀ x, F (-x) = -F x) →
        (∀ x, r < |x| → F x = 0) → (∀ x, 0 ≤ x → 0 ≤ F x) →
        r ≤ Real.log n → 0 ≤ netPrimeStripBalance F r n) ∧
      (∀ (F : ℝ → ℝ) (r : ℝ) (n : ℕ),
        0 < r → Continuous F → (∀ x, F (-x) = -F x) →
        (∀ x, r < |x| → F x = 0) → r ≤ Real.log n →
        evenStripGain F r n < oddStripCost F r n →
        (∃ x ≥ 0, 0 < F x) ∧ (∃ x ≥ 0, F x < 0))) ∧
    -- (3) Complete resolution of the Edge-Tent Sharing Obstruction on the thin band
    (∀ (F : ℝ → ℝ) (r ε : ℝ) (S : Finset ℕ),
      0 < ε → (∀ x, |x| < r - ε → F x = 0) →
      (∀ n ∈ S, r ≤ Real.log n ∧ Real.log n ≤ 2 * (r - ε)) →
      ∑ n ∈ S, netPrimeStripBalance F r n = 0) ∧
    -- (4) Screw-resonant kernel unification, plastic crossover dichotomy & collar moment calibration
    ((∀ t : ℝ, 0 < t → screwRegularKernel t = 2 * Real.cosh (t / 2) - archLevyDensity t) ∧
      ((1 / 10 < screwSignThreshold ∧ screwSignThreshold < Real.log 2) ∧
        screwRegularKernel screwSignThreshold = 0 ∧
        (∀ t, 0 < t → t ≤ screwSignThreshold → 0 ≤ -screwRegularKernel t) ∧
        (∀ t, screwSignThreshold < t → -screwRegularKernel t < 0)) ∧
      (∀ (P F : ℝ → ℝ) (R : ℝ),
        (∀ y, 0 ≤ P y) → (∀ y, R ≤ |y| → P y = 0) → 2 * R ≤ screwSignThreshold →
        0 ≤ screwResonantJumpEnergy P F) ∧
      (∀ (P₀ P_col : ℝ → ℝ),
        Continuous P₀ → HasCompactSupport P₀ →
        Continuous P_col → HasCompactSupport P_col →
        evenPoleMoment P_col = -evenPoleMoment P₀ →
        evenPoleMoment (fun y => P₀ y + P_col y) = 0)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro P F L hP hF hFc hFP
    exact ⟨integral_mul_mul_shiftCommutator_eq_gaugeJumpProfile hP hF hFc L,
      gaugeJumpProfile_sub_shiftPotential_eq_neg_two_mul_autoCorr hP hF hFc hFP L⟩
  · intro P c_arch heven hP3 hneg
    exact profilePrimeSum_zero_neg_and_weilOperator_gain_of_neg_collar c_arch heven hP3 hneg
  · intro F r n hr hF hodd hsupp hnn hn
    exact netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici hr hF hodd hsupp hnn hn
  · intro F r n hr hF hodd hsupp hn hlt
    exact exists_pos_and_neg_on_Ici_of_evenStripGain_lt_oddStripCost hr hF hodd hsupp hn hlt
  · intro F r ε S hε hinner hS
    exact sum_netPrimeStripBalance_eq_zero_of_edgeSupported hε hinner hS
  · intro t ht
    exact screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht
  · exact screwRegularKernel_crossover_dichotomy
  · intro P F R hP0 hPR hR
    exact screwResonantJumpEnergy_nonneg_of_two_mul_le_screwSignThreshold hP0 hPR hR
  · intro P₀ P_col hP₀ hP₀c hPcol hPcolc hcancel
    exact evenPoleMoment_collar_cancellation hP₀ hP₀c hPcol hPcolc hcancel

end GaloisForLFunctions.SignChangingScrewGauge

end
