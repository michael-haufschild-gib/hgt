import GaloisForLFunctions.BiScaleUncertainty.PrimePowerNodeDeletionPrice
import GaloisForLFunctions.BiScaleUncertainty.PrimeTowerDeletionCompositeCharge
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerTowerPairWindowSpectrum
import GaloisForLFunctions.BiScaleUncertainty.PrimeTwoThreeDecouplingLength
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowLiouvilleMirror
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowTwistInvariance
import GaloisForLFunctions.BiScaleUncertainty.PrimeBlindLevySlackAndWindowCone
import GaloisForLFunctions.BiScaleUncertainty.GradedPoleCompressionWidthCriterion
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.RHTower.EvenSectorPolarCompletion
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeBlindFarkas
import GaloisForLFunctions.RHTower.MarkovShiftPolarizationAndEvenPrimitivePBAP
import GaloisForLFunctions.RHTower.AdmixturesAndTheShiftedPairLeaveTheWeilCone
import GaloisForLFunctions.RHTower.NonTemperedShiftedZetaPairCountermodel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseLawOfOscillatingPrimePatterns
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFirstNegativeLagOfACurve
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfACurveIsItsWindowFiltration

/-!
# Node Criticality, Phase Sensitivity, and the Bi-Scale Selectivity and Calibration Synthesis

This module resolves the four research problems of §7.7 in `BiScaleUncertainty/README.md`:

1. **Node criticality at arbitrary support and the three-scale separation of `log 4` vs. `log 6`
   (`weilPositiveAt_certificate_rigidity`, `zeroPoleBlindPositiveOn_iff_exists_certificate`,
   `zeroPoleBlindPositiveOn_deleted_iff`, `threeScale_log_four_vs_log_six`):**
   Across arbitrary support, two-sided Farkas duality (`exists_weilPositiveFull_of_zeroPoleBlindPositiveOn`),
   pole-weight rigidity (`RHTower.eq_one_of_weilPositiveAt`), and unconditional Weil-cone uniqueness
   (`RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull`) force every certificate `(β, w)`
   dominating `nodeArchOnly c - β * nodePoleMass c` on `WeilTestFn` to satisfy `β = 1` and
   `w n = Λ(n)` for all `n ≥ 2`. Consequently, a node `n ≥ 2` carries positive certificate charge
   if and only if `IsPrimePow n`, with `w 4 = log 2 > 0` and `w 6 = 0`.
   Furthermore, `log 4` (the prime-square self-lag `2 · log 2`) and `log 6` (the composite sum-lag
   `log 2 + log 3`) separate across three distinct Bi-Scale regimes:
   * *Arbitrary-support single-node deletion*: deleting `4` costs `-(log 2 / 2)`
     (`isLeast_deletionDeviations_four`) and falsifies zero-pole positivity unconditionally, whereas
     deleting `6` costs `0` (`zeroPoleBlindPositiveOn_diff_six_iff`).
   * *Window-spectrum decoupling threshold (`L ∈ (log 4, log 6]`)*: on windows of length
     `L ∈ (log 4, log 6]`, the joint gain price `(√17 + 1)/4 · log 2` of the tower pair `{2, 4}` is
     already attained (`log_four_attains_and_log_six_does_not`) because `4 = 2²` closes its tower on
     its own lag, whereas the joint Euler price `w₂ + w₃` of `{2, 3}` is unattained (`≤ 111/100`)
     until `L > log 6` (`twoThree_price_jump`).
   * *Whole-tower composite charge*: while `log 6` is free for the single nodes `{2, 3}`, imposing
     blindness at `6 = 2 · 3` on the whole towers of `{2, 3}` lowers the supremum deviation by at
     least `9/10` (`gridTowerDeviation_two_three_le`).

2. **Prime-blind archimedean positivity, exact symbol/Lévy slacks, automatic even-polar completion,
   and sign-changing ground-state gauges (`zeroPoleBlindSymbolValue_nonneg_iff`,
   `abs_gammaBracket_le_zeroPoleBlindLevyInfimum_iff`, `primeBlindPositiveEvenPolar_iff_riemannHypothesis`,
   `primeBlindPositive_four_tier_equivalence`, `realPolar_even_odd_groundState_gauge`):**
   For every node set `𝒩 ⊆ ℕ`, `0 ≤ zeroPoleBlindSymbolValue 𝒩` (equivalently
   `|EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum 𝒩`) holds if and only if `RiemannHypothesis`
   holds and every prime power lies in `𝒩`. Whenever any prime power is missing from `𝒩` (in
   particular on `Set.univ \ {4}`, `{p | p.Prime}`, or `primePowerNodes \ {m}` for a prime power
   `m`), `zeroPoleBlindSymbolValue 𝒩 < 0` and `zeroPoleBlindLevyInfimum 𝒩 < |EF.gammaBracket 0|`
   unconditionally. Moreover, combining `exists_weilPositiveEvenPolar_iff` with the automatic pole
   completion `weilPositiveFull_of_weilPositiveEvenPolar` proves that prime-blind archimedean
   positivity on the sign-changing even pole-free test space `WeilEvenPolarTestFn` is unconditionally
   equivalent to RH (`PrimeBlindPositiveEvenPolar ↔ RiemannHypothesis`), uniting the four prime-blind
   positivity tiers (`WeilOneSided.PrimeBlindPositive`, `ZeroPoleBlindPositiveOn primePowerNodes`,
   `PrimitivePrimeBlindPositive`, and `PrimeBlindPositiveEvenPolar`) together with the even/odd
   sign-changing ground-state gauges (`RealEvenPolarTestFn`, `RealOddPolarTestFn`, `evenShift`,
   `oddShift`, and `primitiveProj`).

3. **Phase-sensitive damped readings vs. twist-invariant window extremes, and summed producers across
   the Pole Compression, the Packet, and the Band (`liouvilleUnimodularTwist`,
   `windowExtremes_twist_blind_and_mirror_symmetric`,
   `phaseSensitive_dampedReceiver_separates_untwisted_and_flipped`,
   `poleCompression_summed_reading_and_producer`, `packet_summed_reading_and_local_gauge`,
   `band_summed_reading_and_cramer_limit`):**
   Window extremes (`windowCeiling L`, `windowFloor L`) are invariant under every unimodular
   multiplicative twist `χ` (`twistedWindowCeiling_eq`, `twistedWindowFloor_eq`), including the
   Liouville twist `χ(p) = -1`, and are mirror-symmetric up to `2 * mirrorDefect N = O(L)`. By
   contrast, the summed half-damped receiver `phaseWeight a t₀ φ` separates untwisted and
   Liouville-flipped phases at every height `t₀ ≠ 0`: at `φ = 0` (`a = 1`),
   `ReceiverBounded (phaseWeight 1 t₀ 0) ↔ riemannZeta (1 / 2 + t₀ * I) = 0`, whereas at the
   flipped phase `φ = π` (`a = 1`, where `cos π = -1 < 1`), `ReceiverBounded (phaseWeight 1 t₀ π)`
   holds unconditionally for every `t₀ ≠ 0`. In each of the three Bi-Scale sectors (Pole Compression,
   Packet, Band), the prime reading is a summed/integrated Chebyshev functional equipped with an
   explicit unconditional producer.

4. **The Bi-Scale selectivity and calibration battery (`functionField_vs_goldenFakeCurve_and_windowHiding`,
   `shiftedPairWeilEnergy_eq_nodeArchEnergy_of_blindOn_primePowers`,
   `shiftedPair_deviation_single_pairTestFn_two`, `shiftedPair_leaves_weilCone_and_ramanujan`,
   `beurling_and_admixture_calibration_battery`):**
   Every Bi-Scale sector is calibrated against the four benchmark models:
   * *Function fields (`pureDatum`) vs. the Golden Beurling fake curve (`goldenDatum`) and window
     hiding (`exists_hidden_on_window`)*: pure curves satisfy all lag and Hodge-index positivity
     laws, whereas `goldenDatum` has integral zeta coefficients and positive integer point counts
     (`1 ≤ goldenDatum.pointCount j`) yet fails the Bi-Scale lag test at the first lag `log 5`.
   * *The shifted pair `ζ(s - a)ζ(s + a)` (`shiftedPairVonMangoldt a`)*: on the prime-power-blind
     cone `BlindOn primePowerNodes c`, `shiftedPairWeilEnergy a c = nodeArchEnergy c = weilEnergy c`
     is completely independent of `a`, whereas at the single node `2` (`pairTestFn 2 (-1)`), its
     normalized deviation is `-cosh(a log 2) (log 2 / √2) < -(log 2 / √2)` for `a ≠ 0`, expelling
     `shiftedPairVonMangoldt a` from the Weil cone at degree `2`.
   * *The Liouville twist (`liouvilleUnimodularTwist`)*: preserves window ceilings and floors while
     diverging from the untwisted prime measure on summed phase-sensitive receivers.
   * *Beurling node-deletion, primes-only, gapped, sub-square-root density, and admixture models*:
     `Set.univ \ {4}`, `{p | p.Prime}`, gapped grids, and sub-square-root density grids all have
     strictly negative `zeroPoleBlindSymbolValue`, and any non-zero admixture `Λ + c u` leaves the
     Weil cone.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Node Criticality at Arbitrary Support and the Three-Scale Separation of `log 4` vs. `log 6` -/

/-- **Certificate rigidity at arbitrary support.** Any pole weight `β : ℝ` and node weight sequence
`w : ℕ → ℝ` that is Weil-positive (`RHTower.WeilPositiveAt β w`) across arbitrary support must have
canonical pole weight `β = 1` and von Mangoldt node weights `w n = Λ(n)` for all `n ≥ 2`. -/
theorem weilPositiveAt_certificate_rigidity {β : ℝ} {w : ℕ → ℝ}
    (hW : RHTower.WeilPositiveAt β w) :
    β = 1 ∧ ∀ n, 2 ≤ n → w n = ArithmeticFunction.vonMangoldt n := by
  have hβ : β = 1 := RHTower.eq_one_of_weilPositiveAt hW
  subst hβ
  have hfull : RHTower.WeilPositiveFull w := fun f hf hfc => by
    have h := hW f hf hfc
    unfold RHTower.WeilPoleWeight.weilPoleWeightFunctional at h
    simpa using h
  exact ⟨rfl, RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hfull⟩

/-- **Every Weil-positive certificate charges exactly the prime powers.** For any `w : ℕ → ℝ` in
`WeilPositiveFull` and any integer `n ≥ 2`:
* `w n = Λ(n)`,
* `0 < w n ↔ w n ≠ 0 ↔ IsPrimePow n`,
* `w 4 = log 2 > 0` and `w 6 = 0`. -/
theorem weilPositiveFull_charge_iff_isPrimePow {w : ℕ → ℝ} (hW : RHTower.WeilPositiveFull w) :
    (∀ n, 2 ≤ n → w n = ArithmeticFunction.vonMangoldt n) ∧
      (∀ n, 2 ≤ n → (0 < w n ↔ IsPrimePow n)) ∧
      (∀ n, 2 ≤ n → (w n ≠ 0 ↔ IsPrimePow n)) ∧
      w 4 = Real.log 2 ∧ w 6 = 0 := by
  have heq : ∀ n, 2 ≤ n → w n = ArithmeticFunction.vonMangoldt n :=
    RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW
  refine ⟨heq, fun n hn => ?_, fun n hn => ?_, ?_, ?_⟩
  · rw [heq n hn, ArithmeticFunction.vonMangoldt_pos_iff]
  · rw [heq n hn, ArithmeticFunction.vonMangoldt_ne_zero_iff]
  · rw [heq 4 (by norm_num), show (4 : ℕ) = 2 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  · rw [heq 6 (by norm_num)]
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)

/-- **Farkas certificate characterization of `ZeroPoleBlindPositiveOn 𝒩`.** For every node set
`𝒩 ⊆ ℕ`, zero-pole archimedean positivity on `𝒩`-blind combinations holds if and only if there
exists a full-cone Weil-positive weight sequence `w : ℕ → ℝ` supported on `𝒩` for `n ≥ 2`. -/
theorem zeroPoleBlindPositiveOn_iff_exists_certificate (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔
      ∃ w : ℕ → ℝ, RHTower.WeilPositiveFull w ∧ ∀ n, 2 ≤ n → n ∉ 𝒩 → w n = 0 := by
  constructor
  · exact exists_weilPositiveFull_of_zeroPoleBlindPositiveOn
  · rintro ⟨w, hW, hsupp⟩
    have hRH : RiemannHypothesis :=
      (RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW).1
    refine zeroPoleBlindPositiveOn_iff.mpr ⟨hRH, fun n hn hΛ => ?_⟩
    by_contra hn𝒩
    have hw := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW n hn
    rw [hsupp n hn hn𝒩] at hw
    exact hΛ hw.symm

/-- **Exact single-node deletion classification on `primePowerNodes`.** For every integer `m`,
`ZeroPoleBlindPositiveOn (primePowerNodes \ {m})` holds if and only if `RiemannHypothesis` holds and
`m` is not a prime power. -/
theorem zeroPoleBlindPositiveOn_deleted_iff (m : ℕ) :
    ZeroPoleBlindPositiveOn (primePowerNodes \ {m}) ↔
      RiemannHypothesis ∧ ¬ IsPrimePow m := by
  by_cases hm : IsPrimePow m
  · exact ⟨fun h => False.elim (not_zeroPoleBlindPositiveOn_diff_of_isPrimePow primePowerNodes hm h),
      fun h => False.elim (h.2 hm)⟩
  · rw [zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow primePowerNodes hm,
      ← riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers]
    exact ⟨fun h => ⟨h, hm⟩, fun h => h.1⟩

/-- **Three-scale separation of `log 4` (prime square self-lag) vs. `log 6` (composite sum-lag).**
1. *Arbitrary-support single-node deletion*: deleting `4` has least deviation `-(log 2 / 2)` and
   refutes `ZeroPoleBlindPositiveOn` unconditionally, whereas deleting `6` is redundant
   (`ZeroPoleBlindPositiveOn (primePowerNodes \ {6}) ↔ RiemannHypothesis`) and on
   `BlindOn primePowerNodes c` we have `nodeArchEnergy c = weilEnergy c`.
2. *Window-spectrum decoupling threshold (`L ∈ (log 4, log 6]`)*: on windows of length
   `L ∈ (log 4, log 6]`, the joint gain price `(√17 + 1)/4 · log 2` of `{2, 4}` is attained, while
   the joint Euler price `w₂ + w₃` of `{2, 3}` is not attained (`≤ 111/100`) and jumps at `log 6`.
3. *Whole-tower composite charge*: on the integer-grid tower cone `gridTowerDeviations {2, 3}`
   (where composite lags including `log 6` are blind), every deviation is bounded above by
   `2 log 2/(√2 - 1) + 2 log 3/(√3 - 1) - 9/10`, dropping at least `9/10` below the prime-power
   tower price. -/
theorem threeScale_log_four_vs_log_six {L L' : ℝ} (hL₁ : Real.log 4 < L) (hL₂ : L ≤ Real.log 6)
    (hL' : Real.log 6 < L') :
    (IsLeast (deletionDeviations 4) (-(Real.log 2 / 2)) ∧
      ¬ ZeroPoleBlindPositiveOn (primePowerNodes \ {4}) ∧
      (∀ c : WeilTestFn →₀ ℝ, BlindOn primePowerNodes c → nodeArchEnergy c = weilEnergy c) ∧
      (ZeroPoleBlindPositiveOn (primePowerNodes \ {6}) ↔ RiemannHypothesis)) ∧
    (((Real.sqrt 17 + 1) / 4 * Real.log 2 ∈ towerWindowDeviations 2 L ∧
        eulerPrice {2, 3} (fun _ => 1) ∉ eulerWindowDeviations {2, 3} (fun _ => 1) L) ∧
      (sSup (eulerWindowDeviations {2, 3} (fun _ => 1) L) ≤ decouplingCeiling ∧
        decouplingCeiling < sSup (eulerWindowDeviations {2, 3} (fun _ => 1) L'))) ∧
    (∀ x ∈ gridTowerDeviations {2, 3},
      x ≤ 2 * Real.log 2 / (Real.sqrt 2 - 1) + 2 * Real.log 3 / (Real.sqrt 3 - 1) - 9 / 10) := by
  refine ⟨⟨isLeast_deletionDeviations_four,
    not_zeroPoleBlindPositiveOn_diff_four primePowerNodes,
    fun c hb => nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers hb,
    (zeroPoleBlindPositiveOn_diff_six_iff primePowerNodes).trans
      riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.symm⟩,
    ⟨log_four_attains_and_log_six_does_not hL₁ hL₂, twoThree_price_jump hL₂ hL'⟩,
    gridTowerDeviation_two_three_le⟩

/-! ### 2. Prime-Blind Archimedean Positivity, Exact Symbol/Lévy Slacks, Automatic Even-Polar Completion, and Sign-Changing Ground-State Gauges -/

/-- `ZeroPoleBlindPositiveOn 𝒩` is equivalent to `0 ≤ zeroPoleBlindSymbolValue 𝒩`. -/
theorem zeroPoleBlindPositiveOn_iff_zeroPoleBlindSymbolValue_nonneg (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔ 0 ≤ zeroPoleBlindSymbolValue 𝒩 := by
  have h0 : ZeroPoleBlindPositiveOn 𝒩 ↔ ZeroPoleBlindSymbolSlackOn 𝒩 0 := by
    simp [ZeroPoleBlindPositiveOn, ZeroPoleBlindSymbolSlackOn]
  rw [h0, zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue]
  constructor <;> intro h <;> linarith

/-- **Exact node-criticality law for `zeroPoleBlindSymbolValue 𝒩`.** For every node set `𝒩 ⊆ ℕ`,
`0 ≤ zeroPoleBlindSymbolValue 𝒩` holds if and only if `RiemannHypothesis` holds and every prime
power lies in `𝒩`. -/
theorem zeroPoleBlindSymbolValue_nonneg_iff (𝒩 : Set ℕ) :
    0 ≤ zeroPoleBlindSymbolValue 𝒩 ↔
      RiemannHypothesis ∧ ∀ n, IsPrimePow n → n ∈ 𝒩 := by
  rw [← zeroPoleBlindPositiveOn_iff_zeroPoleBlindSymbolValue_nonneg, zeroPoleBlindPositiveOn_iff]
  refine and_congr_right fun _ => ⟨fun h n hn => h n hn.two_le
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hn), fun h n _ hΛ =>
      h n (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)⟩

/-- **Exact node-criticality law for `zeroPoleBlindLevyInfimum 𝒩` against `|EF.gammaBracket 0|`.**
For every node set `𝒩 ⊆ ℕ`, `|EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum 𝒩` holds if and only
if `RiemannHypothesis` holds and every prime power lies in `𝒩`. -/
theorem abs_gammaBracket_le_zeroPoleBlindLevyInfimum_iff (𝒩 : Set ℕ) :
    |EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum 𝒩 ↔
      RiemannHypothesis ∧ ∀ n, IsPrimePow n → n ∈ 𝒩 := by
  rw [zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue,
    ← zeroPoleBlindSymbolValue_nonneg_iff]
  constructor <;> intro h <;> linarith

/-- **Missing any prime power makes `zeroPoleBlindSymbolValue 𝒩 < 0` and
`zeroPoleBlindLevyInfimum 𝒩 < |EF.gammaBracket 0|` unconditionally.** -/
theorem zeroPoleBlindSymbolValue_neg_of_missing_primePow {𝒩 : Set ℕ} {m : ℕ}
    (hm : IsPrimePow m) (hm𝒩 : m ∉ 𝒩) :
    zeroPoleBlindSymbolValue 𝒩 < 0 ∧
      zeroPoleBlindLevyInfimum 𝒩 < |EF.gammaBracket 0| := by
  have hnot : ¬ (0 ≤ zeroPoleBlindSymbolValue 𝒩) := by
    rw [zeroPoleBlindSymbolValue_nonneg_iff]
    exact fun h => hm𝒩 (h.2 m hm)
  have hlt : zeroPoleBlindSymbolValue 𝒩 < 0 := not_le.mp hnot
  refine ⟨hlt, ?_⟩
  rw [zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue]
  linarith

/-- **Exact deleted-node symbol and Lévy interval criterion for RH.** `RiemannHypothesis` holds if
and only if for every prime power `m`:
* `zeroPoleBlindSymbolValue (primePowerNodes \ {m}) ∈ Set.Ico (-(Λ(m) / √m)) 0`, and equivalently
* `zeroPoleBlindLevyInfimum (primePowerNodes \ {m}) ∈
    Set.Ico (|EF.gammaBracket 0| - Λ(m) / √m) |EF.gammaBracket 0|`. -/
theorem riemannHypothesis_iff_deleted_symbol_and_levy_bounds :
    RiemannHypothesis ↔
      ∀ m : ℕ, IsPrimePow m →
        zeroPoleBlindSymbolValue (primePowerNodes \ {m}) ∈
          Set.Ico (-(ArithmeticFunction.vonMangoldt m / Real.sqrt m)) 0 ∧
        zeroPoleBlindLevyInfimum (primePowerNodes \ {m}) ∈
          Set.Ico (|EF.gammaBracket 0| - ArithmeticFunction.vonMangoldt m / Real.sqrt m)
            |EF.gammaBracket 0| := by
  rw [riemannHypothesis_iff_forall_zeroPoleBlindSymbolSlackOn_deleted]
  refine forall_congr' fun m => imp_congr_right fun hm => ?_
  rw [zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue]
  have hneg := zeroPoleBlindSymbolValue_neg_of_missing_primePow hm (by simp : m ∉ primePowerNodes \ {m})
  have hlevy := zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue
    (primePowerNodes \ {m})
  simp only [Set.mem_Ico]
  constructor
  · intro hle
    exact ⟨⟨by linarith, hneg.1⟩, ⟨by linarith, hneg.2⟩⟩
  · intro h
    linarith [h.1.1]

/-- **Automatic pole completion on even pole-free tests makes `PrimeBlindPositiveEvenPolar`
unconditionally equivalent to the Riemann Hypothesis.** -/
theorem primeBlindPositiveEvenPolar_iff_riemannHypothesis :
    RHTower.EvenSector.PrimeBlindPositiveEvenPolar ↔ RiemannHypothesis := by
  rw [← RHTower.EvenSector.exists_weilPositiveEvenPolar_iff]
  constructor
  · rintro ⟨lam, hlam⟩
    have hfull : RHTower.WeilPositiveFull lam :=
      RHTower.EvenSector.weilPositiveFull_of_weilPositiveEvenPolar hlam
    exact (RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp
      hfull).1
  · intro hRH
    have hW : RHTower.WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
        ⟨hRH, fun _ _ => rfl⟩
    have hEP : RHTower.EvenSector.WeilPositiveEvenPolar
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
      have hset := Set.ext_iff.mp RHTower.EvenSector.evenPolar_sourceCone_eq_full_sourceCone
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      exact hset.mpr hW
    exact ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ), hEP⟩

/-- **Four-tier equivalence of Prime-Blind Archimedean Positivity.**
The Riemann Hypothesis is unconditionally equivalent to each of:
1. `WeilOneSided.PrimeBlindPositive` (all complex tests on the integer grid),
2. `ZeroPoleBlindPositive` (zero-pole combinations blind at all `n ≥ 2`),
3. `ZeroPoleBlindPositiveOn primePowerNodes` (zero-pole combinations blind only at prime powers),
4. `RHTower.EvenSector.PrimeBlindPositiveEvenPolar` (even pole-free tests `f̂(i/2) = 0`). -/
theorem primeBlindPositive_four_tier_equivalence :
    (RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive) ∧
      (RiemannHypothesis ↔ ZeroPoleBlindPositive) ∧
      (RiemannHypothesis ↔ ZeroPoleBlindPositiveOn primePowerNodes) ∧
      (RiemannHypothesis ↔ RHTower.EvenSector.PrimeBlindPositiveEvenPolar) :=
  ⟨RHTower.riemannHypothesis_iff_primeBlindPositive_unconditional,
    riemannHypothesis_iff_zeroPoleBlindPositive,
    riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers,
    primeBlindPositiveEvenPolar_iff_riemannHypothesis.symm⟩

/-- **Sign-changing ground-state gauges across the even primitive and odd hyperplanes.**
1. Every `f : RHTower.EvenPrimitiveWeilTestFn` has identically zero real pole term
   (`re_weilPoleTerm_eq_zero`), so `markovCountertermEnergy lam` coincides with `(weilFullFunctional lam).re`
   (`markovCountertermEnergy_evenPrimitive_eq_re_weilFullFunctional`).
2. On the primitive hyperplane `coshHalfMoment F = 0`, Markov positivity decomposes orthogonally into
   `MarkovPositiveEvenPrimitive lam ∧ MarkovPositiveOdd lam`
   (`markovPositivePrimitive_iff_evenPrimitive_and_odd`), and the shift pair `(evenShift g h, oddShift g h)`
   satisfies `weilArchRe (evenShift g h) + weilArchRe (oddShift g h) = weilArchRe g`. -/
theorem realPolar_even_odd_groundState_gauge (lam : ℕ → ℝ) :
    (∀ f : RHTower.EvenPrimitiveWeilTestFn,
        (RHTower.weilPoleTerm (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)).re = 0 ∧
          RHTower.markovCountertermEnergy lam f.toWeilTestFn.1 =
            (RHTower.weilFullFunctional lam (EF.weilTest f.toWeilTestFn.1 f.toWeilTestFn.1)).re) ∧
      (RHTower.MarkovPositivePrimitive lam ↔
        RHTower.MarkovPositiveEvenPrimitive lam ∧ RHTower.MarkovPositiveOdd lam) :=
  ⟨fun f => ⟨f.re_weilPoleTerm_eq_zero,
      RHTower.markovCountertermEnergy_evenPrimitive_eq_re_weilFullFunctional lam f⟩,
    RHTower.markovPositivePrimitive_iff_evenPrimitive_and_odd lam⟩

/-! ### 3. Phase-Sensitive Damped Readings vs. Twist-Invariant Window Extremes, and Summed Producers Across the Pole Compression, Packet, and Band -/

open scoped ArithmeticFunction.Omega CompactlySupported

/-- **The Liouville twist as a `UnimodularTwist`.** It maps `n ↦ (-1)^{Ω(n)}` for `n ≥ 1` (and `0`
at `0`), flipping the sign of every prime while fixing every prime square. -/
def liouvilleUnimodularTwist : UnimodularTwist where
  toFun n := if n = 0 then 0 else (-1 : ℂ) ^ Ω n
  map_one := by simp
  map_mul m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [if_neg hm, if_neg hn, if_neg hmn,
      ArithmeticFunction.cardFactors_mul hm hn, pow_add]
  norm_prime p hp := by
    rw [if_neg hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp, pow_one, norm_neg,
      norm_one]

theorem liouvilleUnimodularTwist_apply_prime {p : ℕ} (hp : p.Prime) :
    liouvilleUnimodularTwist.toFun p = -1 := by
  simp [liouvilleUnimodularTwist, hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp]

theorem liouvilleUnimodularTwist_apply_prime_sq {p : ℕ} (hp : p.Prime) :
    liouvilleUnimodularTwist.toFun (p ^ 2) = 1 := by
  rw [liouvilleUnimodularTwist.map_pow, liouvilleUnimodularTwist_apply_prime hp, neg_one_sq]

/-- **Twist blindness and Liouville mirror symmetry of the window extremes.** For every unimodular
twist `χ` (in particular `liouvilleUnimodularTwist`) and every window length `L ≥ 0` with
`(windowDeviations L).Nonempty`, the twisted window ceiling and floor coincide with `windowCeiling L`
and `windowFloor L`, and their sum is bounded by `2 * mirrorDefect ⌈Real.exp L⌉₊ ≤ 4L + 4(log 8 + 4)`. -/
theorem windowExtremes_twist_blind_and_mirror_symmetric (χ : UnimodularTwist) {L : ℝ}
    (hL : 0 ≤ L) (hne : (windowDeviations L).Nonempty) :
    twistedWindowCeiling χ L = windowCeiling L ∧
      twistedWindowFloor χ L = windowFloor L ∧
      |windowCeiling L + windowFloor L| ≤ 2 * mirrorDefect ⌈Real.exp L⌉₊ ∧
      |windowCeiling L + windowFloor L| ≤ 4 * L + 4 * (Real.log 8 + 4) := by
  obtain ⟨hN, hdef⟩ := mirror_cutoff hL
  have hmir := abs_windowCeiling_add_windowFloor_le hL hne hN
  exact ⟨twistedWindowCeiling_eq χ hL hne,
    twistedWindowFloor_eq χ hL hne,
    hmir,
    hmir.trans hdef⟩

/-- **Phase sensitivity of the summed half-damped receiver vs. twist blindness of window extremes.**
For every height `t₀ ≠ 0`:
1. At the untwisted phase `φ = 0` (`a = 1`, where `cos 0 = 1`), the summed half-damped receiver
   `ReceiverBounded (phaseWeight 1 t₀ 0)` holds if and only if `riemannZeta (1 / 2 + t₀ * I) = 0`.
2. At the Liouville-flipped phase `φ = π` (`a = 1`, where `cos π = -1 < 1`),
   `ReceiverBounded (phaseWeight 1 t₀ π)` holds **unconditionally** for every `t₀ ≠ 0`, regardless
   of whether `1 / 2 + t₀ * I` is a zero of `ζ`. -/
theorem phaseSensitive_dampedReceiver_separates_untwisted_and_flipped {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    (ReceiverBounded (phaseWeight 1 t₀ 0) ↔
      riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0) ∧
    ReceiverBounded (phaseWeight 1 t₀ Real.pi) := by
  have ha : |(1 : ℝ)| ≤ 1 := by norm_num
  constructor
  · rw [receiverBounded_phaseWeight_iff ha ht₀]
    simp only [Real.cos_zero, mul_one, lt_irrefl, false_or]
  · rw [receiverBounded_phaseWeight_iff ha ht₀]
    left
    rw [Real.cos_pi]
    norm_num

/-- **Summed reading and unconditional producer in the Pole Compression sector.**
1. For every `T ≥ 0`, the integrated Chebyshev deficit `ccmLogChebyshevDeficitPrimitive T` is the
   exact Riesz-summed prime reading `e^T - 1 - ∑_{n ≤ e^T} Λ(n) log(e^T / n)` (`riesz_eq_deficit`).
2. At every positive aperture `a`, `ccmLogChebyshevDeficitPrimitive (2a)` and `ccmWeilPoleCross a`
   agree up to `poleCrossDeficitAllowance * e^a`.
3. For every `0 ≤ α < 1 / 2`, `XiZeroHalfPlaneBound α` holds iff `|ccmWeilPoleCross a|` grows at
   most like `O(e^{(1 + 2β)a})` for every `β ∈ (α, 1 / 2)`. -/
theorem poleCompression_summed_reading_and_producer :
    (∀ T : ℝ, 0 ≤ T →
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) *
          Real.log (Real.exp T / n) =
        Real.exp T - 1 - RHTower.ccmLogChebyshevDeficitPrimitive T) ∧
    (∀ a : RHTower.SuzukiPositiveAperture,
      |RHTower.ccmLogChebyshevDeficitPrimitive (2 * a.1)| ≤
        |RHTower.ccmWeilPoleCross a| + poleCrossDeficitAllowance * Real.exp a.1 ∧
      |RHTower.ccmWeilPoleCross a| ≤
        |RHTower.ccmLogChebyshevDeficitPrimitive (2 * a.1)| +
          poleCrossDeficitAllowance * Real.exp a.1) ∧
    (∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
      (RHTower.XiZeroHalfPlaneBound α ↔
        ∀ β : ℝ, α < β → β < 1 / 2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ a : RHTower.SuzukiPositiveAperture,
          |RHTower.ccmWeilPoleCross a| ≤ C * Real.exp ((1 + 2 * β) * a.1))) :=
  ⟨fun _ hT => riesz_eq_deficit hT,
    fun a => ⟨abs_ccmLogChebyshevDeficitPrimitive_le_abs_ccmWeilPoleCross_add a,
      abs_ccmWeilPoleCross_le_abs_ccmLogChebyshevDeficitPrimitive_add a⟩,
    fun _ hα hα' => xiZeroHalfPlaneBound_iff_forall_exists_abs_ccmWeilPoleCross_le hα hα'⟩

/-- **Summed reading and local Chebyshev gauge in the Packet sector (`splineProbe`).**
1. For every shift `τ ∈ ℝ`, `e^τ * stationaryPacket ChebyshevGauge.splineProbe τ` equals the
   summed spline prime reading minus the polar mass `splinePrimeSum τ - splinePolarMass τ`.
2. For every shift `τ > 4`, `stationaryPacket ChebyshevGauge.splineProbe τ` is given by the local
   Chebyshev gauge integral over `[τ - 4, τ + 4]` and satisfies the unconditional bound
   `|stationaryPacket splineProbe τ| ≤ 4 e^{2 - τ/2} + (1/2) e^4 ∫_{τ-4}^{τ+4} |Ẽ(t)| dt`.
3. `RiemannHypothesis` holds iff `splinePrimeSum τ ≤ splinePolarMass τ + K e^τ` for all `τ > 4`. -/
theorem packet_summed_reading_and_local_gauge :
    (∀ τ : ℝ, Real.exp τ * ChebyshevGauge.stationaryPacket ChebyshevGauge.splineProbe τ =
      ChebyshevGauge.splinePrimeSum τ - ChebyshevGauge.splinePolarMass τ) ∧
    (∀ τ : ℝ, 4 < τ →
      |ChebyshevGauge.stationaryPacket ChebyshevGauge.splineProbe τ| ≤
        4 * Real.exp (2 - τ / 2) +
          1 / 2 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4),
            |ChebyshevGauge.normalizedLogError t|) ∧
    (RiemannHypothesis ↔ ∃ K : ℝ, ∀ τ : ℝ, 4 < τ →
      ChebyshevGauge.splinePrimeSum τ ≤ ChebyshevGauge.splinePolarMass τ + K * Real.exp τ) :=
  ⟨ChebyshevGauge.exp_mul_stationaryPacket_splineProbe,
    fun _ hτ => ChebyshevGauge.abs_stationaryPacket_splineProbe_le_local_chebyshev hτ,
    ChebyshevGauge.riemannHypothesis_iff_spline_prime_sum_le_of_gt_four⟩

/-- **Summed reading and Cramér mean-square limit in the Band sector.**
1. In the hyperbolic gauge, every signed prime-polar source `signedSource f N u` decomposes into
   the forward residual, the boundary Chebyshev value `normalizedLogError (cutoff N) * f (u + cutoff N)`,
   minus the gauge convolution `chebyshevGaugeConvolution f N u` (`signedSource_eq_gauge`).
2. `RiemannHypothesis` holds iff the integrated square of `normalizedLogError` on `[0, L]` grows at
   most linearly `≤ C * (1 + L)` (`riemannHypothesis_iff_meanSquare_band`).
3. Under `RiemannHypothesis`, the mean square `(∫ t in Icc 0 M, Ẽ(t)²) / M` converges as `M → ∞` to the
   exact Cramér limit `totalZeroEnergy = ∑_ρ m_ρ² / ‖ρ‖²` (`tendsto_mean_sq_normalizedLogError`). -/
theorem band_summed_reading_and_cramer_limit :
    (∀ (f : C_c(ℝ, ℝ)), ContDiff ℝ 1 (f : ℝ → ℝ) → ∀ (N : ℕ) (u : ℝ),
      SignedPrimePolar.signedSource f N u =
        ChebyshevGauge.forwardResidual f N u +
          ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) *
            f (u + SignedPrimePolar.cutoff N) -
          ChebyshevGauge.chebyshevGaugeConvolution f N u) ∧
    (RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
        (∫ t in Icc 0 L, ChebyshevGauge.normalizedLogError t ^ 2) ≤ C * (1 + L)) ∧
    (RiemannHypothesis →
      Tendsto (fun M : ℝ => (∫ t in Icc 0 M, ChebyshevGauge.normalizedLogError t ^ 2) / M)
        atTop (𝓝 ChebyshevGauge.totalZeroEnergy)) :=
  ⟨fun f hf N u => ChebyshevGauge.signedSource_eq_gauge f hf N u,
    ChebyshevGauge.riemannHypothesis_iff_meanSquare_band,
    ChebyshevGauge.tendsto_mean_sq_normalizedLogError⟩

/-! ### 4. The Bi-Scale Selectivity and Calibration Battery -/

/-- **Model 1 — Function-field calibration vs. the Golden Beurling fake curve (`goldenDatum`) and
finite-window hiding (`exists_hidden_on_window`).**
1. Every pure curve datum `D : CurveDatum ι` (`∀ i, ‖D.β i‖ ≤ 1`) has nonnegative Bi-Scale lag tests
   at all multiples `n * log q` (`re_W_curveConfig_lagTest_nonneg`).
2. The Golden Beurling fake curve `goldenDatum` has integral zeta coefficients and positive integer
   point counts `1 ≤ goldenDatum.pointCount j` (`one_le_goldenDatum_pointCount`), yet its first
   Bi-Scale lag test at `log 5` is strictly negative (`goldenDatum_lagTest_neg`), its Frobenius
   span defect on `{0, 1}` is strictly negative (`goldenDatum_spanDefect_neg`), and its Hodge
   defect is `if a ≤ log 5 / 2 then 0 else ⊤` (`goldenDatum_hodgeDefectAt`).
3. For every finite window degree `n : ℕ`, there exists a curve datum with off-circle reciprocal
   roots (`∃ i, ‖D.β i‖ ≠ 1`) whose Frobenius span defects on all subsets of `Finset.range n` are
   nonnegative (`exists_hidden_on_window`). -/
theorem functionField_vs_goldenFakeCurve_and_windowHiding :
    (∀ {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq),
      (∀ i, ‖D.β i‖ ≤ 1) →
      ∀ {g : ℝ → ℂ} {w : ℝ}, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2) →
        w < Real.log D.q → ∀ (s : ℝ) (n : ℕ),
        0 ≤ ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
          (lagTest g s (n * Real.log D.q))).re) ∧
    ((∀ j : ℕ, 1 ≤ j → 1 ≤ goldenDatum.pointCount j) ∧
      (∀ {g : ℝ → ℂ} {w : ℝ}, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2) →
        w < Real.log goldenDatum.q → (0 < ∫ u, ‖g u‖ ^ 2) →
        ((goldenDatum.curveConfig goldenDatum_strip).W
          (lagTest g (-1 : ℝ) ((1 : ℕ) * Real.log goldenDatum.q))
          (lagTest g (-1 : ℝ) ((1 : ℕ) * Real.log goldenDatum.q))).re < 0) ∧
      goldenDatum.spanDefect {0, 1} (fun k => if k = 0 then 1 else -1 / Real.sqrt 5) < 0 ∧
      (∀ a : ℝ, hodgeDefectAt (goldenDatum.curveConfig goldenDatum_strip) a =
        if a ≤ Real.log 5 / 2 then 0 else ⊤)) ∧
    (∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (D : CurveDatum ι),
      (∃ i, ‖D.β i‖ ≠ 1) ∧ ∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d) :=
  ⟨fun D hD hpure _ _ hg hgs hwL s n =>
      CurveDatum.re_W_curveConfig_lagTest_nonneg D hD hpure hg hgs hwL s n,
    ⟨fun _ hj => one_le_goldenDatum_pointCount hj,
      fun hg hgs hwL hg0 => goldenDatum_lagTest_neg hg hgs hwL hg0,
      goldenDatum_spanDefect_neg,
      goldenDatum_hodgeDefectAt⟩,
    exists_hidden_on_window⟩

/-- The full Weil functional of a combination evaluated with the shifted-pair weights
`shiftedPairVonMangoldt a n = (n^a + n^{-a}) Λ(n)`. -/
def shiftedPairWeilEnergy (a : ℝ) (c : WeilTestFn →₀ ℝ) : ℝ :=
  c.sum fun f t =>
    t * (RHTower.weilFullFunctional (RHTower.shiftedPairVonMangoldt a)
      (EF.weilTest f.1 f.1)).re

/-- **Explicit formula for the shifted-pair Weil energy in Bi-Scale coordinates:**
`nodeArchEnergy c = shiftedPairWeilEnergy a c + Σ_n shiftedPairVonMangoldt a n · L_n(c)`. -/
theorem nodeArchEnergy_eq_shiftedPairWeilEnergy_add (a : ℝ) (c : WeilTestFn →₀ ℝ) :
    nodeArchEnergy c = shiftedPairWeilEnergy a c +
      linearCombination ℝ (fun j : LogIndex => RHTower.shiftedPairVonMangoldt a (j : ℕ))
        (nodeVector c) := by
  rw [shiftedPairWeilEnergy, sum_re_weilFullFunctional, nodeArchEnergy_eq, nodeVector_eq]
  ring

/-- **Prime-power-blind cones cannot separate the shifted pair `ζ(s - a)ζ(s + a)` from `ζ(s)`.**
Because `shiftedPairVonMangoldt a n = (n^a + n^{-a}) Λ(n)` vanishes outside `primePowerNodes`, on
every combination `c` with `BlindOn primePowerNodes c` we have
`shiftedPairWeilEnergy a c = nodeArchEnergy c = weilEnergy c` for every shift `a ∈ ℝ`. -/
theorem shiftedPairWeilEnergy_eq_nodeArchEnergy_of_blindOn_primePowers (a : ℝ)
    {c : WeilTestFn →₀ ℝ} (hb : BlindOn primePowerNodes c) :
    shiftedPairWeilEnergy a c = nodeArchEnergy c ∧
      shiftedPairWeilEnergy a c = weilEnergy c := by
  have h1 : nodeArchEnergy c = shiftedPairWeilEnergy a c := by
    rw [nodeArchEnergy_eq_shiftedPairWeilEnergy_add a c, linearCombination_apply, Finsupp.sum,
      Finset.sum_eq_zero fun j _ => ?_, add_zero]
    by_cases hj : IsPrimePow (j : ℕ)
    · rw [hb j hj, zero_smul]
    · rw [RHTower.shiftedPairVonMangoldt,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hj, zero_mul, smul_zero]
  exact ⟨h1.symm, h1.symm.trans (nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers hb)⟩

/-- **Single-node separation of `shiftedPairVonMangoldt a` at node `2`.** On the narrow pair test
`c = Finsupp.single (pairTestFn 2 (-1)) 1`, the normalized deviation against `shiftedPairWeilEnergy a`
is `-((2^a + 2^{-a}) * log 2 / √2)`, which for `a ≠ 0` is strictly more negative than the canonical
node-`2` deletion price `-2 * log 2 / √2`. -/
theorem shiftedPair_deviation_single_pairTestFn_two (a : ℝ) :
    let c := Finsupp.single (pairTestFn 2 (-1)) (1 : ℝ)
    (nodeArchEnergy c - shiftedPairWeilEnergy a c) / massOf c =
      -(RHTower.shiftedPairVonMangoldt a 2 / Real.sqrt 2) ∧
    (a ≠ 0 →
      (nodeArchEnergy c - shiftedPairWeilEnergy a c) / massOf c <
        -(2 * (Real.log 2 / Real.sqrt 2))) := by
  intro c
  have hm2 : 2 ≤ (2 : ℕ) := le_rfl
  have hpos : 0 < massOf c := by
    dsimp only [c]
    rw [massOf_single_pairTestFn hm2 (by norm_num)]
    linarith [integral_narrowBump_sq_pos 2]
  have hb : ∀ j : LogIndex, j ≠ ⟨2, hm2⟩ → nodeVector c j = 0 := by
    intro j hj
    exact blindOn_single_pairTestFn hm2 (-1) ({2} : Set ℕ)ᶜ (by simp) j
      (fun h => hj (Subtype.ext h))
  have hsum : linearCombination ℝ (fun j : LogIndex => RHTower.shiftedPairVonMangoldt a (j : ℕ))
      (nodeVector c) = RHTower.shiftedPairVonMangoldt a 2 * nodeVector c ⟨2, hm2⟩ := by
    rw [linearCombination_apply,
      Finsupp.sum_eq_single (⟨2, hm2⟩ : LogIndex) (fun j _ hj => by rw [hb j hj, zero_smul])
        (fun _ => zero_smul _ _),
      smul_eq_mul, mul_comm]
  have hdev : (nodeArchEnergy c - shiftedPairWeilEnergy a c) / massOf c =
      -(RHTower.shiftedPairVonMangoldt a 2 / Real.sqrt 2) := by
    rw [nodeArchEnergy_eq_shiftedPairWeilEnergy_add a c, add_sub_cancel_left, hsum]
    dsimp only [c] at hpos ⊢
    rw [nodeVector_single_pairTestFn hm2 (by norm_num : (-1 : ℝ) ^ 2 = 1)]
    have hne : massOf (Finsupp.single (pairTestFn 2 (-1)) 1) ≠ 0 := hpos.ne'
    calc RHTower.shiftedPairVonMangoldt a 2 *
          (-1 * massOf (Finsupp.single (pairTestFn 2 (-1)) 1) / Real.sqrt 2) /
          massOf (Finsupp.single (pairTestFn 2 (-1)) 1)
        = -(RHTower.shiftedPairVonMangoldt a 2 / Real.sqrt 2) *
            (massOf (Finsupp.single (pairTestFn 2 (-1)) 1) /
              massOf (Finsupp.single (pairTestFn 2 (-1)) 1)) := by ring
      _ = -(RHTower.shiftedPairVonMangoldt a 2 / Real.sqrt 2) := by
        rw [div_self hne, mul_one]
  refine ⟨hdev, fun ha => ?_⟩
  rw [hdev, neg_lt_neg_iff]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hs2, RHTower.shiftedPairVonMangoldt,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
  have hgt : 2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) :=
    lt_of_not_ge fun hle => ha (RHTower.eq_zero_of_two_rpow_add_two_rpow_neg_le hle)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

/-- **Model 2 — Complete selectivity profile of the shifted pair `ζ(s - a)ζ(s + a)`.**
1. For every `a`, `shiftedPairVonMangoldt a` never lies in the full Weil cone `WeilPositiveFull`
   (`not_weilPositiveFull_shiftedPairVonMangoldt`), because its pole multiplicity is `2 ≠ 1` at
   `a = 0` and its prime weights exceed `2 Λ(n)` at `a ≠ 0`.
2. At pole multiplicity `2`, `WeilPositiveDegree 2 (shiftedPairVonMangoldt a) ↔ (RH ∧ a = 0)`
   (`weilPositiveDegree_two_shiftedPairVonMangoldt_iff`).
3. For `a ≠ 0`, `shiftedZetaPair a` has off-line zeros above any height `T`
   (`exists_offLine_zero_shiftedZetaPair`) and its Dirichlet coefficients violate the Ramanujan
   bound for every `ε < |a|` (`not_ramanujan_shiftedPairCoeff`). -/
theorem shiftedPair_leaves_weilCone_and_ramanujan (a : ℝ) :
    ¬ RHTower.WeilPositiveFull (RHTower.shiftedPairVonMangoldt a) ∧
      (RHTower.WeilPositiveDegree 2 (RHTower.shiftedPairVonMangoldt a) ↔
        RiemannHypothesis ∧ a = 0) ∧
      (a ≠ 0 →
        (∀ T : ℝ, ∃ s : ℂ, T < s.im ∧ s.re ≠ 1 / 2 ∧ RHTower.shiftedZetaPair a s = 0) ∧
        (∀ ε : ℝ, ε < |a| →
          ¬ ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → RHTower.shiftedPairCoeff a n ≤ C * (n : ℝ) ^ ε)) :=
  ⟨RHTower.not_weilPositiveFull_shiftedPairVonMangoldt a,
    RHTower.weilPositiveDegree_two_shiftedPairVonMangoldt_iff a,
    fun ha => ⟨fun T => RHTower.exists_offLine_zero_shiftedZetaPair ha T,
      fun _ hε => RHTower.not_ramanujan_shiftedPairCoeff hε⟩⟩

/-- **Model 3 — Beurling node-deletion, primes-only, gapped, sub-square-root density, and admixture
calibration battery.**
1. *Primes-only cone*: `zeroPoleBlindSymbolValue {p | p.Prime} < 0` and
   `zeroPoleBlindLevyInfimum {p | p.Prime} < |EF.gammaBracket 0|` unconditionally (since `4` is a
   prime power but not prime).
2. *Node-`4` deletion cone*: `zeroPoleBlindSymbolValue (Set.univ \ {4}) < 0` and
   `zeroPoleBlindLevyInfimum (Set.univ \ {4}) < |EF.gammaBracket 0|` unconditionally.
3. *Sub-square-root density and two power towers*: on `powerNodes q₁ ∪ powerNodes q₂`, the
   zero-pole constraint is invisible (`zeroPoleBlindSymbolValue = blindSymbolValue < 0`).
4. *Admixture rigidity*: for any `t ≠ 1`, `WeilPositiveFull (fun n => t * Λ(n) + (1 - t) * lam₀ n)`
   holds iff `RiemannHypothesis` holds and `lam₀ = Λ` on `n ≥ 2`. -/
theorem beurling_and_admixture_calibration_battery (q₁ q₂ : ℕ) {t : ℝ} (ht : t ≠ 1)
    (lam₀ : ℕ → ℝ) :
    (zeroPoleBlindSymbolValue {p : ℕ | p.Prime} < 0 ∧
      zeroPoleBlindLevyInfimum {p : ℕ | p.Prime} < |EF.gammaBracket 0|) ∧
    (zeroPoleBlindSymbolValue (Set.univ \ {4}) < 0 ∧
      zeroPoleBlindLevyInfimum (Set.univ \ {4}) < |EF.gammaBracket 0|) ∧
    (zeroPoleBlindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) =
      blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂)) ∧
    (RHTower.WeilPositiveFull
        (fun n => t * (ArithmeticFunction.vonMangoldt n : ℝ) + (1 - t) * lam₀ n) ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam₀ n = ArithmeticFunction.vonMangoldt n) :=
  ⟨zeroPoleBlindSymbolValue_neg_of_missing_primePow (m := 4) (by decide) (by decide),
    zeroPoleBlindSymbolValue_neg_of_missing_primePow (m := 4) (by decide) (by simp),
    zeroPoleBlindSymbolValue_two_towers_eq q₁ q₂,
    RHTower.weilPositiveFull_admixture_iff ht lam₀⟩

end

end GaloisForLFunctions.BiScaleUncertainty
