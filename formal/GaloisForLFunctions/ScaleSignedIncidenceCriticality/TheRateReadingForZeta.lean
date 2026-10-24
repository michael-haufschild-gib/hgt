import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRateIsACofinalInvariant
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheBoundedApertureRateCertifiesNothing
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw
import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsALandauExponent
import GaloisForLFunctions.SquareRootThreshold.TheReceiverDampingReadsTheZeroWidth
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster

/-!
# The Rate Reading for `ζ`

The faithful scale-free reading of the depth on the lattice family is the exponential growth rate
of the deficit (`sInf_rateSet`). For `ζ`, that rate is the zero width `zetaZeroWidth = sup |Re ρ − ½|`.
This module resolves Open Problem 4 of `ScaleSignedIncidenceCriticality` by pricing the local
off-line zero count against the certificate alone at both a single aperture and in the asymptotic
rate limit, and by unifying the rate readings across the aperture, lag, Chebyshev, band, and
damping faces into one floor theorem:

1. **Five-Currency Unification and Clustering Dichotomy for `ζ` (§1).**
   Four asymptotic rate currencies — the dyadic prime-window lag rate `sInf (zetaLagRates w)`,
   the integrated Chebyshev deficit rate `sInf deficitAbsRates`, the mean-square band rate
   `sInf bandRates`, and the Möbius receiver damping threshold `receiverDampingRate` — are
   unconditionally equal to `zetaZeroWidth` (`five_rate_currencies_of_zeta`). The fifth currency,
   the polar restricted Weil ground-energy rate `polarGroundEnergyRate`, satisfies
   `zetaZeroWidth ≤ polarGroundEnergyRate ≤ 1 / 2` unconditionally and equals `zetaZeroWidth`
   whenever the off-line zeros have bounded local count `OffLineCopiesLocallyBounded M` or bounded
   local squared-depth mass `OffLineDepthLocallyBounded W` on unit height windows.

2. **Single-Aperture Pricing of the Local Off-Line Count (§2).**
   Under `OffLineCopiesLocallyBounded M` (`0 < M`), a ground-energy deficit
   `ccmRestrictedWeilGroundEnergy A ≤ -η` (`0 < η`) at a single aperture `A` forces the explicit
   width lower bound
   `singleApertureWidthFloor M A.1 η = log (η / (M (2A + 2π) e^{2π})) / (2A) ≤ zetaZeroWidth`
   (`singleApertureWidthFloor_le_zetaZeroWidth`), and similarly under `OffLineDepthLocallyBounded W`
   (`singleApertureDepthMassFloor_le_zetaZeroWidth`). In the SSIC reading calculus on
   `ApertureCountDatum A`, a reading that sees the single-aperture deficit `η` alone without the
   local count `M` has exact width resolution floor `0` (`resolutionFloor_width_deficitOnly_eq_zero`),
   whereas adjoining the local count lifts the floor to
   `max 0 (singleApertureWidthFloor d.count A d.deficit)`
   (`le_resolutionFloor_width_deficitAndCount`).

3. **Asymptotic Rate Pricing of the Local Off-Line Count (§3).**
   On the space `ZetaRateDatum` of admissible pairs `(width, polarRate, locallyBounded)` governed
   by the `SquareRootThreshold` laws:
   * Reading `width` alone (for `0 < width`) leaves `polarRate` with resolution limit `1 / 2`,
     resolution floor `width`, and resolution interval `[width, 1 / 2]`
     (`resolutionLimit_polarRate_widthOnly`, `resolutionInterval_polarRate_widthOnly`); adjoining
     the local-count datum `locallyBounded` collapses the limit from `1 / 2` to `width`
     (`resolutionLimit_polarRate_widthAndLocalCount`).
   * Dually, reading `polarRate` alone (for `0 < polarRate`) leaves `width` with resolution limit
     `polarRate` and resolution floor `0` (`resolutionFloor_width_polarRateOnly_eq_zero`); adjoining
     the local-count datum lifts the resolution floor from `0` to `polarRate`
     (`resolutionFloor_width_polarRateAndLocalCount`).

4. **Universal Cofinal-Faithfulness and Bounded-Range Floor Law on the Lattice Rate Face (§4).**
   Without any convexity hypothesis, on the actual two-coordinate lattice family `ScaleDepthDatum`:
   * Sampling the exponential rate bound on *any* cofinal aperture set `S : CofinalApertures`
     (`cofinalRateSet S`) preserves the exact infimum `sInf (cofinalRateSet S p) = sdDepth p` and is
     **faithful** for `sdDepth` (`faithful_sdDepth_cofinalRateSet`).
   * Restricting the rate bound to *any* bounded aperture range `(0, M]` (`boundedRateSet M`)
     collapses the rate set to `Ici 0` for every datum (`boundedRateSet_eq_Ici_zero`), giving
     `sInf = 0`, exact resolution limit `1 / 2` (`resolutionLimit_sdDepth_boundedRateSet_eq_half`),
     and exact resolution floor `0` (`resolutionFloor_sdDepth_boundedRateSet_eq_zero`).
-/

open Set Filter Topology Real
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

noncomputable section
set_option autoImplicit false

/-! ### 1. Five-Currency Unification and Clustering Dichotomy for `ζ` -/

/-- **Five-currency rate unification for `ζ`.**
The dyadic prime-window lag rate (off a countable exceptional set of widths `w ∈ (0, ½ log 2)`),
the integrated Chebyshev deficit rate, the mean-square band rate, and the Möbius receiver damping
rate all equal `zetaZeroWidth` unconditionally; the polar ground-energy rate dominates
`zetaZeroWidth`, lies in `[0, 1/2]`, vanishes iff `RiemannHypothesis`, and equals `zetaZeroWidth`
whenever the off-line copies or their squared depths are locally bounded on unit height windows. -/
theorem five_rate_currencies_of_zeta :
    (∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      sInf (zetaLagRates w) = zetaZeroWidth) ∧
    sInf deficitAbsRates = zetaZeroWidth ∧
    sInf bandRates = zetaZeroWidth ∧
    receiverDampingRate = zetaZeroWidth ∧
    zetaZeroWidth ≤ polarGroundEnergyRate ∧
    polarGroundEnergyRate ≤ 1 / 2 ∧
    (RiemannHypothesis ↔ polarGroundEnergyRate = 0) ∧
    (∀ M : ℕ, OffLineCopiesLocallyBounded M → polarGroundEnergyRate = zetaZeroWidth) ∧
    (∀ W : ℝ, OffLineDepthLocallyBounded W → polarGroundEnergyRate = zetaZeroWidth) ∧
    (polarGroundEnergyRate = zetaZeroWidth ∨ ∀ W : ℝ, ¬ OffLineDepthLocallyBounded W) := by
  obtain ⟨E, hE, hlag⟩ := zetaZeroWidth_eq_sInf_zetaLagRates
  exact ⟨⟨E, hE, fun w hw hw2 hwE => (hlag w hw hw2 hwE).symm⟩,
    zetaZeroWidth_eq_sInf_deficitAbsRates.symm,
    zetaZeroWidth_eq_sInf_bandRates.symm,
    receiverDampingRate_eq_zetaZeroWidth,
    zetaZeroWidth_le_polarGroundEnergyRate,
    polarGroundEnergyRate_le_half,
    riemannHypothesis_iff_polarGroundEnergyRate_eq_zero,
    fun _ hM => polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded hM,
    fun _ hW => polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded hW,
    polarGroundEnergyRate_eq_zetaZeroWidth_or_depthMass_clusters⟩

/-! ### 2. Single-Aperture Pricing of the Local Off-Line Count -/

/-- The explicit width lower bound certified at a single aperture `A` by a ground-energy deficit
`η` together with a local off-line copy bound `M`:
`log (η / (M (2A + 2π) e^{2π})) / (2A)`. -/
def singleApertureWidthFloor (M : ℕ) (A η : ℝ) : ℝ :=
  Real.log (η / ((M : ℝ) * ((2 * A + 2 * Real.pi) * Real.exp (2 * Real.pi)))) / (2 * A)

/-- The explicit width lower bound certified at a single aperture `A` by a ground-energy deficit
`η` together with a local squared-depth mass bound `W`:
`log (η / (A² (2A + 2π) e^{2π} W)) / (2A)`. -/
def singleApertureDepthMassFloor (W A η : ℝ) : ℝ :=
  Real.log (η / (A ^ 2 * ((2 * A + 2 * Real.pi) * Real.exp (2 * Real.pi)) * W)) / (2 * A)

/-- **Single-aperture width floor from a local copy bound.**
If `OffLineCopiesLocallyBounded M` (`0 < M`) holds and `ccmRestrictedWeilGroundEnergy A ≤ -η`
(`0 < η`), then `singleApertureWidthFloor M A.1 η ≤ zetaZeroWidth`. -/
theorem singleApertureWidthFloor_le_zetaZeroWidth
    {M : ℕ} (hM0 : 0 < M) (hM : OffLineCopiesLocallyBounded M)
    (A : SuzukiPositiveAperture) {η : ℝ} (hη : 0 < η)
    (hdef : ccmRestrictedWeilGroundEnergy A ≤ -η) :
    singleApertureWidthFloor M A.1 η ≤ zetaZeroWidth := by
  have hA : 0 < A.1 := A.2
  have hfl := neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy hM A
  have hle : η ≤ clusterFloorConst M A.1 := by linarith
  set D : ℝ := (M : ℝ) * ((2 * A.1 + 2 * Real.pi) * Real.exp (2 * Real.pi))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hD : 0 < D := by positivity
  have hcluster : clusterFloorConst M A.1 = D * Real.exp (2 * zetaZeroWidth * A.1) := by
    unfold clusterFloorConst; ring
  rw [hcluster] at hle
  have hdiv : η / D ≤ Real.exp (2 * zetaZeroWidth * A.1) := (div_le_iff₀ hD).mpr (by linarith)
  have hlog := Real.log_le_log (div_pos hη hD) hdiv
  rw [Real.log_exp] at hlog
  rw [singleApertureWidthFloor, div_le_iff₀ (by linarith : 0 < 2 * A.1)]
  linarith

/-- **Single-aperture width floor from a local depth-mass bound.**
If `OffLineDepthLocallyBounded W` (`0 < W`) holds and `ccmRestrictedWeilGroundEnergy A ≤ -η`
(`0 < η`), then `singleApertureDepthMassFloor W A.1 η ≤ zetaZeroWidth`. -/
theorem singleApertureDepthMassFloor_le_zetaZeroWidth
    {W : ℝ} (hW0 : 0 < W) (hW : OffLineDepthLocallyBounded W)
    (A : SuzukiPositiveAperture) {η : ℝ} (hη : 0 < η)
    (hdef : ccmRestrictedWeilGroundEnergy A ≤ -η) :
    singleApertureDepthMassFloor W A.1 η ≤ zetaZeroWidth := by
  have hA : 0 < A.1 := A.2
  have hfl := neg_depthFloorConst_le_ccmRestrictedWeilGroundEnergy hW A
  have hle : η ≤ depthFloorConst W A.1 := by linarith
  set D : ℝ := A.1 ^ 2 * ((2 * A.1 + 2 * Real.pi) * Real.exp (2 * Real.pi)) * W
  have hpi : 0 < Real.pi := Real.pi_pos
  have hD : 0 < D := by positivity
  have hdepth : depthFloorConst W A.1 = D * Real.exp (2 * zetaZeroWidth * A.1) := by
    unfold depthFloorConst; ring
  rw [hdepth] at hle
  have hdiv : η / D ≤ Real.exp (2 * zetaZeroWidth * A.1) := (div_le_iff₀ hD).mpr (by linarith)
  have hlog := Real.log_le_log (div_pos hη hD) hdiv
  rw [Real.log_exp] at hlog
  rw [singleApertureDepthMassFloor, div_le_iff₀ (by linarith : 0 < 2 * A.1)]
  linarith

/-- A single-aperture datum pairing a width `width ∈ [0, 1/2]`, a positive local off-line count
`count`, and an observed ground-energy deficit `deficit ≥ 0` obeying the sampling inequality
`deficit ≤ clusterFloorConst count A` at aperture `A > 0`. -/
structure ApertureCountDatum (A : ℝ) where
  width : ℝ
  count : ℕ
  deficit : ℝ
  width_nonneg : 0 ≤ width
  width_le_half : width ≤ 1 / 2
  count_pos : 0 < count
  deficit_nonneg : 0 ≤ deficit
  sampling_bound :
    deficit ≤ (count : ℝ) * ((2 * A + 2 * Real.pi) * Real.exp (2 * Real.pi) *
      Real.exp (2 * width * A))

theorem bddBelow_width_shadow_apertureCountDatum {A : ℝ} {O : Type*}
    (r : ApertureCountDatum A → O) (d : ApertureCountDatum A) :
    BddBelow (ApertureCountDatum.width '' shadow r d) :=
  ⟨0, by rintro _ ⟨e, -, rfl⟩; exact e.width_nonneg⟩

/-- **Without the local count, a single-aperture deficit certifies no positive width floor.**
Under `ApertureCountDatum.deficit` alone, any observed deficit `η ≥ 0` can be produced by a
zero-width (or arbitrarily shallow) configuration with a sufficiently large local count `M`, so
the resolution floor of `width` is `0`. -/
theorem resolutionFloor_width_deficitOnly_eq_zero {A : ℝ} (hA : 0 < A)
    (d : ApertureCountDatum A) :
    resolutionFloor ApertureCountDatum.width ApertureCountDatum.deficit d = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set B : ℝ := (2 * A + 2 * Real.pi) * Real.exp (2 * Real.pi)
  have hB : 0 < B := by positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (d.deficit / B)
  have hMpos : 0 < M := by
    have : 0 ≤ d.deficit / B := div_nonneg d.deficit_nonneg hB.le
    have hlt : (0 : ℝ) < M := lt_of_le_of_lt this hM
    exact_mod_cast hlt
  have hbd : d.deficit ≤ (M : ℝ) * (B * Real.exp (2 * 0 * A)) := by
    rw [mul_zero, zero_mul, Real.exp_zero, mul_one]
    exact (div_lt_iff₀ hB).mp hM |>.le
  let d₀ : ApertureCountDatum A :=
    ⟨0, M, d.deficit, le_rfl, by norm_num, hMpos, d.deficit_nonneg, hbd⟩
  have hmem : d₀ ∈ shadow ApertureCountDatum.deficit d := rfl
  refine le_antisymm ?_ ?_
  · exact csInf_le (bddBelow_width_shadow_apertureCountDatum _ d) ⟨d₀, hmem, rfl⟩
  · exact le_csInf (shadow_image_nonempty _ _ d) (by rintro _ ⟨e, -, rfl⟩; exact e.width_nonneg)

/-- **Adjoining the local count lifts the single-aperture width floor.**
Under the joint reading `joinReading ApertureCountDatum.deficit ApertureCountDatum.count`, any
positive deficit `0 < d.deficit` certifies the lower bound
`max 0 (singleApertureWidthFloor d.count A d.deficit) ≤ resolutionFloor`. -/
theorem le_resolutionFloor_width_deficitAndCount {A : ℝ} (hA : 0 < A)
    (d : ApertureCountDatum A) (hdef : 0 < d.deficit) :
    max 0 (singleApertureWidthFloor d.count A d.deficit) ≤
      resolutionFloor ApertureCountDatum.width
        (joinReading ApertureCountDatum.deficit ApertureCountDatum.count) d := by
  rw [← certifiesLower_iff_le_resolutionFloor (bddBelow_width_shadow_apertureCountDatum _ d)]
  intro e he
  obtain ⟨hdef_eq, hcnt_eq⟩ := (shadow_joinReading _ _ d).subset he
  change e.deficit = d.deficit at hdef_eq
  change e.count = d.count at hcnt_eq
  refine max_le e.width_nonneg ?_
  have hpi : 0 < Real.pi := Real.pi_pos
  have hMpos : (0 : ℝ) < d.count := by exact_mod_cast d.count_pos
  set D : ℝ := (d.count : ℝ) * ((2 * A + 2 * Real.pi) * Real.exp (2 * Real.pi))
  have hD : 0 < D := by positivity
  have hbd := e.sampling_bound
  rw [hdef_eq, hcnt_eq] at hbd
  have hdiv : d.deficit / D ≤ Real.exp (2 * e.width * A) := by
    rw [div_le_iff₀ hD]
    linarith
  have hlog := Real.log_le_log (div_pos hdef hD) hdiv
  rw [Real.log_exp] at hlog
  rw [singleApertureWidthFloor, div_le_iff₀ (by linarith : 0 < 2 * A)]
  linarith

/-! ### 3. Asymptotic Rate Pricing of the Local Off-Line Count -/

/-- The asymptotic rate-datum space governed by the proven laws of `SquareRootThreshold`:
* `0 ≤ width ≤ polarRate ≤ 1 / 2` (`zetaZeroWidth_le_polarGroundEnergyRate`,
  `polarGroundEnergyRate_le_half`),
* `width = 0 ↔ polarRate = 0` (`riemannHypothesis_iff_polarGroundEnergyRate_eq_zero`),
* `locallyBounded = true → polarRate = width`
  (`polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded`). -/
structure ZetaRateDatum where
  width : ℝ
  polarRate : ℝ
  locallyBounded : Bool
  width_nonneg : 0 ≤ width
  width_le_polarRate : width ≤ polarRate
  polarRate_le_half : polarRate ≤ 1 / 2
  zero_iff_zero : width = 0 ↔ polarRate = 0
  eq_of_locallyBounded : locallyBounded = true → polarRate = width

/-- The canonical rate datum of `ζ` under a local off-line copy bound `OffLineCopiesLocallyBounded M`. -/
def actualZetaRateDatumOfLocallyBounded {M : ℕ} (hM : OffLineCopiesLocallyBounded M) :
    ZetaRateDatum where
  width := zetaZeroWidth
  polarRate := polarGroundEnergyRate
  locallyBounded := true
  width_nonneg := zetaZeroWidth_nonneg
  width_le_polarRate := zetaZeroWidth_le_polarGroundEnergyRate
  polarRate_le_half := polarGroundEnergyRate_le_half
  zero_iff_zero := by
    rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero,
      riemannHypothesis_iff_polarGroundEnergyRate_eq_zero]
  eq_of_locallyBounded := fun _ =>
    polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded hM

theorem bddAbove_polarRate_shadow {O : Type*} (r : ZetaRateDatum → O) (d : ZetaRateDatum) :
    BddAbove (ZetaRateDatum.polarRate '' shadow r d) :=
  ⟨1 / 2, by rintro _ ⟨e, -, rfl⟩; exact e.polarRate_le_half⟩

theorem bddBelow_polarRate_shadow {O : Type*} (r : ZetaRateDatum → O) (d : ZetaRateDatum) :
    BddBelow (ZetaRateDatum.polarRate '' shadow r d) :=
  ⟨0, by rintro _ ⟨e, -, rfl⟩; exact e.width_nonneg.trans e.width_le_polarRate⟩

theorem bddAbove_width_shadow {O : Type*} (r : ZetaRateDatum → O) (d : ZetaRateDatum) :
    BddAbove (ZetaRateDatum.width '' shadow r d) :=
  ⟨1 / 2, by rintro _ ⟨e, -, rfl⟩; exact e.width_le_polarRate.trans e.polarRate_le_half⟩

theorem bddBelow_width_shadow {O : Type*} (r : ZetaRateDatum → O) (d : ZetaRateDatum) :
    BddBelow (ZetaRateDatum.width '' shadow r d) :=
  ⟨0, by rintro _ ⟨e, -, rfl⟩; exact e.width_nonneg⟩

/-- **Without the local count, reading a positive width certifies no polar ground-energy rate
below `1 / 2`.** -/
theorem resolutionLimit_polarRate_widthOnly {d : ZetaRateDatum} (hd : 0 < d.width) :
    resolutionLimit ZetaRateDatum.polarRate ZetaRateDatum.width d = 1 / 2 := by
  let e : ZetaRateDatum :=
    ⟨d.width, 1 / 2, false, d.width_nonneg,
      d.width_le_polarRate.trans d.polarRate_le_half, le_rfl,
      ⟨fun h => absurd h hd.ne', fun h => by norm_num at h⟩,
      fun h => by cases h⟩
  exact resolutionLimit_eq_of_mem_shadow_of_max
    (fun x => x.polarRate_le_half) (rfl : e ∈ shadow ZetaRateDatum.width d) rfl

theorem resolutionFloor_polarRate_widthOnly (d : ZetaRateDatum) :
    resolutionFloor ZetaRateDatum.polarRate ZetaRateDatum.width d = d.width := by
  let e : ZetaRateDatum :=
    ⟨d.width, d.width, true, d.width_nonneg, le_rfl,
      d.width_le_polarRate.trans d.polarRate_le_half, Iff.rfl, fun _ => rfl⟩
  refine le_antisymm ?_ ?_
  · exact csInf_le (bddBelow_polarRate_shadow _ d) ⟨e, rfl, rfl⟩
  · refine le_csInf (shadow_image_nonempty _ _ d) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← mem_shadow_iff.mp hx]
    exact x.width_le_polarRate

/-- **The resolution interval of `polarRate` under `width` alone is `[d.width, 1 / 2]`.** -/
theorem resolutionInterval_polarRate_widthOnly {d : ZetaRateDatum} (hd : 0 < d.width) :
    resolutionInterval ZetaRateDatum.polarRate ZetaRateDatum.width d =
      Set.Icc d.width (1 / 2) := by
  rw [resolutionInterval, resolutionFloor_polarRate_widthOnly,
    resolutionLimit_polarRate_widthOnly hd]

/-- **Adjoining the local-count datum collapses the resolution limit of `polarRate` from `1 / 2`
to `d.width`.** -/
theorem resolutionLimit_polarRate_widthAndLocalCount {d : ZetaRateDatum}
    (hloc : d.locallyBounded = true) :
    resolutionLimit ZetaRateDatum.polarRate
      (joinReading ZetaRateDatum.width ZetaRateDatum.locallyBounded) d = d.width := by
  refine le_antisymm ?_ ?_
  · rw [← certifies_iff_resolutionLimit_le (bddAbove_polarRate_shadow _ d)]
    intro e he
    obtain ⟨hw, hl⟩ := (shadow_joinReading _ _ d).subset he
    change e.width = d.width at hw
    change e.locallyBounded = d.locallyBounded at hl
    rw [e.eq_of_locallyBounded (hl.trans hloc), hw]
  · rw [← d.eq_of_locallyBounded hloc]
    exact le_resolutionLimit (bddAbove_polarRate_shadow _ d)

/-- **Dually, reading `polarRate` alone has width resolution limit `d.polarRate` and floor `0`.**
Without the local count, a positive ground-energy rate `d.polarRate > 0` can arise from
arbitrarily small positive widths `0 < ε ≤ d.polarRate` that cluster on unit windows. -/
theorem resolutionLimit_width_polarRateOnly (d : ZetaRateDatum) :
    resolutionLimit ZetaRateDatum.width ZetaRateDatum.polarRate d = d.polarRate := by
  let e : ZetaRateDatum :=
    ⟨d.polarRate, d.polarRate, true,
      d.width_nonneg.trans d.width_le_polarRate, le_rfl, d.polarRate_le_half, Iff.rfl,
      fun _ => rfl⟩
  refine le_antisymm ?_ ?_
  · rw [← certifies_iff_resolutionLimit_le (bddAbove_width_shadow _ d)]
    intro x hx
    rw [← mem_shadow_iff.mp hx]
    exact x.width_le_polarRate
  · exact le_csSup (bddAbove_width_shadow _ d) ⟨e, rfl, rfl⟩

theorem resolutionFloor_width_polarRateOnly_eq_zero (d : ZetaRateDatum) :
    resolutionFloor ZetaRateDatum.width ZetaRateDatum.polarRate d = 0 := by
  refine le_antisymm ?_ (le_csInf (shadow_image_nonempty _ _ d)
    (by rintro _ ⟨x, -, rfl⟩; exact x.width_nonneg))
  rcases eq_or_lt_of_le (d.width_nonneg.trans d.width_le_polarRate) with h0 | hpos
  · have hd0 : d.width = 0 := le_antisymm (d.width_le_polarRate.trans h0.symm.le) d.width_nonneg
    exact hd0 ▸ resolutionFloor_le (bddBelow_width_shadow _ d)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    set w := min (ε / 2) d.polarRate
    have hw0 : 0 < w := lt_min (by linarith) hpos
    have hwle : w ≤ d.polarRate := min_le_right _ _
    let e : ZetaRateDatum :=
      ⟨w, d.polarRate, false, hw0.le, hwle, d.polarRate_le_half,
        ⟨fun h => absurd h hw0.ne', fun h => absurd h hpos.ne'⟩,
        fun h => by cases h⟩
    have hfl : resolutionFloor ZetaRateDatum.width ZetaRateDatum.polarRate d ≤ w :=
      csInf_le (bddBelow_width_shadow _ d) ⟨e, rfl, rfl⟩
    have hwε : w ≤ ε := (min_le_left _ _).trans (by linarith)
    exact hfl.trans hwε

/-- **Adjoining the local-count datum lifts the resolution floor of `width` under `polarRate` from
`0` to `d.polarRate`.** -/
theorem resolutionFloor_width_polarRateAndLocalCount {d : ZetaRateDatum}
    (hloc : d.locallyBounded = true) :
    resolutionFloor ZetaRateDatum.width
      (joinReading ZetaRateDatum.polarRate ZetaRateDatum.locallyBounded) d = d.polarRate := by
  refine le_antisymm ?_ ?_
  · rw [d.eq_of_locallyBounded hloc]
    exact resolutionFloor_le (bddBelow_width_shadow _ d)
  · rw [← certifiesLower_iff_le_resolutionFloor (bddBelow_width_shadow _ d)]
    intro e he
    obtain ⟨hp, hl⟩ := (shadow_joinReading _ _ d).subset he
    change e.polarRate = d.polarRate at hp
    change e.locallyBounded = d.locallyBounded at hl
    rw [← hp, ← e.eq_of_locallyBounded (hl.trans hloc)]

/-! ### 4. Universal Cofinal-Faithfulness and Bounded-Range Floor Law on the Lattice Rate Face -/

/-- The rate condition `WeilFloorAtLevel Z.1 a (C * e^{2βa})` sampled only on a cofinal aperture
set `S : CofinalApertures`. -/
def cofinalDeficitRateBelow (S : CofinalApertures) (β : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a ∈ S.carrier, WeilFloorAtLevel Z.1 a (C * Real.exp (2 * β * a))

/-- The set of nonnegative rates certified on a cofinal aperture set `S`. -/
def cofinalRateSet (S : CofinalApertures) (p : ScaleDepthDatum) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ cofinalDeficitRateBelow S β (offLineLattice p.2.1 p.2.2.1 p.2.2.2)}

/-- Every rate above `sdDepth p` is certified on `S`. -/
theorem mem_cofinalRateSet_of_lt (S : CofinalApertures) {p : ScaleDepthDatum} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : sdDepth p < β) :
    β ∈ cofinalRateSet S p := by
  obtain ⟨C, hC, hall⟩ := deficitRateBelow_of_lt p.2.1 p.2.2.1 p.2.2.2 hβ
  exact ⟨hβ0, C, hC, fun a ha => hall a (S.pos a ha)⟩

/-- No nonnegative rate below `sdDepth p` can hold even along a cofinal aperture set `S`. -/
theorem notMem_cofinalRateSet_of_lt (S : CofinalApertures) {p : ScaleDepthDatum} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < sdDepth p) :
    β ∉ cofinalRateSet S p := by
  rintro ⟨_, C, hC, hall⟩
  set L : ℝ := p.1.1
  set δ : ℝ := p.1.2
  change β < δ at hβ
  have hL : 0 < L := p.2.1
  have hδ : 0 < δ := p.2.2.1
  have hδ' : δ ≤ 1 / 2 := p.2.2.2
  set A : ℝ := L * Real.exp (-(δ * L)) with hA
  set c : ℝ := 2 * (δ - β) with hc
  have hA0 : 0 < A := by rw [hA]; positivity
  have hc0 : 0 < c := by rw [hc]; linarith
  set a₀ : ℝ := max (L + 1) (4 * (2 + C + L) / (A * c ^ 2))
  obtain ⟨a, haS, ha₀⟩ := S.cofinal a₀
  have haL1 : L + 1 ≤ a := (le_max_left _ _).trans ha₀
  have haL : L / 2 < a := by linarith
  have ha0 : 0 < a := S.pos a haS
  have hbig : 4 * (2 + C + L) / (A * c ^ 2) ≤ a := (le_max_right _ _).trans ha₀
  have hslack : 2 + C + L ≤ A * c ^ 2 * a / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < A * c ^ 2)).mp hbig
    nlinarith [h]
  have hquad : 1 + c * a + (c * a) ^ 2 / 4 ≤ Real.exp (c * a) :=
    one_add_add_sq_quarter_le_exp (by positivity)
  have hkey : C + 2 * a + L < A * Real.exp (c * a) := by
    have h1 : A * (1 + c * a + (c * a) ^ 2 / 4) ≤ A * Real.exp (c * a) :=
      mul_le_mul_of_nonneg_left hquad hA0.le
    have h2 : a * (2 + C + L) ≤ a * (A * c ^ 2 * a / 4) :=
      mul_le_mul_of_nonneg_left hslack ha0.le
    have h3 : 0 < A * c * a := by positivity
    have h4 : 0 ≤ (a - 1) * (C + L) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, h3, h4]
  have hE0 : (0 : ℝ) < Real.exp (2 * β * a) := Real.exp_pos _
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * β * a) := Real.one_le_exp (by positivity)
  have hid : Real.exp (δ * (2 * a - L)) =
      Real.exp (-(δ * L)) * (Real.exp (c * a) * Real.exp (2 * β * a)) := by
    rw [← Real.exp_add, ← Real.exp_add, hc]
    congr 1; ring
  have hLHS : L * Real.exp (δ * (2 * a - L)) = (A * Real.exp (c * a)) * Real.exp (2 * β * a) := by
    rw [hid, hA]; ring
  have hlow : C * Real.exp (2 * β * a) < L * Real.exp (δ * (2 * a - L)) - 2 * a - L := by
    rw [hLHS]
    have hmul := mul_lt_mul_of_pos_right hkey hE0
    have hslack2 : 0 ≤ (2 * a + L) * (Real.exp (2 * β * a) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hmul, hslack2]
  exact not_weilFloorAtLevel_offLineLattice_of_lt_exp hL hδ hδ' haL hlow (hall a haS)

/-- **Cofinal sampling preserves the exact infimum rate on `ScaleDepthDatum` without any convexity
assumption.** -/
theorem sInf_cofinalRateSet (S : CofinalApertures) (p : ScaleDepthDatum) :
    sInf (cofinalRateSet S p) = sdDepth p := by
  have hd : (0 : ℝ) < sdDepth p := p.2.2.1
  have hne : (cofinalRateSet S p).Nonempty :=
    ⟨sdDepth p + 1, mem_cofinalRateSet_of_lt S (by linarith) (by linarith)⟩
  have hlb : ∀ β ∈ cofinalRateSet S p, sdDepth p ≤ β := by
    intro β hβ
    by_contra hcon
    exact notMem_cofinalRateSet_of_lt S hβ.1 (not_le.mp hcon) hβ
  refine le_antisymm ?_ (le_csInf hne hlb)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le ⟨sdDepth p, hlb⟩ (mem_cofinalRateSet_of_lt S (by linarith) (by linarith))

/-- **Cofinal rate readings are faithful for `sdDepth` on `ScaleDepthDatum`.** -/
theorem faithful_sdDepth_cofinalRateSet (S : CofinalApertures) :
    Faithful sdDepth (cofinalRateSet S) := by
  have hbdd : ∀ p : ScaleDepthDatum, BddAbove (sdDepth '' shadow (cofinalRateSet S) p) :=
    fun p => ⟨1 / 2, by rintro _ ⟨q, -, rfl⟩; exact q.2.2.2⟩
  rw [faithful_iff hbdd]
  intro p q hq
  rw [← sInf_cofinalRateSet S q, ← sInf_cofinalRateSet S p, mem_shadow_iff.mp hq]

/-- The rate condition restricted to a bounded aperture range `0 < a ≤ M`. -/
def boundedDeficitRateBelow (M β : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ M →
    WeilFloorAtLevel Z.1 a (C * Real.exp (2 * β * a))

/-- The set of nonnegative rates certified on `(0, M]`. -/
def boundedRateSet (M : ℝ) (p : ScaleDepthDatum) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ boundedDeficitRateBelow M β (offLineLattice p.2.1 p.2.2.1 p.2.2.2)}

/-- **Every nonnegative rate is admissible on a bounded aperture range `(0, M]`.** -/
theorem boundedRateSet_eq_Ici_zero {M : ℝ} (hM : 0 < M) (p : ScaleDepthDatum) :
    boundedRateSet M p = Set.Ici 0 := by
  ext β
  simp only [boundedRateSet, Set.mem_setOf_eq, Set.mem_Ici]
  refine ⟨fun h => h.1, fun hβ0 => ⟨hβ0, ?_⟩⟩
  set L : ℝ := p.1.1
  set δ : ℝ := p.1.2
  have hL : 0 < L := p.2.1
  have hδ : 0 < δ := p.2.2.1
  have hδ' : δ ≤ 1 / 2 := p.2.2.2
  set C : ℝ := (2 * M + L) * Real.exp (2 * δ * M)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, fun a ha haM => ?_⟩
  intro f hf hfs hp hm
  have hup := weilFloorAtLevel_offLineLattice_exp hL hδ hδ' ha f hf hfs hp hm
  have h1 : 2 * a + L ≤ 2 * M + L := by linarith
  have h2 : Real.exp (2 * δ * a) ≤ Real.exp (2 * δ * M) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : (2 * a + L) * Real.exp (2 * δ * a) ≤ C :=
    mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have h4 : (1 : ℝ) ≤ Real.exp (2 * β * a) := Real.one_le_exp (by positivity)
  have h5 : C ≤ C * Real.exp (2 * β * a) := le_mul_of_one_le_right hC.le h4
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hstep : (2 * a + L) * Real.exp (2 * δ * a) * ∫ u, ‖f u‖ ^ 2 ≤
      C * Real.exp (2 * β * a) * ∫ u, ‖f u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (h3.trans h5) hint
  have hup' : -((2 * a + L) * Real.exp (2 * δ * a) * ∫ u, ‖f u‖ ^ 2) ≤
      ((offLineLattice hL hδ hδ').1.W f f).re := hup
  linarith

/-- On any bounded aperture range `(0, M]`, the measured rate collapses to `0`. -/
theorem sInf_boundedRateSet_eq_zero {M : ℝ} (hM : 0 < M) (p : ScaleDepthDatum) :
    sInf (boundedRateSet M p) = 0 := by
  rw [boundedRateSet_eq_Ici_zero hM p, csInf_Ici]

/-- **A bounded-range rate reading on `ScaleDepthDatum` has exact resolution limit `1 / 2`.** -/
theorem resolutionLimit_sdDepth_boundedRateSet_eq_half {M : ℝ} (hM : 0 < M)
    (p : ScaleDepthDatum) :
    resolutionLimit sdDepth (boundedRateSet M) p = 1 / 2 := by
  let p_max : ScaleDepthDatum := ⟨(1, 1 / 2), one_pos, by norm_num, le_rfl⟩
  refine resolutionLimit_eq_of_constant_reading
    (fun x y => by rw [boundedRateSet_eq_Ici_zero hM x, boundedRateSet_eq_Ici_zero hM y])
    (fun x => x.2.2.2) (e := p_max) rfl p

/-- **A bounded-range rate reading on `ScaleDepthDatum` has exact resolution floor `0`.** -/
theorem resolutionFloor_sdDepth_boundedRateSet_eq_zero {M : ℝ} (hM : 0 < M)
    (p : ScaleDepthDatum) :
    resolutionFloor sdDepth (boundedRateSet M) p = 0 := by
  have hbdd : BddBelow (sdDepth '' shadow (boundedRateSet M) p) :=
    ⟨0, by rintro _ ⟨q, -, rfl⟩; exact q.2.2.1.le⟩
  refine le_antisymm ?_ (le_csInf (shadow_image_nonempty _ _ p)
    (by rintro _ ⟨q, -, rfl⟩; exact q.2.2.1.le))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  set δ := min (ε / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  let q : ScaleDepthDatum := ⟨(1, δ), one_pos, hδ0, hδ2⟩
  have hmem : q ∈ shadow (boundedRateSet M) p := by
    simp only [mem_shadow_iff, boundedRateSet_eq_Ici_zero hM]
  have hfl : resolutionFloor sdDepth (boundedRateSet M) p ≤ δ :=
    csInf_le hbdd ⟨q, hmem, rfl⟩
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  exact hfl.trans hδε

end

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
