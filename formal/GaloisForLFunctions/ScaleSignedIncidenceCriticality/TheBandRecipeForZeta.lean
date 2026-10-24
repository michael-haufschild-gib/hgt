import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThreeBandsDefeatTheMass
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.SquareRootThreshold.NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths
import GaloisForLFunctions.SquareRootThreshold.UnimodularTwoBumpTestsDecideTheCriticalLine

/-!
# The Band Recipe for `ζ`: Two-Aperture Ratios and Unconditional Reachable Bounds

In `TwoAliasingBandsDetermineTheDepth` and `ThreeBandsDefeatTheMass`, the depth of a model lattice or
of an isolated off-line pair is read from ratios of ground energies or window moments at two
apertures (`t₃ / (2 t₂) - 1 = cosh(δL)` and `M(2a) / (2 M(a)) = cosh(2δa)`), whose critical value `1`
is attained on the critical line. For `ζ` itself, the corresponding magnitudes are the restricted
Weil ground energy `μ(A) = ccmRestrictedWeilGroundEnergy A` and the explicit-formula prime-window
functional `Re P_{w, v} = Re W_ζ(f_{w, v}, f_{w, v})` (which retains the prime sum, archimedean term,
and polar term).

This module constructs the exact two-aperture ratios for `ζ`, proves that their critical value `1` is
attained if and only if the zeros of `ζ` lie on the critical line, derives the unconditional abscissa
inversion law from their large-aperture growth, and establishes the unconditional bounds on them
reachable from the corpus's inputs:

1. **The two-aperture ground-energy ratio of `ζ` (`zetaTwoApertureRatio`).**
   Fix a reference aperture `A₀ ≤ 21/200`, where `μ(A₀) ≥ 1/30 > 0` unconditionally
   (`one_thirtieth_le_ccmRestrictedWeilGroundEnergy`), and define for any second aperture `A > 0`
   `zetaTwoApertureRatio A₀ A = (μ(A₀) - μ(A)) / μ(A₀) = 1 - μ(A) / μ(A₀)`.
   - `zetaTwoApertureRatio A₀` is monotone nondecreasing in `A`, vanishes at `A = A₀`, is
     nonnegative for `A ≥ A₀`, and unconditionally approaches `≥ 1` as `A → ∞`
     (`exists_one_sub_lt_zetaTwoApertureRatio`).
   - **Exact criticality on the line**: `RiemannHypothesis` holds if and only if
     `∀ A, zetaTwoApertureRatio A₀ A ≤ 1` (`riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one`),
     and if and only if `zetaTwoApertureRatio A₀ A → 1` as `A → ∞`
     (`riemannHypothesis_iff_tendsto_zetaTwoApertureRatio_one`).
   - Its clamped companion `zetaClampedTwoApertureRatio A₀ A = 1 - min(μ(A), 0) / μ(A₀)` satisfies
     `1 ≤ zetaClampedTwoApertureRatio A₀ A` unconditionally and attains the critical value `1` at
     every aperture if and only if `RiemannHypothesis` holds
     (`riemannHypothesis_iff_forall_zetaClampedTwoApertureRatio_eq_one`).

2. **The explicit-formula prime-window two-aperture ratio (`primeWindowTwoApertureRatio`).**
   Replacing `μ(A)` at the upper aperture `A = v/2 + w` by the two-bump explicit-formula prime-window
   functional `Re P_{w, v}` (retaining the prime sum, archimedean term, and polar term) defines
   `primeWindowTwoApertureRatio A₀ w v = 1 - Re P_{w, v} / (2 (∫ ‖κ_w‖²) μ(A₀))`.
   - For disjoint bumps `2w < v` (`2w < log 2`), the Rayleigh bridge yields
     `primeWindowTwoApertureRatio A₀ w v ≤ zetaTwoApertureRatio A₀ (v/2 + w)`
     (`primeWindowTwoApertureRatio_le_zetaTwoApertureRatio`).
   - Under `RiemannHypothesis`, `primeWindowTwoApertureRatio A₀ w v ≤ 1` at every lag `v ≥ 0`, and
     under `ZerosApproachLine`, `primeWindowTwoApertureRatio A₀ w (kℓ) ≤ 1` along a single
     non-resonant geometric progression `k ≥ N` is necessary and sufficient for `RiemannHypothesis`
     (`riemannHypothesis_iff_zerosApproachLine_and_grid_primeWindowTwoApertureRatio_le_one`).

3. **Unconditional `2σ`-abscissa inversion and near-top zero detection.**
   - An exponential upper bound `zetaTwoApertureRatio A₀ A ≤ 1 + C e^{2σA}` (`A ≥ A₁`, `σ ≥ 0`)
     unconditionally forces `|Re ρ - 1/2| ≤ σ` for every nontrivial zero `ρ` of `ζ`
     (`abs_re_sub_half_le_of_zetaTwoApertureRatio_le_one_add_exp`).
   - Conversely, a near-top zero `½ + z₀` right of the line forces `zetaTwoApertureRatio A₀ A > 1`
     at every aperture `A ≥ V/2 + w` beyond its visibility lag
     (`one_lt_zetaTwoApertureRatio_of_near_top_zero`).

4. **Unconditional bounds reachable from the corpus's inputs.**
   - **Markov small-aperture band (`A ≤ 21/200`)**: `zetaTwoApertureRatio A₀ A ≤ 1 - 1 / (30 μ(A₀)) < 1`
     (`zetaTwoApertureRatio_le_of_le_twentyOne_twoHundredths`, `zetaTwoApertureRatio_lt_one_of_le_twentyOne_twoHundredths`).
   - **Sharp-gauge three-tenths band (`v/2 + w ≤ 3/10`)**: `primeWindowTwoApertureRatio A₀ w v ≤ 1`
     unconditionally through aperture `3/10` (`primeWindowTwoApertureRatio_le_one_of_le_threeTenths`).
   - **Suzuki window-gauge logarithmic band (`2A < log 2`)**:
     `zetaTwoApertureRatio A₀ A ≤ 1 - windowFloor(A) / μ(A₀)` and
     `primeWindowTwoApertureRatio A₀ w v ≤ 1 - windowFloor(R) / μ(A₀)` for `v/2 + w < R < (log 2)/2`
     (`zetaTwoApertureRatio_le_windowFloor`, `primeWindowTwoApertureRatio_le_windowFloor`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

noncomputable section
set_option autoImplicit false

/-! ## §1. The two-aperture ground-energy ratio of `ζ` -/

/-- The two-aperture ratio of the restricted Weil ground energy `μ` of `ζ` between a base aperture
`A₀` and a target aperture `A`:
`zetaTwoApertureRatio A₀ A = (μ(A₀) - μ(A)) / μ(A₀)`. -/
def zetaTwoApertureRatio (A₀ A : SuzukiPositiveAperture) : ℝ :=
  (ccmRestrictedWeilGroundEnergy A₀ - ccmRestrictedWeilGroundEnergy A) /
    ccmRestrictedWeilGroundEnergy A₀

/-- The clamped two-aperture ratio of `ζ`, which records only negative excursions of `μ(A)` below
the critical value `0`:
`zetaClampedTwoApertureRatio A₀ A = 1 - min(μ(A), 0) / μ(A₀)`. -/
def zetaClampedTwoApertureRatio (A₀ A : SuzukiPositiveAperture) : ℝ :=
  1 - min (ccmRestrictedWeilGroundEnergy A) 0 / ccmRestrictedWeilGroundEnergy A₀

/-- Unconditional positivity of the reference ground energy `μ(A₀)` for `A₀ ≤ 21/200`. -/
theorem ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) :
    0 < ccmRestrictedWeilGroundEnergy A₀ := by
  have h := one_thirtieth_le_ccmRestrictedWeilGroundEnergy hA₀
  linarith

/-- Decomposition `zetaTwoApertureRatio A₀ A = 1 - μ(A) / μ(A₀)` when `A₀ ≤ 21/200`. -/
theorem zetaTwoApertureRatio_eq_one_sub {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (A : SuzukiPositiveAperture) :
    zetaTwoApertureRatio A₀ A =
      1 - ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ := by
  unfold zetaTwoApertureRatio
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  rw [sub_div, div_self (ne_of_gt hpos)]

/-- At equal apertures `A = A₀`, the two-aperture ratio vanishes. -/
theorem zetaTwoApertureRatio_self (A₀ : SuzukiPositiveAperture) :
    zetaTwoApertureRatio A₀ A₀ = 0 := by
  simp [zetaTwoApertureRatio]

/-- Because `μ(A)` is antitone in `A` and `μ(A₀) > 0`, `zetaTwoApertureRatio A₀` is monotone
nondecreasing in the second aperture `A`. -/
theorem zetaTwoApertureRatio_monotone {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) {A B : SuzukiPositiveAperture} (hAB : A.1 ≤ B.1) :
    zetaTwoApertureRatio A₀ A ≤ zetaTwoApertureRatio A₀ B := by
  unfold zetaTwoApertureRatio
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hant := ccmRestrictedWeilGroundEnergy_antitone (a := A) (b := B) hAB
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- For `A₀ ≤ A`, `zetaTwoApertureRatio A₀ A ≥ 0` unconditionally. -/
theorem zetaTwoApertureRatio_nonneg_of_le {A₀ A : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (hle : A₀.1 ≤ A.1) :
    0 ≤ zetaTwoApertureRatio A₀ A := by
  rw [← zetaTwoApertureRatio_self A₀]
  exact zetaTwoApertureRatio_monotone hA₀ hle

/-- **Unconditional approach to the critical value `1` from below.**
Because the theta plateau lies in the radical of the full zero form (`μ(A) < ε` for large `A`), for
every `ε > 0` there is an aperture threshold `A₁` beyond which `zetaTwoApertureRatio A₀ A > 1 - ε`
unconditionally. -/
theorem exists_one_sub_lt_zetaTwoApertureRatio {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₁ : ℝ, ∀ A : SuzukiPositiveAperture, A₁ ≤ A.1 →
      1 - ε < zetaTwoApertureRatio A₀ A := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  obtain ⟨A₁, hA₁⟩ := exists_ccmRestrictedWeilGroundEnergy_lt (mul_pos hε hpos)
  refine ⟨A₁, fun A hA => ?_⟩
  rw [zetaTwoApertureRatio_eq_one_sub hA₀]
  have hlt := hA₁ A hA
  have hdiv : ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ < ε :=
    (div_lt_iff₀ hpos).mpr hlt
  linarith

/-- The two-aperture ratio lies at or below the critical value `1` if and only if `μ(A) ≥ 0`. -/
theorem zetaTwoApertureRatio_le_one_iff {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (A : SuzukiPositiveAperture) :
    zetaTwoApertureRatio A₀ A ≤ 1 ↔ 0 ≤ ccmRestrictedWeilGroundEnergy A := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  rw [zetaTwoApertureRatio_eq_one_sub hA₀]
  constructor
  · intro h
    have hdiv : 0 ≤ ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ := by linarith
    have hmul := mul_nonneg hdiv hpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
  · intro h
    have hdiv : 0 ≤ ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ :=
      div_nonneg h hpos.le
    linarith

/-- The two-aperture ratio strictly exceeds `1` if and only if `μ(A) < 0`. -/
theorem one_lt_zetaTwoApertureRatio_iff {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (A : SuzukiPositiveAperture) :
    1 < zetaTwoApertureRatio A₀ A ↔ ccmRestrictedWeilGroundEnergy A < 0 := by
  rw [← not_iff_not]
  push Not
  exact zetaTwoApertureRatio_le_one_iff hA₀ A

/-- **Criticality of the two-aperture ratio (`≤ 1` form).**
For any reference aperture `A₀ ≤ 21/200`, `RiemannHypothesis` holds if and only if
`zetaTwoApertureRatio A₀ A ≤ 1` for every aperture `A`. -/
theorem riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) :
    RiemannHypothesis ↔ ∀ A : SuzukiPositiveAperture, zetaTwoApertureRatio A₀ A ≤ 1 := by
  constructor
  · intro hRH A
    rw [zetaTwoApertureRatio_le_one_iff hA₀]
    exact ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A
  · intro h
    rw [riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero]
    intro ε hε
    obtain ⟨A₁, hA₁⟩ := exists_ccmRestrictedWeilGroundEnergy_lt hε
    refine ⟨A₁, fun A hA => abs_lt.mpr ⟨?_, hA₁ A hA⟩⟩
    have h0 := (zetaTwoApertureRatio_le_one_iff hA₀ A).mp (h A)
    linarith

/-- **Criticality of the two-aperture ratio (asymptotic limit `1` form).**
For any reference aperture `A₀ ≤ 21/200`, `RiemannHypothesis` holds if and only if
`zetaTwoApertureRatio A₀ A → 1` as `A → ∞`. -/
theorem riemannHypothesis_iff_tendsto_zetaTwoApertureRatio_one
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) :
    RiemannHypothesis ↔
      ∀ ε > 0, ∃ A₁ : ℝ, ∀ A : SuzukiPositiveAperture, A₁ ≤ A.1 →
        |zetaTwoApertureRatio A₀ A - 1| < ε := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  rw [riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero]
  constructor
  · intro h ε hε
    obtain ⟨A₁, hA₁⟩ := h (ε * ccmRestrictedWeilGroundEnergy A₀) (mul_pos hε hpos)
    refine ⟨A₁, fun A hA => ?_⟩
    rw [zetaTwoApertureRatio_eq_one_sub hA₀,
      show 1 - ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ - 1 =
        -(ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀) by ring,
      abs_neg, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    exact hA₁ A hA
  · intro h ε hε
    obtain ⟨A₁, hA₁⟩ := h (ε / ccmRestrictedWeilGroundEnergy A₀) (div_pos hε hpos)
    refine ⟨A₁, fun A hA => ?_⟩
    have hlt := hA₁ A hA
    rw [zetaTwoApertureRatio_eq_one_sub hA₀,
      show 1 - ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ - 1 =
        -(ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀) by ring,
      abs_neg, abs_div, abs_of_pos hpos] at hlt
    exact (div_lt_div_iff_of_pos_right hpos).mp hlt

/-- The clamped two-aperture ratio is unconditionally at least `1` at every aperture. -/
theorem one_le_zetaClampedTwoApertureRatio {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (A : SuzukiPositiveAperture) :
    1 ≤ zetaClampedTwoApertureRatio A₀ A := by
  unfold zetaClampedTwoApertureRatio
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hle : min (ccmRestrictedWeilGroundEnergy A) 0 / ccmRestrictedWeilGroundEnergy A₀ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (min_le_right _ _) hpos.le
  linarith

/-- **Exact attainment of the critical value `1` on the critical line.**
For any reference aperture `A₀ ≤ 21/200`, `RiemannHypothesis` holds if and only if the clamped
two-aperture ratio `zetaClampedTwoApertureRatio A₀ A` equals `1` at every aperture `A`. -/
theorem riemannHypothesis_iff_forall_zetaClampedTwoApertureRatio_eq_one
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) :
    RiemannHypothesis ↔ ∀ A : SuzukiPositiveAperture, zetaClampedTwoApertureRatio A₀ A = 1 := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  rw [riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one hA₀]
  refine forall_congr' fun A => ?_
  rw [zetaTwoApertureRatio_le_one_iff hA₀]
  unfold zetaClampedTwoApertureRatio
  constructor
  · intro h
    rw [min_eq_right h, zero_div, sub_zero]
  · intro h
    have h0 : min (ccmRestrictedWeilGroundEnergy A) 0 / ccmRestrictedWeilGroundEnergy A₀ = 0 := by
      linarith
    have hmin : min (ccmRestrictedWeilGroundEnergy A) 0 = 0 :=
      (div_eq_zero_iff.mp h0).resolve_right (ne_of_gt hpos)
    exact min_eq_right_iff.mp hmin

/-! ## §2. The explicit-formula prime-window two-aperture ratio -/

/-- The explicit-formula prime-window two-aperture ratio at reference aperture `A₀`, bump width `w`,
and lag `v`, built directly from `lagPrimeWindowRHS` (which retains the prime sum, archimedean term,
and polar term) and the reference ground energy `μ(A₀)`:
`primeWindowTwoApertureRatio A₀ w v = 1 - Re P_{w, v} / (2 (∫ ‖κ_w‖²) μ(A₀))`. -/
def primeWindowTwoApertureRatio (A₀ : SuzukiPositiveAperture) (w v : ℝ) : ℝ :=
  1 - (lagPrimeWindowRHS v w
    (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1)))).re /
    (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀)

/-- For `0 < w < (log 2)/2` and `0 ≤ v`, the explicit-formula prime-window ratio coincides with the
normalized Weil functional ratio on the difference two-bump test `f_{w, v}`. -/
theorem primeWindowTwoApertureRatio_eq_weilRatio (A₀ : SuzukiPositiveAperture)
    {w v : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv : 0 ≤ v) :
    primeWindowTwoApertureRatio A₀ w v =
      1 - (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re /
        (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀) := by
  unfold primeWindowTwoApertureRatio
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]

/-- **Rayleigh comparison between the prime-window ratio and the ground-energy ratio.**
For `A₀ ≤ 21/200`, `0 < w`, `2w < log 2`, and disjoint bumps `2w < v` with `∫ ‖κ_w‖² > 0`,
`primeWindowTwoApertureRatio A₀ w v ≤ zetaTwoApertureRatio A₀ (v/2 + w)`. -/
theorem primeWindowTwoApertureRatio_le_zetaTwoApertureRatio {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) {w v : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv : 2 * w < v)
    (hB : 0 < ∫ t, ‖modScaledBump w 0 t‖ ^ 2) :
    primeWindowTwoApertureRatio A₀ w v ≤
      zetaTwoApertureRatio A₀ ⟨v / 2 + w, by linarith⟩ := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hden : 0 < 2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀ := by
    positivity
  have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS hw hw2 hv
  unfold primeWindowTwoApertureRatio
  rw [zetaTwoApertureRatio_eq_one_sub hA₀]
  have hdiv : ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ /
      ccmRestrictedWeilGroundEnergy A₀ ≤
      (lagPrimeWindowRHS v w
        (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1)))).re /
        (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀) := by
    rw [div_le_div_iff₀ hpos hden]
    nlinarith
  linarith

/-- Under `RiemannHypothesis`, the prime-window two-aperture ratio lies at or below `1` for every
`w ∈ (0, (log 2)/2)` and `v ≥ 0`. -/
theorem primeWindowTwoApertureRatio_le_one_of_riemannHypothesis (hRH : RiemannHypothesis)
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200)
    {w v : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv : 0 ≤ v) :
    primeWindowTwoApertureRatio A₀ w v ≤ 1 := by
  rw [primeWindowTwoApertureRatio_eq_weilRatio A₀ hw hw2 hv]
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hB : 0 ≤ ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hW : 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re :=
    weil_nonneg_of_onLine _ (riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH) _
  have hdiv : 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re /
      (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀) :=
    div_nonneg hW (by positivity)
  linarith

/-- **Single-progression equivalence for the two-aperture ground-energy ratio under `ZerosApproachLine`.**
For every non-resonant step `ℓ > 0`, good width `w > 0`, and base aperture `A₀ ≤ 21/200`,
`RiemannHypothesis` holds if and only if `ZerosApproachLine` holds and the two-aperture ratio
`zetaTwoApertureRatio A₀ (kℓ/2 + w)` is bounded above along `k ≥ N`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_grid_zetaTwoApertureRatio_bddAbove
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200)
    {w ℓ : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    (hℓ : 0 < ℓ) (hres : ℓ ∉ resonantSteps zetaZeroConfig) (N : ℕ) :
    RiemannHypothesis ↔
      BacklundConverse.ZerosApproachLine ∧
        ∃ B : ℝ, ∀ k : ℕ, N ≤ k →
          zetaTwoApertureRatio A₀
            ⟨k * ℓ / 2 + w, by have : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le; positivity⟩ ≤ B := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  rw [riemannHypothesis_iff_zerosApproachLine_and_grid_ccmRestrictedWeilGroundEnergy_bddBelow
    hw hgood hℓ hres N]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨1 + C / ccmRestrictedWeilGroundEnergy A₀, fun k hk => ?_⟩
    let Ak : SuzukiPositiveAperture :=
      ⟨k * ℓ / 2 + w, by have : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le; positivity⟩
    rw [zetaTwoApertureRatio_eq_one_sub hA₀]
    have hle : -C ≤ ccmRestrictedWeilGroundEnergy Ak := hC k hk
    have hdiv : -(C / ccmRestrictedWeilGroundEnergy A₀) ≤
        ccmRestrictedWeilGroundEnergy Ak / ccmRestrictedWeilGroundEnergy A₀ := by
      rw [← neg_div, div_le_div_iff_of_pos_right hpos]
      exact hle
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨(B - 1) * ccmRestrictedWeilGroundEnergy A₀, fun k hk => ?_⟩
    let Ak : SuzukiPositiveAperture :=
      ⟨k * ℓ / 2 + w, by have : (0 : ℝ) ≤ k * ℓ := mul_nonneg k.cast_nonneg hℓ.le; positivity⟩
    have hle : zetaTwoApertureRatio A₀ Ak ≤ B := hB k hk
    rw [zetaTwoApertureRatio_eq_one_sub hA₀] at hle
    have hdiv : 1 - B ≤
        ccmRestrictedWeilGroundEnergy Ak / ccmRestrictedWeilGroundEnergy A₀ := by
      linarith
    have hmul := (le_div_iff₀ hpos).mp hdiv
    linarith

/-! ## §3. Unconditional `2σ`-abscissa inversion and near-top zero detection -/

/-- **Unconditional `2σ`-abscissa law for `zetaTwoApertureRatio`.**
If `zetaTwoApertureRatio A₀ A ≤ 1 + C e^{2σA}` for all `A ≥ A₁` (`A₀ ≤ 21/200`, `σ ≥ 0`), then
every nontrivial zero `ρ ∈ zetaZeroConfig.carrier` satisfies `|Re ρ - 1/2| ≤ σ` unconditionally. -/
theorem abs_re_sub_half_le_of_zetaTwoApertureRatio_le_one_add_exp
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200)
    {σ C A₁ : ℝ} (hσ : 0 ≤ σ)
    (hratio : ∀ A : SuzukiPositiveAperture, A₁ ≤ A.1 →
      zetaTwoApertureRatio A₀ A ≤ 1 + C * Real.exp (2 * σ * A.1))
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re - 1 / 2| ≤ σ := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  refine abs_re_sub_half_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ
    (C := ccmRestrictedWeilGroundEnergy A₀ * C) (A₀ := A₁) (fun A hA => ?_) hρ
  have h := hratio A hA
  rw [zetaTwoApertureRatio_eq_one_sub hA₀] at h
  have hdiv : -(C * Real.exp (2 * σ * A.1)) ≤
      ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ := by
    linarith
  have hmul := (le_div_iff₀ hpos).mp hdiv
  linarith

/-- **Near-top zeros force `zetaTwoApertureRatio` strictly above the critical value `1`.**
If `½ + z₀ ∈ zetaZeroConfig.carrier` is a zero of `ζ` right of the line (`Re z₀ > 0`) with
`η ≤ ‖paperFT (scaledBump w) (-i z₀)‖`, visibility lag `V ≥ oneParamLag w η (Re z₀)`, and no zero
deeper than `Re z₀ + 1/V`, then `1 < zetaTwoApertureRatio A₀ A` for every aperture `A ≥ V/2 + w`. -/
theorem one_lt_zetaTwoApertureRatio_of_near_top_zero {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (A : SuzukiPositiveAperture) (hA : V / 2 + w ≤ A.1) :
    1 < zetaTwoApertureRatio A₀ A := by
  rw [one_lt_zetaTwoApertureRatio_iff hA₀]
  exact ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero hw hz₀ hre₀ hη hηle hV htop A hA

/-! ## §4. Unconditional bounds reachable from the corpus's inputs -/

/-- **Reachable Bound 1 (Markov small-aperture band `A ≤ 21/200`).**
For every `A₀, A ≤ 21/200`, the two-aperture ratio satisfies the explicit unconditional bound
`zetaTwoApertureRatio A₀ A ≤ 1 - 1 / (30 μ(A₀)) < 1`. -/
theorem zetaTwoApertureRatio_le_of_le_twentyOne_twoHundredths
    {A₀ A : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) (hA : A.1 ≤ 21 / 200) :
    zetaTwoApertureRatio A₀ A ≤ 1 - 1 / (30 * ccmRestrictedWeilGroundEnergy A₀) := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hfloor := one_thirtieth_le_ccmRestrictedWeilGroundEnergy hA
  rw [zetaTwoApertureRatio_eq_one_sub hA₀]
  have hdiv : 1 / (30 * ccmRestrictedWeilGroundEnergy A₀) ≤
      ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ := by
    rw [show 1 / (30 * ccmRestrictedWeilGroundEnergy A₀) =
      (1 / 30) / ccmRestrictedWeilGroundEnergy A₀ by ring]
    exact div_le_div_of_nonneg_right hfloor hpos.le
  linarith

theorem zetaTwoApertureRatio_lt_one_of_le_twentyOne_twoHundredths
    {A₀ A : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200) (hA : A.1 ≤ 21 / 200) :
    zetaTwoApertureRatio A₀ A < 1 := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hle := zetaTwoApertureRatio_le_of_le_twentyOne_twoHundredths hA₀ hA
  have hpos' : 0 < 1 / (30 * ccmRestrictedWeilGroundEnergy A₀) := by positivity
  linarith

/-- **Reachable Bound 2 (Sharp-gauge three-tenths band `v/2 + w ≤ 3/10`).**
For every `A₀ ≤ 21/200`, `0 < w < (log 2)/2`, `0 ≤ v`, and `v/2 + w ≤ 3/10`, the explicit-formula
prime-window two-aperture ratio satisfies `primeWindowTwoApertureRatio A₀ w v ≤ 1` unconditionally. -/
theorem primeWindowTwoApertureRatio_le_one_of_le_threeTenths
    {A₀ : SuzukiPositiveAperture} (hA₀ : A₀.1 ≤ 21 / 200)
    {w v : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv : 0 ≤ v) (hvw : v / 2 + w ≤ 3 / 10) :
    primeWindowTwoApertureRatio A₀ w v ≤ 1 := by
  rw [primeWindowTwoApertureRatio_eq_weilRatio A₀ hw hw2 hv]
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hB : 0 ≤ ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsupp : tsupport (twoBump (modScaledBump w 0) v (-1)) ⊆ Icc (-(3 / 10)) (3 / 10) :=
    (tsupport_twoBump_modScaledBump_subset hw hv).trans fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hW : 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re :=
    zetaZeroConfig_re_W_nonneg_of_aperture_le_threeTenths
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]) hsupp
  have hdiv : 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re /
      (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀) :=
    div_nonneg hW (by positivity)
  linarith

/-- **Reachable Bound 3 (Suzuki window-gauge logarithmic band `2A < log 2`).**
For every `A₀ ≤ 21/200` and every aperture `A` with `2A < log 2`,
`zetaTwoApertureRatio A₀ A ≤ 1 - windowFloor(A) / μ(A₀)` unconditionally. -/
theorem zetaTwoApertureRatio_le_windowFloor {A₀ A : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) (hA : 2 * A.1 < Real.log 2) :
    zetaTwoApertureRatio A₀ A ≤
      1 - windowFloor A.1 / ccmRestrictedWeilGroundEnergy A₀ := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hfloor := windowFloor_le_ccmRestrictedWeilGroundEnergy_self hA
  rw [zetaTwoApertureRatio_eq_one_sub hA₀]
  have hdiv : windowFloor A.1 / ccmRestrictedWeilGroundEnergy A₀ ≤
      ccmRestrictedWeilGroundEnergy A / ccmRestrictedWeilGroundEnergy A₀ :=
    div_le_div_of_nonneg_right hfloor hpos.le
  linarith

/-- **Reachable Bound 4 (Prime-window logarithmic floor for `v/2 + w < R < (log 2)/2`).**
For `A₀ ≤ 21/200`, `0 < w`, `2w < v`, `v/2 + w < R`, `2R < log 2`, and `∫ ‖κ_w‖² > 0`,
`primeWindowTwoApertureRatio A₀ w v ≤ 1 - windowFloor(R) / μ(A₀)` unconditionally. -/
theorem primeWindowTwoApertureRatio_le_windowFloor {A₀ : SuzukiPositiveAperture}
    (hA₀ : A₀.1 ≤ 21 / 200) {w v R : ℝ} (hw : 0 < w) (hv : 2 * w < v)
    (hR : v / 2 + w < R) (hR2 : 2 * R < Real.log 2)
    (hB : 0 < ∫ t, ‖modScaledBump w 0 t‖ ^ 2) :
    primeWindowTwoApertureRatio A₀ w v ≤
      1 - windowFloor R / ccmRestrictedWeilGroundEnergy A₀ := by
  have hpos := ccmRestrictedWeilGroundEnergy_pos_of_le_twentyOne_twoHundredths hA₀
  have hden : 0 < 2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀ := by
    positivity
  have hfloor := two_mul_windowFloor_le_re_lagPrimeWindowRHS_of_lt hw hv hR hR2
  unfold primeWindowTwoApertureRatio
  have hdiv : windowFloor R / ccmRestrictedWeilGroundEnergy A₀ ≤
      (lagPrimeWindowRHS v w
        (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1)))).re /
        (2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * ccmRestrictedWeilGroundEnergy A₀) := by
    rw [div_le_div_iff₀ hpos hden]
    nlinarith
  linarith

/-! ## §5. Model-to-object unification: the normalized doubling ratio on isolated pairs -/

/-- The normalized two-aperture doubling ratio `M(2a) / (2 M(a))` of an isolated pair at depth `δ`
and aperture `a > 0`, calibrated so that its critical value on the line (`δ = 0`) is `1`, matching
`zetaClampedTwoApertureRatio`. -/
def normalizedPairDoublingRatio (δ a : ℝ) : ℝ :=
  if δ = 0 then 1 else pairMoment δ (2 * a) / (2 * pairMoment δ a)

/-- For every `δ ≥ 0` and `a > 0`, `normalizedPairDoublingRatio δ a = cosh(2δa)`. -/
theorem normalizedPairDoublingRatio_eq_cosh {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0 < a) :
    normalizedPairDoublingRatio δ a = Real.cosh (2 * δ * a) := by
  unfold normalizedPairDoublingRatio
  rcases eq_or_lt_of_le hδ with rfl | hpos
  · simp
  · rw [if_neg (ne_of_gt hpos)]
    have h := pairMoment_doubling hpos ha
    calc pairMoment δ (2 * a) / (2 * pairMoment δ a)
        = (pairMoment δ (2 * a) / pairMoment δ a) / 2 := by ring
      _ = 2 * Real.cosh (2 * δ * a) / 2 := by rw [h]
      _ = Real.cosh (2 * δ * a) := by ring

/-- The normalized doubling ratio attains its critical value `1` if and only if `δ = 0` (the pair
lies on the critical line). -/
theorem normalizedPairDoublingRatio_eq_one_iff {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0 < a) :
    normalizedPairDoublingRatio δ a = 1 ↔ δ = 0 := by
  rw [normalizedPairDoublingRatio_eq_cosh hδ ha]
  constructor
  · intro h
    rcases eq_or_lt_of_le hδ with rfl | hpos
    · rfl
    · have hgt : 1 < Real.cosh (2 * δ * a) := Real.one_lt_cosh.mpr (by positivity)
      linarith
  · rintro rfl
    simp

end

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
