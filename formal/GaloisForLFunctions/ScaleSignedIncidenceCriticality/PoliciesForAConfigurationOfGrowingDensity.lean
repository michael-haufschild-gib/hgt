import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDesignSpecificationOfACounterexample
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.SquareRootThreshold.PolarGroundEnergyAndPoleFreeLagAbscissaBridge

/-!
# Policies for a configuration of growing density

This module resolves **Open Problem 6** of the Scale-Signed Incidence Criticality (SSIC)
programme: *for a configuration whose zero density grows with the height (`L(T) = log(T/2π)`),
what is the exact floor of the class of policies with a prescribed growth of aperture `A(L)` and
precision `η(L)`, and which schedules of aperture and precision are realisable from the corpus's
unconditional inputs?*

## Mathematical overview

1. **The scale-aware policy reading and the sub-Nyquist escape law (§1).**
   A policy `(A, η : ℝ → ℝ)` induces both the pure policy reading `adaptiveReading A η` on
   `ScaleDepthDatum` and the scale-aware reading
   `scaleAdaptiveReading A η = joinReading sdScale (adaptiveReading A η)` observing the known
   local density scale `L = sdScale p`. Whenever `A L ≤ L / 2` and `0 ≤ η L` at even one scale
   `L > 0` (in particular for any bounded aperture schedule `A L ≤ M`), the global reading
   `adaptiveReading A η` has exact resolution limit `1 / 2`, resolution floor `0`, and resolution
   interval `[0, 1 / 2]` (`resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist`,
   `resolutionLimit_sdDepth_adaptiveReading_of_bddAbove`). Likewise, at any sub-Nyquist scale
   `A L ≤ L / 2`, `scaleAdaptiveReading A η` has exact limit `1 / 2` and floor `0`
   (`resolutionLimit_sdDepth_scaleAdaptiveReading_of_subNyquist`).

2. **Exact resolution limits and certification equivalences for scale-matched policies (§2).**
   In the second aliasing band `L / 2 < A L ≤ L` (`ScaleMatched A η`):
   - At a known scale `L = sdScale p₀`, `scaleAdaptiveReading A η` has exact resolution limit
     `min (1 / 2) (depthResolution L (η L))`, floor `0`, and interval
     `[0, min (1 / 2) (depthResolution L (η L))]`
     (`resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched`).
   - Globally across all scales `L > 0`, `adaptiveReading A η` has exact resolution limit
     `sSup ((fun L => min (1 / 2) (depthResolution L (η L))) '' Ioi 0)` and floor `0`
     (`resolutionLimit_sdDepth_adaptiveReading_scaleMatched`,
     `resolutionFloor_sdDepth_adaptiveReading_scaleMatched`).
   - For every target depth `0 < β < 1 / 2`, a scale-matched policy certifies `sdDepth ≤ β`
     if and only if `∀ L > 0, η L ≤ weilFloorThreshold L β`
     (`certifies_sdDepth_adaptiveReading_iff`).
   - As `L → ∞`, any precision schedule with `η L / L ^ 3 → 0` (in particular any sub-cubic
     power schedule `η L ≤ C * L ^ 2`) drives `depthResolution L (η L) → 0`
     (`tendsto_depthResolution_zero_of_div_cube_tendsto_zero`).

3. **Policies with prescribed trans-Nyquist aperture growth `A(L) > L / 2` (§3).**
   For a general trans-Nyquist policy `TransNyquistPolicy A η` (`L / 2 < A L`, `0 ≤ η L`) with
   aliasing index schedule `aliasingIndex A L = ⌈2 * A L / L⌉₊ ≥ 2`:
   - `adaptiveReading A η p ↔ bandEnergy (sdScale p) (sdDepth p) (aliasingIndex A (sdScale p)) ≤ η (sdScale p)`
     (`adaptiveReading_iff_bandEnergy_le`).
   - A zero-deficit trans-Nyquist policy (`η L = 0`) refutes every off-line lattice datum at scale `L`
     (`not_adaptiveReading_zero_of_transNyquist`).
   - Using the two-step recurrence `bandEnergy_succ_sub_pred`, the `n`-th band energy satisfies the
     hyperbolic lower bound `weilFloorThreshold L ((n - 1) * δ) ≤ bandEnergy L δ n`
     (`weilFloorThreshold_mul_le_bandEnergy`), so `bandEnergy L δ n ≤ η` implies
     `δ ≤ depthResolution L η / (n - 1) ≤ √(η / L ^ 3) / (n - 1)`
     (`depth_le_div_sub_one_of_bandEnergy_le`).
   - Consequently, at scale `L = sdScale p₀` with `n = aliasingIndex A L ≥ 2`, the exact
     resolution limit of `scaleAdaptiveReading A η` is bracketed between two `arcosh` profiles:
     `min (1 / 2) (arcosh (1 + η L / (L * n)) / (n * L)) ≤ resolutionLimit ≤ min (1 / 2) (depthResolution L (η L) / (n - 1))`
     (`resolutionLimit_sdDepth_scaleAdaptiveReading_brackets`), and for `0 < β < 1 / 2`,
     `Certifies sdDepth (adaptiveReading A η) p₀ β ↔ ∀ L > 0, η L ≤ bandEnergy L β (aliasingIndex A L)`
     (`certifies_sdDepth_adaptiveReading_transNyquist_iff`).

4. **Unconditionally realisable schedules for `ζ` at growing density (§4).**
   At height `2πξ` with local archimedean density scale `zetaHeightScale ξ = log (1 + π|ξ| / 4)`,
   the corpus's unconditional inputs give a two-way pincer on realisable policies:
   - *Sub-Nyquist single-height positivity regime:* Every single-height positivity schedule
     satisfying the archimedean symbol horizon `4 e^{A L} ≤ 4 + L` (i.e. `A L ≤ log (1 + L / 4)`,
     including the Chebyshev schedule `archimedeanHorizonAperture L = log (1 + L / 70)`) satisfies
     `A L < L / 2` at every scale `L > 0` (`sharpHorizonAperture_lt_half_scale`), so despite
     operating at zero main-term deficit (`η = 0`), its lattice depth resolution limit is `1 / 2`
     (`resolutionLimit_sdDepth_of_le_sharpHorizonAperture`).
   - *Trans-Nyquist Chebyshev deficit regime:* Crossing `L / 2` into the second aliasing band
     `A L = L` with the corpus's unconditional Chebyshev floor
     `chebyshevDeficit L = horizonExponent (e^{2L}) = 10 + 68 e^L`
     (`neg_horizonExponent_mul_le_fullZeroForm_Icc`) satisfies
     `weilFloorThreshold L (1 / 2) ≤ chebyshevDeficit L` at every scale `L > 0`
     (`weilFloorThreshold_half_le_chebyshevDeficit`), so its depth resolution limit is again `1 / 2`
     (`resolutionLimit_sdDepth_scaleAdaptiveReading_chebyshev_eq_half`,
     `resolutionLimit_sdDepth_adaptiveReading_chebyshev_eq_half`).
-/

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

noncomputable section

/-! ## §1. The Scale-Aware Policy Reading and the Sub-Nyquist Escape Law -/

/-- The **scale-aware policy reading** at a configuration of known local density `L = sdScale p`:
it observes both the scale `sdScale p` and the adaptive Weil-floor verdict `adaptiveReading A η p`. -/
def scaleAdaptiveReading (A η : ℝ → ℝ) : ScaleDepthDatum → ℝ × Prop :=
  joinReading sdScale (adaptiveReading A η)

/-- Two data share the same `scaleAdaptiveReading` iff they have the same scale and the same
adaptive verdict. -/
theorem mem_shadow_scaleAdaptiveReading_iff {A η : ℝ → ℝ} {p p₀ : ScaleDepthDatum} :
    p ∈ shadow (scaleAdaptiveReading A η) p₀ ↔
      sdScale p = sdScale p₀ ∧ (adaptiveReading A η p ↔ adaptiveReading A η p₀) := by
  rw [scaleAdaptiveReading, shadow_joinReading, mem_inter_iff, mem_shadow_iff, mem_shadow_iff,
    eq_iff_iff]

/-- **Sub-Nyquist automaticity for policies.** At any datum `p` whose scale `L = sdScale p`
satisfies `A L ≤ L / 2` and `0 ≤ η L`, the policy reading `adaptiveReading A η p` holds
automatically regardless of the depth `sdDepth p`. -/
theorem adaptiveReading_of_subNyquist {A η : ℝ → ℝ} {p : ScaleDepthDatum}
    (hA : A (sdScale p) ≤ sdScale p / 2) (hη : 0 ≤ η (sdScale p)) :
    adaptiveReading A η p :=
  scaleDepthReading_of_dense hη p (by linarith)

/-- **The sub-Nyquist escape law (resolution limit).** If a policy `(A, η)` falls at or below the
Nyquist threshold `A L ≤ L / 2` with `0 ≤ η L` at even one scale `L > 0`, its global depth
resolution limit on `ScaleDepthDatum` is `1 / 2`. -/
theorem resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist {A η : ℝ → ℝ}
    (hex : ∃ L : ℝ, 0 < L ∧ A L ≤ L / 2 ∧ 0 ≤ η L)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionLimit sdDepth (adaptiveReading A η) p₀ = 1 / 2 := by
  obtain ⟨L, hL, hA, hη⟩ := hex
  set p_max : ScaleDepthDatum := ⟨(L, 1 / 2), hL, by norm_num, le_rfl⟩
  have hread : adaptiveReading A η p_max := adaptiveReading_of_subNyquist hA hη
  have hmem : p_max ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread hp₀)
  exact resolutionLimit_eq_of_mem_shadow_of_max (fun p => p.2.2.2) hmem rfl

/-- **The sub-Nyquist escape law (resolution floor).** Under the same hypothesis, the resolution
floor of `sdDepth` is `0`. -/
theorem resolutionFloor_sdDepth_adaptiveReading_of_exists_subNyquist {A η : ℝ → ℝ}
    (hex : ∃ L : ℝ, 0 < L ∧ A L ≤ L / 2 ∧ 0 ≤ η L)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionFloor sdDepth (adaptiveReading A η) p₀ = 0 := by
  obtain ⟨L, hL, hA, hη⟩ := hex
  have hbdd : BddBelow (sdDepth '' shadow (adaptiveReading A η) p₀) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2.1.le
  refine le_antisymm ?_ (le_csInf (shadow_image_nonempty sdDepth (adaptiveReading A η) p₀) ?_)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    set δ : ℝ := min (1 / 2) (ε / 2)
    have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    set p_δ : ScaleDepthDatum := ⟨(L, δ), hL, hδ0, hδle⟩
    have hread : adaptiveReading A η p_δ := adaptiveReading_of_subNyquist hA hη
    have hmem : p_δ ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread hp₀)
    have h1 : resolutionFloor sdDepth (adaptiveReading A η) p₀ ≤ δ :=
      csInf_le hbdd ⟨p_δ, hmem, rfl⟩
    have h2 : δ ≤ ε := (min_le_right _ _).trans (by linarith)
    exact h1.trans h2
  · rintro _ ⟨p, -, rfl⟩
    exact p.2.2.1.le

/-- **Bounded-aperture policies are blind on growing-density families.** Any policy whose aperture
schedule is bounded above (`∀ L > 0, A L ≤ M`) with nonnegative level (`∀ L > 0, 0 ≤ η L`) has
exact depth resolution limit `1 / 2`, floor `0`, and resolution interval `[0, 1 / 2]`. -/
theorem resolutionLimit_sdDepth_adaptiveReading_of_bddAbove {A η : ℝ → ℝ} {M : ℝ}
    (hA : ∀ L : ℝ, 0 < L → A L ≤ M) (hη : ∀ L : ℝ, 0 < L → 0 ≤ η L)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionLimit sdDepth (adaptiveReading A η) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (adaptiveReading A η) p₀ = 0 ∧
      resolutionInterval sdDepth (adaptiveReading A η) p₀ = Icc 0 (1 / 2) := by
  have hex : ∃ L : ℝ, 0 < L ∧ A L ≤ L / 2 ∧ 0 ≤ η L := by
    refine ⟨max 1 (2 * M), lt_of_lt_of_le one_pos (le_max_left _ _), ?_,
      hη _ (lt_of_lt_of_le one_pos (le_max_left _ _))⟩
    have h1 := hA (max 1 (2 * M)) (lt_of_lt_of_le one_pos (le_max_left _ _))
    have h2 : 2 * M ≤ max 1 (2 * M) := le_max_right _ _
    linarith
  have hlim := resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist hex hp₀
  have hflr := resolutionFloor_sdDepth_adaptiveReading_of_exists_subNyquist hex hp₀
  exact ⟨hlim, hflr, by rw [resolutionInterval, hflr, hlim]⟩

/-- **Sub-Nyquist blindness of the scale-aware reading.** At any datum `p₀` whose scale
`L = sdScale p₀` satisfies `A L ≤ L / 2` and `0 ≤ η L`, the scale-aware policy reading
`scaleAdaptiveReading A η` has exact resolution limit `1 / 2`, resolution floor `0`, and
resolution interval `[0, 1 / 2]`. -/
theorem resolutionLimit_sdDepth_scaleAdaptiveReading_of_subNyquist {A η : ℝ → ℝ}
    {p₀ : ScaleDepthDatum} (hA : A (sdScale p₀) ≤ sdScale p₀ / 2) (hη : 0 ≤ η (sdScale p₀)) :
    resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 ∧
      resolutionInterval sdDepth (scaleAdaptiveReading A η) p₀ = Icc 0 (1 / 2) := by
  set L := sdScale p₀
  have hL : 0 < L := p₀.2.1
  have hp₀_read : adaptiveReading A η p₀ := adaptiveReading_of_subNyquist hA hη
  have hlim : resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ = 1 / 2 := by
    set p_max : ScaleDepthDatum := ⟨(L, 1 / 2), hL, by norm_num, le_rfl⟩
    have hread : adaptiveReading A η p_max := adaptiveReading_of_subNyquist hA hη
    have hmem : p_max ∈ shadow (scaleAdaptiveReading A η) p₀ :=
      mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread hp₀_read⟩
    exact resolutionLimit_eq_of_mem_shadow_of_max (fun p => p.2.2.2) hmem rfl
  have hflr : resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 := by
    have hbdd : BddBelow (sdDepth '' shadow (scaleAdaptiveReading A η) p₀) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le
    refine le_antisymm ?_
      (le_csInf (shadow_image_nonempty sdDepth (scaleAdaptiveReading A η) p₀) ?_)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      set δ : ℝ := min (1 / 2) (ε / 2)
      have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
      have hδle : δ ≤ 1 / 2 := min_le_left _ _
      set p_δ : ScaleDepthDatum := ⟨(L, δ), hL, hδ0, hδle⟩
      have hread : adaptiveReading A η p_δ := adaptiveReading_of_subNyquist hA hη
      have hmem : p_δ ∈ shadow (scaleAdaptiveReading A η) p₀ :=
        mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread hp₀_read⟩
      exact (csInf_le hbdd ⟨p_δ, hmem, rfl⟩).trans ((min_le_right _ _).trans (by linarith))
    · rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le
  exact ⟨hlim, hflr, by rw [resolutionInterval, hflr, hlim]⟩

/-! ## §2. Exact Limits, Floors, and Certification Equivalences for Scale-Matched Policies -/

/-- **Exact resolution limit, floor, and interval of a scale-matched policy at a known scale.**
For `ScaleMatched A η` and any datum `p₀` with `adaptiveReading A η p₀` at scale `L = sdScale p₀`,
the scale-aware policy reading `scaleAdaptiveReading A η` has exact resolution limit
`min (1 / 2) (depthResolution L (η L))`, resolution floor `0`, and resolution interval
`[0, min (1 / 2) (depthResolution L (η L))]`. -/
theorem resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched {A η : ℝ → ℝ}
    (h : ScaleMatched A η) {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ =
        min (1 / 2) (depthResolution (sdScale p₀) (η (sdScale p₀))) ∧
      resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 ∧
      resolutionInterval sdDepth (scaleAdaptiveReading A η) p₀ =
        Icc 0 (min (1 / 2) (depthResolution (sdScale p₀) (η (sdScale p₀)))) := by
  set L := sdScale p₀
  have hL : 0 < L := p₀.2.1
  have hD : 0 < depthResolution L (η L) :=
    lt_of_lt_of_le p₀.2.2.1 ((adaptiveReading_iff h p₀).mp hp₀)
  set M := min (1 / 2 : ℝ) (depthResolution L (η L))
  have hM0 : 0 < M := lt_min (by norm_num) hD
  have hMle : M ≤ 1 / 2 := min_le_left _ _
  have hlim : resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ = M := by
    have hbdd : BddAbove (sdDepth '' shadow (scaleAdaptiveReading A η) p₀) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨hscale, hiff⟩ := mem_shadow_scaleAdaptiveReading_iff.mp hp
      have hread : adaptiveReading A η p := hiff.mpr hp₀
      have hdepth := (adaptiveReading_iff h p).mp hread
      rw [hscale] at hdepth
      exact le_min p.2.2.2 hdepth
    refine le_antisymm
      (csSup_le (shadow_image_nonempty sdDepth (scaleAdaptiveReading A η) p₀) ?_) ?_
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨hscale, hiff⟩ := mem_shadow_scaleAdaptiveReading_iff.mp hp
      have hread : adaptiveReading A η p := hiff.mpr hp₀
      have hdepth := (adaptiveReading_iff h p).mp hread
      rw [hscale] at hdepth
      exact le_min p.2.2.2 hdepth
    · set p_M : ScaleDepthDatum := ⟨(L, M), hL, hM0, hMle⟩
      have hread_M : adaptiveReading A η p_M :=
        (adaptiveReading_iff h p_M).mpr (min_le_right _ _)
      have hmem : p_M ∈ shadow (scaleAdaptiveReading A η) p₀ :=
        mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread_M hp₀⟩
      exact le_csSup hbdd ⟨p_M, hmem, rfl⟩
  have hflr : resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 := by
    have hbdd : BddBelow (sdDepth '' shadow (scaleAdaptiveReading A η) p₀) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le
    refine le_antisymm ?_
      (le_csInf (shadow_image_nonempty sdDepth (scaleAdaptiveReading A η) p₀) ?_)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      set δ : ℝ := min M (ε / 2)
      have hδ0 : 0 < δ := lt_min hM0 (by linarith)
      have hδM : δ ≤ M := min_le_left _ _
      set p_δ : ScaleDepthDatum := ⟨(L, δ), hL, hδ0, hδM.trans hMle⟩
      have hread_δ : adaptiveReading A η p_δ :=
        (adaptiveReading_iff h p_δ).mpr (hδM.trans (min_le_right _ _))
      have hmem : p_δ ∈ shadow (scaleAdaptiveReading A η) p₀ :=
        mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread_δ hp₀⟩
      exact (csInf_le hbdd ⟨p_δ, hmem, rfl⟩).trans ((min_le_right _ _).trans (by linarith))
    · rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le
  exact ⟨hlim, hflr, by rw [resolutionInterval, hflr, hlim]⟩

/-- **Exact global resolution floor of a scale-matched policy.** For any `ScaleMatched A η` and any
`p₀` with `adaptiveReading A η p₀`, `resolutionFloor sdDepth (adaptiveReading A η) p₀ = 0`. -/
theorem resolutionFloor_sdDepth_adaptiveReading_scaleMatched {A η : ℝ → ℝ}
    (h : ScaleMatched A η) {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionFloor sdDepth (adaptiveReading A η) p₀ = 0 := by
  set L := sdScale p₀
  have hL : 0 < L := p₀.2.1
  have hD : 0 < depthResolution L (η L) :=
    lt_of_lt_of_le p₀.2.2.1 ((adaptiveReading_iff h p₀).mp hp₀)
  set M := min (1 / 2 : ℝ) (depthResolution L (η L))
  have hM0 : 0 < M := lt_min (by norm_num) hD
  have hMle : M ≤ 1 / 2 := min_le_left _ _
  have hbdd : BddBelow (sdDepth '' shadow (adaptiveReading A η) p₀) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2.1.le
  refine le_antisymm ?_
    (le_csInf (shadow_image_nonempty sdDepth (adaptiveReading A η) p₀) ?_)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    set δ : ℝ := min M (ε / 2)
    have hδ0 : 0 < δ := lt_min hM0 (by linarith)
    have hδM : δ ≤ M := min_le_left _ _
    set p_δ : ScaleDepthDatum := ⟨(L, δ), hL, hδ0, hδM.trans hMle⟩
    have hread_δ : adaptiveReading A η p_δ :=
      (adaptiveReading_iff h p_δ).mpr (hδM.trans (min_le_right _ _))
    have hmem : p_δ ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread_δ hp₀)
    exact (csInf_le hbdd ⟨p_δ, hmem, rfl⟩).trans ((min_le_right _ _).trans (by linarith))
  · rintro _ ⟨p, -, rfl⟩
    exact p.2.2.1.le

/-- At level `0`, `depthResolution L 0 = 0`. -/
theorem depthResolution_zero (L : ℝ) : depthResolution L 0 = 0 := by
  simp [depthResolution]

/-- **Exact global resolution limit of a scale-matched policy.** Across all scales `L > 0`, the
resolution limit of `sdDepth` under `adaptiveReading A η` is the supremum of the per-scale limits
`min (1 / 2) (depthResolution L (η L))` over `L ∈ Ioi 0`. -/
theorem resolutionLimit_sdDepth_adaptiveReading_scaleMatched {A η : ℝ → ℝ}
    (h : ScaleMatched A η) {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    resolutionLimit sdDepth (adaptiveReading A η) p₀ =
      sSup ((fun L => min (1 / 2) (depthResolution L (η L))) '' Ioi 0) := by
  set S := (fun L => min (1 / 2) (depthResolution L (η L))) '' Ioi 0
  have hS_bdd : BddAbove S := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨L, -, rfl⟩
    exact min_le_left _ _
  have hS_ne : S.Nonempty := ⟨_, ⟨1, mem_Ioi.mpr one_pos, rfl⟩⟩
  have hsh_bdd : BddAbove (sdDepth '' shadow (adaptiveReading A η) p₀) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2.2
  refine le_antisymm
    (csSup_le (shadow_image_nonempty sdDepth (adaptiveReading A η) p₀) ?_)
    (csSup_le hS_ne ?_)
  · rintro _ ⟨p, hp, rfl⟩
    have hread : adaptiveReading A η p := (mem_shadow_iff.mp hp) ▸ hp₀
    have hdepth : sdDepth p ≤ min (1 / 2) (depthResolution (sdScale p) (η (sdScale p))) :=
      le_min p.2.2.2 ((adaptiveReading_iff h p).mp hread)
    exact hdepth.trans (le_csSup hS_bdd ⟨sdScale p, p.2.1, rfl⟩)
  · rintro _ ⟨L, hL : 0 < L, rfl⟩
    dsimp only
    rcases (h.level_nonneg L hL).eq_or_lt with hη0 | hηpos
    · rw [← hη0, depthResolution_zero, min_eq_right (by norm_num)]
      have h0 : 0 < sdDepth p₀ := p₀.2.2.1
      exact h0.le.trans (le_csSup hsh_bdd ⟨p₀, rfl, rfl⟩)
    · have hD : 0 < depthResolution L (η L) := depthResolution_pos hL hηpos
      set M := min (1 / 2 : ℝ) (depthResolution L (η L))
      have hM0 : 0 < M := lt_min (by norm_num) hD
      have hMle : M ≤ 1 / 2 := min_le_left _ _
      set p_M : ScaleDepthDatum := ⟨(L, M), hL, hM0, hMle⟩
      have hread_M : adaptiveReading A η p_M :=
        (adaptiveReading_iff h p_M).mpr (min_le_right _ _)
      have hmem : p_M ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread_M hp₀)
      exact le_csSup hsh_bdd ⟨p_M, hmem, rfl⟩

/-- Evaluating `weilFloorThreshold L` at `depthResolution L η` recovers `η`. -/
theorem weilFloorThreshold_depthResolution {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η) :
    weilFloorThreshold L (depthResolution L η) = η := by
  have h1 : 1 ≤ 1 + η / (2 * L) := by
    have : 0 ≤ η / (2 * L) := by positivity
    linarith
  rw [weilFloorThreshold, depthResolution, div_mul_cancel₀ _ hL.ne', Real.cosh_arcosh h1]
  field_simp
  ring

/-- **Exact certification equivalence for scale-matched policies.** For any `ScaleMatched A η`,
any `0 < β < 1 / 2`, and any `p₀` with `adaptiveReading A η p₀`:
`Certifies sdDepth (adaptiveReading A η) p₀ β` holds if and only if
`∀ L > 0, depthResolution L (η L) ≤ β`, if and only if `∀ L > 0, η L ≤ weilFloorThreshold L β`. -/
theorem certifies_sdDepth_adaptiveReading_iff {A η : ℝ → ℝ} (h : ScaleMatched A η)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    (Certifies sdDepth (adaptiveReading A η) p₀ β ↔
        ∀ L : ℝ, 0 < L → depthResolution L (η L) ≤ β) ∧
      (Certifies sdDepth (adaptiveReading A η) p₀ β ↔
        ∀ L : ℝ, 0 < L → η L ≤ weilFloorThreshold L β) := by
  have h1 : Certifies sdDepth (adaptiveReading A η) p₀ β ↔
      ∀ L : ℝ, 0 < L → depthResolution L (η L) ≤ β := by
    constructor
    · intro hcert L hL
      by_contra hgt
      rw [not_le] at hgt
      set β' := min (1 / 2 : ℝ) (depthResolution L (η L))
      have hβ' : β < β' := lt_min hβ hgt
      have hβ'0 : 0 < β' := hβ0.trans hβ'
      have hβ'le : β' ≤ 1 / 2 := min_le_left _ _
      have hreach : weilFloorThreshold L β' ≤ η L :=
        (weilFloorThreshold_le_iff hL hβ'0 (h.level_nonneg L hL)).mpr (min_le_right _ _)
      exact not_certifies_of_budget_violation h hL hβ'0 hβ'le hβ' hreach hp₀ hcert
    · intro hall p hp
      have hread : adaptiveReading A η p := (mem_shadow_iff.mp hp) ▸ hp₀
      exact ((adaptiveReading_iff h p).mp hread).trans (hall (sdScale p) p.2.1)
  have h2 : (∀ L : ℝ, 0 < L → depthResolution L (η L) ≤ β) ↔
      ∀ L : ℝ, 0 < L → η L ≤ weilFloorThreshold L β := by
    refine forall₂_congr fun L hL => ?_
    have hη := h.level_nonneg L hL
    have heq_thr := weilFloorThreshold_depthResolution hL hη
    constructor
    · intro hle
      rcases (h.level_nonneg L hL).eq_or_lt with hη0 | hηpos
      · rw [← hη0]
        have h0 : 0 ≤ L ^ 3 * β ^ 2 := by positivity
        linarith [cube_mul_sq_le_weilFloorThreshold hL hβ0]
      · have hDpos : 0 < depthResolution L (η L) := depthResolution_pos hL hηpos
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (heq_thr ▸ (weilFloorThreshold_strictMono hL hDpos hlt).le)
        · rw [← heq_thr, heq]
    · intro hle
      by_contra hgt
      rw [not_le] at hgt
      have hmono := weilFloorThreshold_strictMono hL hβ0 hgt
      linarith
  exact ⟨h1, h1.trans h2⟩

/-- **Asymptotic resolution of sub-cubic precision schedules.** If `0 ≤ η L` for `L > 0` and
`η L / L ^ 3 → 0` as `L → ∞`, then `depthResolution L (η L) → 0` as `L → ∞`. -/
theorem tendsto_depthResolution_zero_of_div_cube_tendsto_zero {η : ℝ → ℝ}
    (hη : ∀ L : ℝ, 0 < L → 0 ≤ η L)
    (htend : Tendsto (fun L : ℝ => η L / L ^ 3) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => depthResolution L (η L)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun L : ℝ => Real.sqrt (η L / L ^ 3)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp htend
  rw [Real.sqrt_zero] at hsqrt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt
    (eventually_gt_atTop 0 |>.mono fun L hL => ?_)
    (eventually_gt_atTop 0 |>.mono fun L hL => depthResolution_le_sqrt hL (hη L hL))
  have h1 : (1 : ℝ) ≤ 1 + η L / (2 * L) := by
    have : 0 ≤ η L / (2 * L) := div_nonneg (hη L hL) (by linarith)
    linarith
  exact div_nonneg (Real.arcosh_nonneg h1) hL.le

/-! ## §3. Policies with Prescribed Trans-Nyquist Aperture Growth (`A L > L / 2`) -/

/-- A **trans-Nyquist policy** prescribes an aperture strictly above `L / 2` and a nonnegative
deficit level at every scale `L > 0`, without restricting `A L` to the second aliasing band. -/
structure TransNyquistPolicy (A η : ℝ → ℝ) : Prop where
  aperture_lb : ∀ L : ℝ, 0 < L → L / 2 < A L
  level_nonneg : ∀ L : ℝ, 0 < L → 0 ≤ η L

/-- The aliasing index schedule `n(L) = ⌈2 * A L / L⌉₊` of an aperture policy `A`. -/
def aliasingIndex (A : ℝ → ℝ) (L : ℝ) : ℕ := ⌈2 * A L / L⌉₊

/-- Above the Nyquist aperture `L / 2 < A L`, the aliasing index is at least `2`. -/
theorem two_le_aliasingIndex {A : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hA : L / 2 < A L) :
    2 ≤ aliasingIndex A L := by
  rw [aliasingIndex]
  exact Nat.lt_ceil.mpr (by rw [Nat.cast_one, lt_div_iff₀ hL]; linarith)

/-- **Band-energy characterization of a general trans-Nyquist policy.** At any scale `L = sdScale p`
with `L / 2 < A L`, `adaptiveReading A η p` holds iff the `aliasingIndex A L`-th band energy is at
most `η L`. -/
theorem adaptiveReading_iff_bandEnergy_le {A η : ℝ → ℝ} {p : ScaleDepthDatum}
    (hA : sdScale p / 2 < A (sdScale p)) :
    adaptiveReading A η p ↔
      bandEnergy (sdScale p) (sdDepth p) (aliasingIndex A (sdScale p)) ≤ η (sdScale p) := by
  rw [adaptiveReading, sdConfig, offLineLattice_weilFloor_iff p.2.1 p.2.2.1 p.2.2.2 hA]
  rfl

/-- Strict positivity of `bandEnergy L δ n` for `L > 0`, `δ > 0`, and `n ≥ 2`. -/
theorem bandEnergy_pos_of_two_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n) :
    0 < bandEnergy L δ n := by
  have h0 : bandEnergy L 0 n = 0 := by simp [bandEnergy_eq_sum_cosh_sub_one]
  exact h0 ▸ bandEnergy_strictMono_depth hL le_rfl hδ hn

/-- Upper bound `bandEnergy L δ n ≤ M` whenever `δ ≤ arcosh(1 + M / (L * n)) / (n * L)`. -/
theorem bandEnergy_le_of_le_arcosh {L δ M : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hM : 0 ≤ M)
    {n : ℕ} (hn : 1 ≤ n) (hle : δ ≤ Real.arcosh (1 + M / (L * n)) / (n * L)) :
    bandEnergy L δ n ≤ M := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : δ * (n * L) ≤ Real.arcosh (1 + M / (L * n)) := by
    rwa [← le_div_iff₀ (by positivity)]
  have hquot_nn : 0 ≤ M / (L * n) := by positivity
  have h1 : (1 : ℝ) ≤ 1 + M / (L * n) := by linarith
  have harc_nn : 0 ≤ Real.arcosh (1 + M / (L * n)) := Real.arcosh_nonneg h1
  have hcosh : Real.cosh (δ * (n * L)) - 1 ≤ M / (L * n) := by
    have hc : Real.cosh (δ * (n * L)) ≤ Real.cosh (Real.arcosh (1 + M / (L * n))) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_pos (by positivity), abs_of_nonneg harc_nn]
        exact hprod)
    rw [Real.cosh_arcosh h1] at hc
    linarith
  calc bandEnergy L δ n ≤ L * n * (Real.cosh (δ * (n * L)) - 1) :=
        bandEnergy_le_mul_cosh hL.le hδ.le n
    _ ≤ L * n * (M / (L * n)) := mul_le_mul_of_nonneg_left hcosh (by positivity)
    _ = M := mul_div_cancel₀ _ (by positivity)

/-- **Pure-positivity refutation past the Nyquist threshold.** Any policy with `L / 2 < A L` and
zero deficit `η L = 0` refutes every off-line lattice datum at scale `L`. -/
theorem not_adaptiveReading_zero_of_transNyquist {A η : ℝ → ℝ} {p : ScaleDepthDatum}
    (hA : sdScale p / 2 < A (sdScale p)) (hη0 : η (sdScale p) = 0) :
    ¬ adaptiveReading A η p := by
  rw [adaptiveReading_iff_bandEnergy_le hA, hη0]
  exact not_le.mpr (bandEnergy_pos_of_two_le p.2.1 p.2.2.1 (two_le_aliasingIndex p.2.1 hA))

/-- **Two-mode hyperbolic lower bound on `bandEnergy`.** For every `L > 0`, `δ > 0`, and `n ≥ 2`,
the `n`-th band energy dominates `weilFloorThreshold L ((n - 1) * δ)`. -/
theorem weilFloorThreshold_mul_le_bandEnergy {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    {n : ℕ} (hn : 2 ≤ n) :
    weilFloorThreshold L (((n - 1 : ℕ) : ℝ) * δ) ≤ bandEnergy L δ n := by
  have hm : 1 ≤ n - 1 := by omega
  have hrec := bandEnergy_succ_sub_pred (mul_pos hδ hL) hm
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  rw [hsub] at hrec
  have hnn : 0 ≤ bandEnergy L δ (n - 1 - 1) := bandEnergy_nonneg hL.le δ (n - 1 - 1)
  have hthr : weilFloorThreshold L (((n - 1 : ℕ) : ℝ) * δ) =
      2 * L * (Real.cosh (((n - 1 : ℕ) : ℝ) * (δ * L)) - 1) := by
    rw [weilFloorThreshold, show ((n - 1 : ℕ) : ℝ) * δ * L = ((n - 1 : ℕ) : ℝ) * (δ * L) by ring]
  linarith

/-- **Multi-band depth resolution inversion.** If `bandEnergy L δ n ≤ η` with `L > 0`, `δ > 0`,
`η ≥ 0`, and `n ≥ 2`, then `δ ≤ depthResolution L η / (n - 1) ≤ √(η / L ^ 3) / (n - 1)`. -/
theorem depth_le_div_sub_one_of_bandEnergy_le {L δ η : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hη : 0 ≤ η)
    {n : ℕ} (hn : 2 ≤ n) (hle : bandEnergy L δ n ≤ η) :
    δ ≤ depthResolution L η / ((n - 1 : ℕ) : ℝ) ∧
      δ ≤ Real.sqrt (η / L ^ 3) / ((n - 1 : ℕ) : ℝ) := by
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast this
  have hthr : weilFloorThreshold L (((n - 1 : ℕ) : ℝ) * δ) ≤ η :=
    (weilFloorThreshold_mul_le_bandEnergy hL hδ hn).trans hle
  have hmul : ((n - 1 : ℕ) : ℝ) * δ ≤ depthResolution L η :=
    (weilFloorThreshold_le_iff hL (mul_pos hn1_pos hδ) hη).mp hthr
  have h1 : δ ≤ depthResolution L η / ((n - 1 : ℕ) : ℝ) := by
    rwa [le_div_iff₀ hn1_pos, mul_comm]
  have h2 : δ ≤ Real.sqrt (η / L ^ 3) / ((n - 1 : ℕ) : ℝ) :=
    h1.trans (div_le_div_of_nonneg_right (depthResolution_le_sqrt hL hη) hn1_pos.le)
  exact ⟨h1, h2⟩

/-- Continuity of `δ ↦ bandEnergy L δ n`. -/
theorem continuous_bandEnergy_depth (L : ℝ) (n : ℕ) :
    Continuous fun δ : ℝ => bandEnergy L δ n := by
  have heq : (fun δ : ℝ => bandEnergy L δ n) =
      fun δ : ℝ => L * ∑ j : Fin n, (Real.cosh ((δ * L) * (2 * (j : ℝ) - n + 1)) - 1) := by
    ext δ
    exact bandEnergy_eq_sum_cosh_sub_one L δ n
  rw [heq]
  fun_prop

/-- **Exact two-sided `arcosh` bracket for the resolution limit of a trans-Nyquist policy.**
At scale `L = sdScale p₀` with `L / 2 < A L`, `0 ≤ η L`, and `n = aliasingIndex A L ≥ 2`, the
scale-aware policy reading `scaleAdaptiveReading A η` has resolution floor `0` and resolution
limit bracketed between `min (1 / 2) (arcosh (1 + η L / (L * n)) / (n * L))` and
`min (1 / 2) (depthResolution L (η L) / (n - 1))`. -/
theorem resolutionLimit_sdDepth_scaleAdaptiveReading_brackets {A η : ℝ → ℝ}
    {p₀ : ScaleDepthDatum} (hA : sdScale p₀ / 2 < A (sdScale p₀))
    (hη : 0 ≤ η (sdScale p₀)) (hp₀ : adaptiveReading A η p₀) :
    min (1 / 2) (Real.arcosh (1 + η (sdScale p₀) / (sdScale p₀ * aliasingIndex A (sdScale p₀))) /
        (aliasingIndex A (sdScale p₀) * sdScale p₀)) ≤
      resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ ∧
    resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ ≤
      min (1 / 2) (depthResolution (sdScale p₀) (η (sdScale p₀)) /
        ((aliasingIndex A (sdScale p₀) - 1 : ℕ) : ℝ)) ∧
    resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 := by
  set L := sdScale p₀
  have hL : 0 < L := p₀.2.1
  set n := aliasingIndex A L
  have hn2 : 2 ≤ n := two_le_aliasingIndex hL hA
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hband₀ : bandEnergy L (sdDepth p₀) n ≤ η L :=
    (adaptiveReading_iff_bandEnergy_le hA).mp hp₀
  have hηpos : 0 < η L := lt_of_lt_of_le (bandEnergy_pos_of_two_le hL p₀.2.2.1 hn2) hband₀
  have hbdd : BddAbove (sdDepth '' shadow (scaleAdaptiveReading A η) p₀) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · set δ₀ := min (1 / 2 : ℝ) (Real.arcosh (1 + η L / (L * n)) / ((n : ℝ) * L))
    have hquot_pos : 0 < η L / (L * n) := by positivity
    have harc_pos : 0 < Real.arcosh (1 + η L / (L * n)) := Real.arcosh_pos (by linarith)
    have hδ₀_pos : 0 < δ₀ := lt_min (by norm_num) (by positivity)
    have hδ₀_le : δ₀ ≤ 1 / 2 := min_le_left _ _
    set p_low : ScaleDepthDatum := ⟨(L, δ₀), hL, hδ₀_pos, hδ₀_le⟩
    have hband_low : bandEnergy L δ₀ n ≤ η L :=
      bandEnergy_le_of_le_arcosh hL hδ₀_pos hη hn1 (min_le_right _ _)
    have hA_low : sdScale p_low / 2 < A (sdScale p_low) := hA
    have hread_low : adaptiveReading A η p_low :=
      (adaptiveReading_iff_bandEnergy_le hA_low).mpr hband_low
    have hmem : p_low ∈ shadow (scaleAdaptiveReading A η) p₀ :=
      mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread_low hp₀⟩
    exact le_csSup hbdd ⟨p_low, hmem, rfl⟩
  · refine csSup_le (shadow_image_nonempty sdDepth (scaleAdaptiveReading A η) p₀) ?_
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hscale, hiff⟩ := mem_shadow_scaleAdaptiveReading_iff.mp hp
    have hread : adaptiveReading A η p := hiff.mpr hp₀
    have hA_p : sdScale p / 2 < A (sdScale p) := by rw [hscale]; exact hA
    have hband : bandEnergy L (sdDepth p) n ≤ η L := by
      have hb := (adaptiveReading_iff_bandEnergy_le hA_p).mp hread
      rwa [hscale] at hb
    exact le_min p.2.2.2 (depth_le_div_sub_one_of_bandEnergy_le hL p.2.2.1 hη hn2 hband).1
  · have hbdd_low : BddBelow (sdDepth '' shadow (scaleAdaptiveReading A η) p₀) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le
    refine le_antisymm ?_
      (le_csInf (shadow_image_nonempty sdDepth (scaleAdaptiveReading A η) p₀) ?_)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      set δ := min (sdDepth p₀) (ε / 2)
      have hδ0 : 0 < δ := lt_min p₀.2.2.1 (by linarith)
      have hδp₀ : δ ≤ sdDepth p₀ := min_le_left _ _
      set p_δ : ScaleDepthDatum := ⟨(L, δ), hL, hδ0, hδp₀.trans p₀.2.2.2⟩
      have hband_δ : bandEnergy L δ n ≤ η L :=
        (bandEnergy_mono_depth hL.le hδ0.le hδp₀ n).trans hband₀
      have hA_δ : sdScale p_δ / 2 < A (sdScale p_δ) := hA
      have hread_δ : adaptiveReading A η p_δ :=
        (adaptiveReading_iff_bandEnergy_le hA_δ).mpr hband_δ
      have hmem : p_δ ∈ shadow (scaleAdaptiveReading A η) p₀ :=
        mem_shadow_scaleAdaptiveReading_iff.mpr ⟨rfl, iff_of_true hread_δ hp₀⟩
      exact (csInf_le hbdd_low ⟨p_δ, hmem, rfl⟩).trans ((min_le_right _ _).trans (by linarith))
    · rintro _ ⟨p, -, rfl⟩
      exact p.2.2.1.le

/-- **Exact certification equivalence for general trans-Nyquist policies.** For any
`TransNyquistPolicy A η`, any target depth `0 < β < 1 / 2`, and any `p₀` with
`adaptiveReading A η p₀`: `Certifies sdDepth (adaptiveReading A η) p₀ β` holds if and only if
`∀ L > 0, η L ≤ bandEnergy L β (aliasingIndex A L)`. -/
theorem certifies_sdDepth_adaptiveReading_transNyquist_iff {A η : ℝ → ℝ}
    (h : TransNyquistPolicy A η) {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2)
    {p₀ : ScaleDepthDatum} (hp₀ : adaptiveReading A η p₀) :
    Certifies sdDepth (adaptiveReading A η) p₀ β ↔
      ∀ L : ℝ, 0 < L → η L ≤ bandEnergy L β (aliasingIndex A L) := by
  constructor
  · intro hcert L hL
    set n := aliasingIndex A L
    have hn2 : 2 ≤ n := two_le_aliasingIndex hL (h.aperture_lb L hL)
    by_contra hgt
    rw [not_le] at hgt
    have hev : ∀ᶠ δ : ℝ in 𝓝 β, bandEnergy L δ n < η L :=
      (continuous_bandEnergy_depth L n).continuousAt.eventually (gt_mem_nhds hgt)
    obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.mp hev
    set β' := min (1 / 2 : ℝ) (β + r / 2)
    have hβ'gt : β < β' := lt_min hβ (by linarith)
    have hβ'0 : 0 < β' := hβ0.trans hβ'gt
    have hβ'le : β' ≤ 1 / 2 := min_le_left _ _
    have hdist : dist β' β < r := by
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < β' - β)]
      have : β' ≤ β + r / 2 := min_le_right _ _
      linarith
    have hband_lt : bandEnergy L β' n < η L := hr hdist
    set p_β' : ScaleDepthDatum := ⟨(L, β'), hL, hβ'0, hβ'le⟩
    have hread : adaptiveReading A η p_β' :=
      (adaptiveReading_iff_bandEnergy_le (h.aperture_lb L hL)).mpr hband_lt.le
    have hmem : p_β' ∈ shadow (adaptiveReading A η) p₀ := propext (iff_of_true hread hp₀)
    exact absurd (hcert p_β' hmem) (not_le.mpr hβ'gt)
  · intro hall p hp
    have hread : adaptiveReading A η p := (mem_shadow_iff.mp hp) ▸ hp₀
    set L := sdScale p
    have hL : 0 < L := p.2.1
    set n := aliasingIndex A L
    have hn2 : 2 ≤ n := two_le_aliasingIndex hL (h.aperture_lb L hL)
    have hband : bandEnergy L (sdDepth p) n ≤ bandEnergy L β n :=
      ((adaptiveReading_iff_bandEnergy_le (h.aperture_lb L hL)).mp hread).trans (hall L hL)
    by_contra hgt
    rw [not_le] at hgt
    exact absurd hband (not_le.mpr (bandEnergy_strictMono_depth hL hβ0.le hgt hn2))

/-! ## §4. Unconditionally Realisable Schedules for `ζ` at Growing Density -/

/-- The local archimedean density scale `L(ξ) = log(1 + π|ξ|/4)` of `ζ` at height shift `ξ`. -/
def zetaHeightScale (ξ : ℝ) : ℝ := Real.log (1 + Real.pi * |ξ| / 4)

/-- The archimedean density scale is strictly positive at every nonzero height shift `ξ ≠ 0`. -/
theorem zetaHeightScale_pos {ξ : ℝ} (hξ : ξ ≠ 0) : 0 < zetaHeightScale ξ := by
  rw [zetaHeightScale]
  have h1 : 0 < Real.pi * |ξ| / 4 := div_pos (mul_pos Real.pi_pos (abs_pos.mpr hξ)) (by norm_num)
  exact Real.log_pos (by linarith)

/-- The sharp PNT single-height symbol-positivity aperture `log(1 + L / 4)` at density scale `L`. -/
def sharpHorizonAperture (L : ℝ) : ℝ := Real.log (1 + L / 4)

/-- The unconditional Chebyshev single-height positivity aperture `log(1 + L / 70)` at scale `L`. -/
def archimedeanHorizonAperture (L : ℝ) : ℝ := Real.log (1 + L / 70)

/-- The unconditional Chebyshev global deficit schedule `10 + 68 e^A = horizonExponent (e^{2A})`. -/
def chebyshevDeficit (A : ℝ) : ℝ := horizonExponent (Real.exp (2 * A))

/-- Closed form `chebyshevDeficit A = 10 + 68 * Real.exp A`. -/
theorem chebyshevDeficit_eq (A : ℝ) : chebyshevDeficit A = 10 + 68 * Real.exp A := by
  rw [chebyshevDeficit, horizonExponent, show 2 * A = A + A by ring, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos A).le]

/-- **Sub-Nyquist confinement of single-height positivity horizons.** For every scale `L > 0`,
both `archimedeanHorizonAperture L` and `sharpHorizonAperture L` lie strictly below `L / 4 < L / 2`. -/
theorem sharpHorizonAperture_lt_half_scale {L : ℝ} (hL : 0 < L) :
    archimedeanHorizonAperture L ≤ sharpHorizonAperture L ∧
      sharpHorizonAperture L ≤ L / 4 ∧
      sharpHorizonAperture L < L / 2 := by
  have h1 : archimedeanHorizonAperture L ≤ sharpHorizonAperture L := by
    rw [archimedeanHorizonAperture, sharpHorizonAperture]
    exact Real.log_le_log (by positivity) (by linarith)
  have h2 : sharpHorizonAperture L ≤ L / 4 := by
    rw [sharpHorizonAperture]
    have hexp : 1 + L / 4 ≤ Real.exp (L / 4) := by
      have := Real.add_one_le_exp (L / 4)
      linarith
    calc Real.log (1 + L / 4) ≤ Real.log (Real.exp (L / 4)) :=
          Real.log_le_log (by positivity) hexp
      _ = L / 4 := Real.log_exp (L / 4)
  exact ⟨h1, h2, by linarith⟩

/-- **Realisability of the Chebyshev single-height positivity schedule on `ζ`.** For every height
`ξ` with `zetaHeightScale ξ ≥ 80`, every aperture `0 ≤ a ≤ Real.log ((zetaHeightScale ξ - 10) / 70)`
satisfies `a < zetaHeightScale ξ / 2` and makes the main-term coefficient
`zetaHeightScale ξ - horizonExponent (e^{2a}) - 2 * pairEnergy (1 / 2) a` in
`zetaZeroConfig_re_W_heightShift_ge` nonnegative. -/
theorem zeta_singleHeight_archimedean_schedule_realisable {ξ a : ℝ}
    (hL80 : 80 ≤ zetaHeightScale ξ) (ha0 : 0 ≤ a)
    (ha : a ≤ Real.log ((zetaHeightScale ξ - 10) / 70)) :
    a < zetaHeightScale ξ / 2 ∧
      0 ≤ zetaHeightScale ξ - horizonExponent (Real.exp (2 * a)) - 2 * pairEnergy (1 / 2) a ∧
      ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        -((4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + Real.pi * |ξ|))) ≤
          (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  set L := zetaHeightScale ξ
  have hLpos : 0 < L := by linarith
  have hquot1 : 1 ≤ (L - 10) / 70 := by linarith
  have hexp_a : Real.exp a ≤ (L - 10) / 70 := by
    rw [← Real.log_exp a] at ha
    exact (Real.log_le_log_iff (Real.exp_pos a) (by linarith)).mp ha
  have hpair : 2 * pairEnergy (1 / 2) a ≤ Real.exp a := by
    rw [pairEnergy, show 2 * (1 / 2 : ℝ) * a = a by ring, show 2 * (1 / 2 : ℝ) = 1 by ring,
      div_one, Real.sinh_eq]
    have h_neg : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h_pos : 1 ≤ Real.exp a := Real.one_le_exp ha0
    linarith [Real.exp_pos (-a)]
  have hhor : horizonExponent (Real.exp (2 * a)) = 10 + 68 * Real.exp a := by
    rw [horizonExponent, show 2 * a = a + a by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos a).le]
  have hmain : 0 ≤ L - horizonExponent (Real.exp (2 * a)) - 2 * pairEnergy (1 / 2) a := by
    rw [hhor]
    linarith
  have ha_lt : a < L / 2 := by
    have hle_sharp : a ≤ sharpHorizonAperture L := by
      refine ha.trans (Real.log_le_log (by linarith) (by linarith))
    exact hle_sharp.trans_lt (sharpHorizonAperture_lt_half_scale hLpos).2.2
  refine ⟨ha_lt, hmain, fun {f} hf hfs => ?_⟩
  have hge := zetaZeroConfig_re_W_heightShift_ge ha0 hf hfs ξ
  rw [← zetaHeightScale] at hge
  have hN : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hprod : 0 ≤ (L - horizonExponent (Real.exp (2 * a)) - 2 * pairEnergy (1 / 2) a) *
      ∫ t, ‖f t‖ ^ 2 := mul_nonneg hmain hN
  linarith

/-- **Floor of any policy confined to the single-height symbol-positivity horizon.** Any policy
`(A, η)` with `A L ≤ sharpHorizonAperture L` and `0 ≤ η L` for all `L > 0` has exact resolution
limit `1 / 2` and resolution floor `0` under both `adaptiveReading A η` and
`scaleAdaptiveReading A η`. -/
theorem resolutionLimit_sdDepth_of_le_sharpHorizonAperture {A η : ℝ → ℝ}
    (hA : ∀ L : ℝ, 0 < L → A L ≤ sharpHorizonAperture L)
    (hη : ∀ L : ℝ, 0 < L → 0 ≤ η L) (p₀ : ScaleDepthDatum) :
    resolutionLimit sdDepth (adaptiveReading A η) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (adaptiveReading A η) p₀ = 0 ∧
      resolutionLimit sdDepth (scaleAdaptiveReading A η) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (scaleAdaptiveReading A η) p₀ = 0 := by
  have hsub : ∀ L : ℝ, 0 < L → A L ≤ L / 2 := fun L hL =>
    (hA L hL).trans (sharpHorizonAperture_lt_half_scale hL).2.2.le
  have hp₀ : adaptiveReading A η p₀ :=
    adaptiveReading_of_subNyquist (hsub (sdScale p₀) p₀.2.1) (hη (sdScale p₀) p₀.2.1)
  have hex : ∃ L : ℝ, 0 < L ∧ A L ≤ L / 2 ∧ 0 ≤ η L :=
    ⟨1, one_pos, hsub 1 one_pos, hη 1 one_pos⟩
  have hsc := resolutionLimit_sdDepth_scaleAdaptiveReading_of_subNyquist
    (hsub (sdScale p₀) p₀.2.1) (hη (sdScale p₀) p₀.2.1)
  exact ⟨resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist hex hp₀,
    resolutionFloor_sdDepth_adaptiveReading_of_exists_subNyquist hex hp₀,
    hsc.1, hsc.2.1⟩

/-- **The unconditional Chebyshev deficit at `A = L` exceeds the maximal lattice threshold.**
For every scale `L > 0`, `weilFloorThreshold L (1 / 2) ≤ chebyshevDeficit L`. -/
theorem weilFloorThreshold_half_le_chebyshevDeficit {L : ℝ} (hL : 0 < L) :
    weilFloorThreshold L (1 / 2) ≤ chebyshevDeficit L := by
  rw [weilFloorThreshold, chebyshevDeficit_eq, Real.cosh_eq]
  have h1 : Real.exp (-(1 / 2 * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : L ≤ Real.exp (L / 2) := by
    have hq := one_add_add_sq_quarter_le_exp (by positivity : 0 ≤ L / 2)
    have hsq : 0 ≤ (L / 4 - 1) ^ 2 := sq_nonneg _
    nlinarith
  have h3 : Real.exp (1 / 2 * L) = Real.exp (L / 2) := by ring_nf
  have h4 : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    ring_nf
  calc 2 * L * ((Real.exp (1 / 2 * L) + Real.exp (-(1 / 2 * L))) / 2 - 1)
      ≤ 2 * L * ((Real.exp (L / 2) + 1) / 2 - 1) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ L * Real.exp (L / 2) := by linarith
    _ ≤ Real.exp (L / 2) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp L := h4.symm
    _ ≤ 10 + 68 * Real.exp L := by linarith [Real.exp_pos L]

/-- The scale-matched Nyquist policy `(id, chebyshevDeficit)` satisfies `ScaleMatched`. -/
theorem scaleMatched_id_chebyshevDeficit : ScaleMatched id chebyshevDeficit where
  aperture_lb L hL := by simp; linarith
  aperture_ub L _ := le_rfl
  level_nonneg L _ := by
    rw [chebyshevDeficit_eq]
    positivity

/-- **Exact resolution limit of the scale-matched Chebyshev policy.** Because the unconditional
prime-sum bound `chebyshevDeficit L = 10 + 68 e^L` grows as `e^L > L e^{L/2}`, the scale-matched
policy `(id, chebyshevDeficit)` admits every depth `δ ∈ (0, 1 / 2]` at every scale `L > 0`, and
therefore has exact resolution limit `1 / 2` and resolution floor `0` under both
`scaleAdaptiveReading` and `adaptiveReading`. -/
theorem resolutionLimit_sdDepth_chebyshevSchedule_eq_half (p₀ : ScaleDepthDatum) :
    adaptiveReading id chebyshevDeficit p₀ ∧
      resolutionLimit sdDepth (scaleAdaptiveReading id chebyshevDeficit) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (scaleAdaptiveReading id chebyshevDeficit) p₀ = 0 ∧
      resolutionLimit sdDepth (adaptiveReading id chebyshevDeficit) p₀ = 1 / 2 ∧
      resolutionFloor sdDepth (adaptiveReading id chebyshevDeficit) p₀ = 0 := by
  have hsm := scaleMatched_id_chebyshevDeficit
  have hhalf_le : ∀ L : ℝ, 0 < L → 1 / 2 ≤ depthResolution L (chebyshevDeficit L) := fun L hL =>
    (weilFloorThreshold_le_iff hL (by norm_num) (hsm.level_nonneg L hL)).mp
      (weilFloorThreshold_half_le_chebyshevDeficit hL)
  have hp₀ : adaptiveReading id chebyshevDeficit p₀ :=
    (adaptiveReading_iff hsm p₀).mpr (p₀.2.2.2.trans (hhalf_le (sdScale p₀) p₀.2.1))
  have hsc := resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched hsm hp₀
  have hmin : min (1 / 2 : ℝ) (depthResolution (sdScale p₀) (chebyshevDeficit (sdScale p₀))) =
      1 / 2 := min_eq_left (hhalf_le (sdScale p₀) p₀.2.1)
  have hglob : resolutionLimit sdDepth (adaptiveReading id chebyshevDeficit) p₀ = 1 / 2 := by
    set p_max : ScaleDepthDatum := ⟨(sdScale p₀, 1 / 2), p₀.2.1, by norm_num, le_rfl⟩
    have hread_max : adaptiveReading id chebyshevDeficit p_max :=
      (adaptiveReading_iff hsm p_max).mpr (hhalf_le (sdScale p₀) p₀.2.1)
    have hmem : p_max ∈ shadow (adaptiveReading id chebyshevDeficit) p₀ :=
      propext (iff_of_true hread_max hp₀)
    exact resolutionLimit_eq_of_mem_shadow_of_max (fun p => p.2.2.2) hmem rfl
  exact ⟨hp₀, hsc.1.trans hmin, hsc.2.1, hglob,
    resolutionFloor_sdDepth_adaptiveReading_scaleMatched hsm hp₀⟩

end

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
