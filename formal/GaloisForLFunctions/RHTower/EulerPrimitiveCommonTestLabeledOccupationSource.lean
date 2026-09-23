import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedChainSource
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Prime-power-labelled occupation lift of the polarized Euler boundary

The polarized head/tail weights are not inserted after the critical-clock
limit.  At finite `σ > 1`, every retained prime-power label `n` has moving
horizon

`Tσ(n) = (σ - 1) log n`.

At physical time `u`, the label lies in exactly one incidence sector:

* head: `u < Tσ(n)`;
* tail: `Tσ(n) ≤ u`.

This file keeps those labelled cells before summation.  Their pointwise sum
is the full normalized von-Mangoldt probability, and their total masses
partition one.  Weak convergence of the literal Euler clock then proves

`head mass -> exp (-u)`, `tail mass -> 1 - exp (-u)`.

Consequently the two weights in
`EulerPrimitiveCommonTestPolarizedChainSource` are the exact cofinal limits
of a prime-power-labelled incidence complex.  The singular Hodge scale
`sqrt(exp u - 1)` is therefore the limiting ratio between two arithmetic
occupation sectors, not a post-divisor scalar choice.

No divisor enumeration or RH premise is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators Topology ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Labelled finite-temperature occupation cells -/

/-- Prime-power cell on the compact-head side of the moving horizon. -/
def eulerPrimitiveBoundaryHeadOccupationCell
    (sigma u : ℝ) (n : ℕ) : ℝ :=
  ({n : ℕ | u < eulerPrimeCurrentClock sigma n}.indicator
    (eulerPrimeCurrentProbability sigma)) n

/-- Prime-power cell on the escaping-tail side of the moving horizon. -/
def eulerPrimitiveBoundaryTailOccupationCell
    (sigma u : ℝ) (n : ℕ) : ℝ :=
  ({n : ℕ | eulerPrimeCurrentClock sigma n ≤ u}.indicator
    (eulerPrimeCurrentProbability sigma)) n

/-- Vector-valued labelled occupation cochain before codiagonal summation. -/
def eulerPrimitiveBoundaryLabeledOccupationCochain
    (sigma u : ℝ) : ℕ → ℝ × ℝ :=
  fun n =>
    (eulerPrimitiveBoundaryHeadOccupationCell sigma u n,
      eulerPrimitiveBoundaryTailOccupationCell sigma u n)

theorem summable_eulerPrimitiveBoundaryHeadOccupationCell
    {sigma : ℝ} (hsigma : 1 < sigma) (u : ℝ) :
    Summable (eulerPrimitiveBoundaryHeadOccupationCell sigma u) := by
  exact
    (summable_eulerPrimeCurrentProbability hsigma).indicator
      {n : ℕ | u < eulerPrimeCurrentClock sigma n}

theorem summable_eulerPrimitiveBoundaryTailOccupationCell
    {sigma : ℝ} (hsigma : 1 < sigma) (u : ℝ) :
    Summable (eulerPrimitiveBoundaryTailOccupationCell sigma u) := by
  exact
    (summable_eulerPrimeCurrentProbability hsigma).indicator
      {n : ℕ | eulerPrimeCurrentClock sigma n ≤ u}

/-- Every label occurs in exactly one side of the incidence cut. -/
theorem eulerPrimitiveBoundaryOccupationCell_add
    (sigma u : ℝ) (n : ℕ) :
    eulerPrimitiveBoundaryHeadOccupationCell sigma u n +
        eulerPrimitiveBoundaryTailOccupationCell sigma u n =
      eulerPrimeCurrentProbability sigma n := by
  by_cases h : eulerPrimeCurrentClock sigma n ≤ u
  · simp [eulerPrimitiveBoundaryHeadOccupationCell,
      eulerPrimitiveBoundaryTailOccupationCell, h,
      not_lt.mpr h]
  · have h' : u < eulerPrimeCurrentClock sigma n := lt_of_not_ge h
    simp [eulerPrimitiveBoundaryHeadOccupationCell,
      eulerPrimitiveBoundaryTailOccupationCell, h, h']

/-- Aggregate compact-head occupation mass. -/
def eulerPrimitiveBoundaryHeadOccupationMass
    (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, eulerPrimitiveBoundaryHeadOccupationCell sigma u n

/-- Aggregate escaping-tail occupation mass. -/
def eulerPrimitiveBoundaryTailOccupationMass
    (sigma u : ℝ) : ℝ :=
  ∑' n : ℕ, eulerPrimitiveBoundaryTailOccupationCell sigma u n

/-- Exact finite-temperature conservation of the normalized source mass. -/
theorem eulerPrimitiveBoundaryOccupationMass_add
    {sigma : ℝ} (hsigma : 1 < sigma) (u : ℝ) :
    eulerPrimitiveBoundaryHeadOccupationMass sigma u +
        eulerPrimitiveBoundaryTailOccupationMass sigma u = 1 := by
  rw [eulerPrimitiveBoundaryHeadOccupationMass,
    eulerPrimitiveBoundaryTailOccupationMass,
    ← (summable_eulerPrimitiveBoundaryHeadOccupationCell hsigma u).tsum_add
      (summable_eulerPrimitiveBoundaryTailOccupationCell hsigma u),
    tsum_congr (eulerPrimitiveBoundaryOccupationCell_add sigma u),
    tsum_eulerPrimeCurrentProbability hsigma]

/-! ## Identification with the literal Euler-clock distribution -/

/-- CDF of the literal normalized von-Mangoldt clock. -/
def eulerPrimeCurrentClockCDF (sigma u : ℝ) : ℝ :=
  ProbabilityTheory.cdf
    (eulerPrimeCurrentClockProbabilityMeasure sigma : Measure ℝ) u

theorem eulerPrimitiveBoundaryTailOccupationMass_eq_cdf
    {sigma : ℝ} (hsigma : 1 < sigma) (u : ℝ) :
    eulerPrimitiveBoundaryTailOccupationMass sigma u =
      eulerPrimeCurrentClockCDF sigma u := by
  rw [eulerPrimitiveBoundaryTailOccupationMass,
    eulerPrimeCurrentClockCDF, ProbabilityTheory.cdf_eq_real,
    Measure.real]
  unfold eulerPrimeCurrentClockProbabilityMeasure
    eulerPrimeCurrentIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iic,
    PMF.toMeasure_apply_eq_tsum]
  have hfinite :
      ∀ n : ℕ,
        (eulerPrimeCurrentClock sigma ⁻¹' Iic u).indicator
          (eulerPrimeCurrentPMF sigma) n ≠ ∞ := by
    intro n
    by_cases hn :
        n ∈ eulerPrimeCurrentClock sigma ⁻¹' Iic u
    · simpa [Set.indicator, hn] using
        (eulerPrimeCurrentPMF sigma).apply_ne_top n
    · simp [Set.indicator, hn]
  rw [ENNReal.tsum_toReal_eq hfinite]
  apply tsum_congr
  intro n
  by_cases h : eulerPrimeCurrentClock sigma n ≤ u
  · simp [eulerPrimitiveBoundaryTailOccupationCell, h,
      eulerPrimeCurrentPMF_toReal hsigma]
  · simp [eulerPrimitiveBoundaryTailOccupationCell, h]

/-- Euler-clock CDF converges pointwise to the unit exponential CDF. -/
theorem tendsto_eulerPrimeCurrentClockCDF (u : ℝ) :
    Tendsto (fun sigma : ℝ => eulerPrimeCurrentClockCDF sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if 0 ≤ u then 1 - Real.exp (-u) else 0)) := by
  have hnull :
      mobiusCriticalExponentialProbabilityMeasure (frontier (Iic u)) = 0 := by
    rw [frontier_Iic]
    ext
    simp [mobiusCriticalExponentialProbabilityMeasure,
      ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  have hmeasure :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      tendsto_eulerPrimeCurrentClockProbabilityMeasure hnull
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp hmeasure
  have hreal' :
      Tendsto
        (fun sigma : ℝ =>
          ProbabilityTheory.cdf
            (eulerPrimeCurrentClockProbabilityMeasure sigma :
              Measure ℝ) u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (ProbabilityTheory.cdf
          (mobiusCriticalExponentialProbabilityMeasure :
            Measure ℝ) u)) := by
    simpa [Function.comp_apply, ProbabilityTheory.cdf_eq_real,
      Measure.real, ProbabilityMeasure.coe_mk] using! hreal
  have hlimit :=
    ProbabilityTheory.cdf_expMeasure_eq (r := (1 : ℝ))
      (by norm_num) u
  simpa [eulerPrimeCurrentClockCDF,
    mobiusCriticalExponentialProbabilityMeasure, hlimit] using hreal'

theorem tendsto_eulerPrimitiveBoundaryTailOccupationMass
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerPrimitiveBoundaryTailOccupationMass sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveBoundaryTailWeight u)) := by
  have heq :
      ∀ᶠ sigma in nhdsWithin 1 (Ioi 1),
        eulerPrimitiveBoundaryTailOccupationMass sigma u =
          eulerPrimeCurrentClockCDF sigma u := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact eulerPrimitiveBoundaryTailOccupationMass_eq_cdf hsigma u
  have heq' :
      ∀ᶠ sigma in nhdsWithin 1 (Ioi 1),
        eulerPrimeCurrentClockCDF sigma u =
          eulerPrimitiveBoundaryTailOccupationMass sigma u :=
    heq.mono fun _ h => h.symm
  have h :=
    (tendsto_eulerPrimeCurrentClockCDF u).congr' heq'
  simpa [hu, eulerPrimitiveBoundaryTailWeight] using h

theorem tendsto_eulerPrimitiveBoundaryHeadOccupationMass
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        eulerPrimitiveBoundaryHeadOccupationMass sigma u)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveBoundaryHeadWeight u)) := by
  have heq :
      ∀ᶠ sigma in nhdsWithin 1 (Ioi 1),
        eulerPrimitiveBoundaryHeadOccupationMass sigma u =
          1 - eulerPrimitiveBoundaryTailOccupationMass sigma u := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    linarith [eulerPrimitiveBoundaryOccupationMass_add hsigma u]
  have htail :=
    tendsto_eulerPrimitiveBoundaryTailOccupationMass hu
  have hsub :
      Tendsto
        (fun sigma : ℝ =>
          1 - eulerPrimitiveBoundaryTailOccupationMass sigma u)
        (nhdsWithin 1 (Ioi 1))
        (nhds (1 - eulerPrimitiveBoundaryTailWeight u)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 1 (Ioi 1)) (nhds 1)).sub htail
  have heq' :
      ∀ᶠ sigma in nhdsWithin 1 (Ioi 1),
        1 - eulerPrimitiveBoundaryTailOccupationMass sigma u =
          eulerPrimitiveBoundaryHeadOccupationMass sigma u :=
    heq.mono fun _ h => h.symm
  have h := hsub.congr' heq'
  simpa [eulerPrimitiveBoundaryHeadWeight,
    eulerPrimitiveBoundaryTailWeight] using h

/--
The singular Hodge scale is the exact limiting occupation-mass ratio:
`q(u)^(2 : ℕ) * head(u) = tail(u)`.
-/
theorem eulerPrimitiveBoundaryHodgeScale_sq_mul_headWeight
    {u : ℝ} (hu : 0 < u) :
    eulerPrimitiveBoundaryHodgeScale u ^ 2 *
        eulerPrimitiveBoundaryHeadWeight u =
      eulerPrimitiveBoundaryTailWeight u := by
  rw [eulerPrimitiveBoundaryHodgeScale_sq hu]
  unfold eulerPrimitiveBoundaryHeadWeight
    eulerPrimitiveBoundaryTailWeight
  rw [show Real.exp (-u) = (Real.exp u)⁻¹ by
    exact Real.exp_neg u]
  field_simp [(Real.exp_pos u).ne']

end

end RHTower
