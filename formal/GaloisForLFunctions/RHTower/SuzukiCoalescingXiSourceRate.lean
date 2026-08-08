import GaloisForLFunctions.RHTower.SuzukiXiSecondDefectJet
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Suzuki's coalescing Xi defect and its theta-source rate

The movable deficiency base `±ic` reads the shifted reciprocal-square Xi moments at `y = c²`.
This file closes the previously missing endpoint regularity at `y = 0`: dominated convergence over
the multiplicity-exact divisor proves that every shifted moment reaches the central moment, and the
existing prime--Gamma transport identifies that boundary value with the normalized source moment.

Consequently the normalized coalescing defect has the exact positive theta-source tangent

`tau = normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0`.

For positive anchors the same defect is exactly `c L'(c) / L(c)`, where `L` is the positive-ray
Xi logarithmic derivative.  No RH hypothesis, fitted divisor value, or numerical computation is
used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- At zero shift, every multiplicity-exact shifted reciprocal moment is exactly its fixed
prime--archimedean source moment. -/
theorem xiShiftedReciprocalMoment_zero_eq_normalizedPrimeArchMoment (m : ℕ) :
    xiShiftedReciprocalMoment 0 m = (normalizedPrimeArchMoment m : ℂ) := by
  rw [xiShiftedReciprocalMoment_eq_centralNegativeBinomial
    (y := 0) (by positivity) (by norm_num) m]
  rw [tsum_eq_single 0]
  · simp [ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment]
  · intro r hr
    simp [hr]

/-- The shifted reciprocal moment tower is right-continuous at the central squared coordinate.
The proof is direct divisor-level dominated convergence, so the boundary value is not inferred
from a formal power-series placeholder. -/
theorem tendsto_xiShiftedReciprocalMoment_nhdsGE_zero (m : ℕ) :
    Tendsto (fun y : ℝ => xiShiftedReciprocalMoment y m)
      (𝓝[≥] (0 : ℝ)) (𝓝 (normalizedPrimeArchMoment m : ℂ)) := by
  have hpoint (q : XiZeroCopy) :
      Tendsto (fun y : ℝ => xiShiftedReciprocalSquare y q ^ (m + 1))
        (𝓝[≥] (0 : ℝ))
        (𝓝 (xiZeroCopyReciprocalSquare q ^ (m + 1))) := by
    have hy : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≥] (0 : ℝ)) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hden : Tendsto
        (fun y : ℝ => 1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)
        (𝓝[≥] (0 : ℝ)) (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hy.mul tendsto_const_nhds)
    have hquot : Tendsto
        (fun y : ℝ => xiZeroCopyReciprocalSquare q /
          (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q))
        (𝓝[≥] (0 : ℝ)) (𝓝 (xiZeroCopyReciprocalSquare q)) := by
      change Tendsto
        ((fun _ : ℝ => xiZeroCopyReciprocalSquare q) /
          (fun y : ℝ => 1 + (y : ℂ) * xiZeroCopyReciprocalSquare q))
        (𝓝[≥] (0 : ℝ)) (𝓝 (xiZeroCopyReciprocalSquare q))
      simpa using tendsto_const_nhds.div hden one_ne_zero
    simpa only [xiShiftedReciprocalSquare] using hquot.pow (m + 1)
  have hbound : ∀ᶠ y : ℝ in 𝓝[≥] (0 : ℝ), ∀ q : XiZeroCopy,
      ‖xiShiftedReciprocalSquare y q ^ (m + 1)‖ ≤
        ‖xiZeroCopyReciprocalSquare q ^ (m + 1)‖ := by
    filter_upwards [self_mem_nhdsWithin] with y hy q
    rw [norm_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_xiShiftedReciprocalSquare_le hy q) _
  have hsum := (summable_xiZeroCopyReciprocalSquare_pow m).norm
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa only [xiShiftedReciprocalMoment,
    tsum_xiZeroCopyReciprocalSquare_pow,
    ← ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment] using hlim

/-- Pre-divisor source definition of the coalescing Xi comparison rate. -/
def suzukiXiCoalescingSourceRate : ℝ :=
  normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0

/-- The coalescing comparison rate is strictly positive, unconditionally. -/
theorem suzukiXiCoalescingSourceRate_pos :
    0 < suzukiXiCoalescingSourceRate := by
  exact div_pos normalizedPrimeArchMoment_one_pos
    normalizedPrimeArchMoment_zero_pos

/-- Exact theta-cusp calibration of the coalescing comparison rate. -/
theorem suzukiXiCoalescingSourceRate_eq_theta :
    suzukiXiCoalescingSourceRate =
      thetaCuspNormalizedEvenMoment 1 / 2 -
        thetaCuspNormalizedEvenMoment 2 /
          (6 * thetaCuspNormalizedEvenMoment 1) := by
  rw [suzukiXiCoalescingSourceRate,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
  have hne : thetaCuspNormalizedEvenMoment 1 ≠ 0 := by
    rw [← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact normalizedPrimeArchMoment_zero_pos.ne'
  field_simp [hne]

/-- Movable-anchor Xi defect in the squared reciprocal-moment coordinate. -/
def suzukiXiCoalescingDefect (c : ℝ) : ℝ :=
  1 - 2 * c ^ 2 *
    (xiShiftedReciprocalMoment (c ^ 2) 1).re /
      (xiShiftedReciprocalMoment (c ^ 2) 0).re

/-- Source-only presentation of the same coalescing defect inside the convergent
negative-binomial source disk. -/
def suzukiPrimeArchCoalescingDefect (c : ℝ) : ℝ :=
  1 - 2 * c ^ 2 *
    (primeArchShiftedReciprocalMoment (c ^ 2) 1).re /
      (primeArchShiftedReciprocalMoment (c ^ 2) 0).re

/-- The divisor and prime--Gamma presentations of the movable defect agree exactly throughout the
source transport window. -/
theorem suzukiXiCoalescingDefect_eq_primeArch
    {c : ℝ} (hcmax : c ^ 2 < 41 / 2) :
    suzukiXiCoalescingDefect c = suzukiPrimeArchCoalescingDefect c := by
  rw [suzukiXiCoalescingDefect, suzukiPrimeArchCoalescingDefect,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (sq_nonneg c) hcmax 0,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (sq_nonneg c) hcmax 1]

/-- Exact positive-ray logarithmic-derivative form `kappa(c) = c L'(c) / L(c)`. -/
theorem suzukiXiCoalescingDefect_eq_logDeriv_ratio
    {c : ℝ} (hc : 0 < c) :
    suzukiXiCoalescingDefect c =
      c * deriv xiRealLogDeriv c / xiRealLogDeriv c := by
  have hm0 : 0 < (xiShiftedReciprocalMoment (c ^ 2) 0).re :=
    re_xiShiftedReciprocalMoment_pos (sq_pos_of_pos hc) (by norm_num)
  rw [suzukiXiCoalescingDefect, deriv_xiRealLogDeriv_eq hc,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hc]
  field_simp [hc.ne', hm0.ne']

/-- Every positive movable anchor has a strict defect below the pure endpoint. -/
theorem suzukiXiCoalescingDefect_lt_one {c : ℝ} (hc : 0 < c) :
    suzukiXiCoalescingDefect c < 1 := by
  have hm0 : 0 < (xiShiftedReciprocalMoment (c ^ 2) 0).re :=
    re_xiShiftedReciprocalMoment_pos (sq_pos_of_pos hc) (by norm_num)
  have hm1 : 0 < (xiShiftedReciprocalMoment (c ^ 2) 1).re :=
    re_xiShiftedReciprocalMoment_pos (sq_pos_of_pos hc) (by norm_num)
  rw [suzukiXiCoalescingDefect]
  have hterm : 0 < 2 * c ^ 2 *
      (xiShiftedReciprocalMoment (c ^ 2) 1).re /
        (xiShiftedReciprocalMoment (c ^ 2) 0).re := by positivity
  linarith

/-- Exact central tangent of the movable Xi defect.  This is equation `(13)` at its invariant
scale: `(1-kappa(c))/(2c²) -> tau_src`. -/
theorem tendsto_suzukiXiCoalescingDefect_rate :
    Tendsto
      (fun c : ℝ => (1 - suzukiXiCoalescingDefect c) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 suzukiXiCoalescingSourceRate) := by
  have hc2 : Tendsto (fun c : ℝ => c ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun c : ℝ => c ^ 2) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · exact Eventually.of_forall fun c => sq_nonneg c
  have hm0 : Tendsto
      (fun c : ℝ => (xiShiftedReciprocalMoment (c ^ 2) 0).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (normalizedPrimeArchMoment 0)) := by
    have h := (Complex.continuous_re.tendsto
      (normalizedPrimeArchMoment 0 : ℂ)).comp
        ((tendsto_xiShiftedReciprocalMoment_nhdsGE_zero 0).comp hc2)
    simpa [Function.comp_def] using h
  have hm1 : Tendsto
      (fun c : ℝ => (xiShiftedReciprocalMoment (c ^ 2) 1).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (normalizedPrimeArchMoment 1)) := by
    have h := (Complex.continuous_re.tendsto
      (normalizedPrimeArchMoment 1 : ℂ)).comp
        ((tendsto_xiShiftedReciprocalMoment_nhdsGE_zero 1).comp hc2)
    simpa [Function.comp_def] using h
  have hratio := hm1.div hm0 normalizedPrimeArchMoment_zero_pos.ne'
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcne : c ≠ 0 := hc.ne'
  change (xiShiftedReciprocalMoment (c ^ 2) 1).re /
      (xiShiftedReciprocalMoment (c ^ 2) 0).re =
    (1 - suzukiXiCoalescingDefect c) / (2 * c ^ 2)
  rw [suzukiXiCoalescingDefect]
  field_simp [hcne]
  ring

/-- The movable Xi defect itself converges to the pure even endpoint. -/
theorem tendsto_suzukiXiCoalescingDefect_one :
    Tendsto suzukiXiCoalescingDefect
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsq : Tendsto (fun c : ℝ => 2 * c ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => 2 * c ^ 2) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hgapScaled := tendsto_suzukiXiCoalescingDefect_rate.mul hsq
  have hgapScaled' : Tendsto
      (fun c : ℝ =>
        (1 - suzukiXiCoalescingDefect c) / (2 * c ^ 2) * (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hgapScaled
  have hgap : Tendsto (fun c : ℝ => 1 - suzukiXiCoalescingDefect c)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hgapScaled'.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcne : c ≠ 0 := hc.ne'
    field_simp [hcne]
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have h := hone.sub hgap
  simpa only [sub_zero, sub_sub_cancel] using h

end

end RHTower
