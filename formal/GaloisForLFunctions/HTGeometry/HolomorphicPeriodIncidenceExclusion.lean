import GaloisForLFunctions.HTGeometry.PeriodIncidenceFlatIntersection
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Holomorphic exclusion from the period-incidence completion defect

The ambient period-incidence multiplier on `ℓ∞` has nonclosed range and a nonzero
all-power flat intersection.  This module proves that bounded holomorphic disk data sees neither
phenomenon.  Evaluation on the regularized nonzero periods meets the closure of the first range
exactly when it already lies in that range, and its intersection with all powered ranges is zero.

This is the source-level no-go required by programme 4: the ambient strictness and flat-radical
defects cannot themselves be the multiple-gamma base-change defect.  Any nonzero comparison class
must measure escape from the bounded holomorphic functional calculus.
-/

open Filter
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- Evaluation of a bounded holomorphic disk function on the regularized nonzero periods. -/
def periodHolomorphicEvaluation
    (L : Submodule ℤ ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R)) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ f (regularizedPeriodWeight q.1.1),
    memℓp_infty ⟨R, by
      rintro _ ⟨q, rfl⟩
      have hw : regularizedPeriodWeight q.1.1 ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball] using norm_regularizedPeriodWeight_lt_one q.1.1
      have hfw := hmap hw
      simpa [Metric.mem_closedBall] using hfw⟩⟩

@[simp] theorem periodHolomorphicEvaluation_apply
    (L : Submodule ℤ ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (q : NonzeroPeriod L) :
    periodHolomorphicEvaluation L f R hmap q =
      f (regularizedPeriodWeight q.1.1) := rfl

/-- Schwarz division gives a bounded exact preimage when the source vanishes at the origin. -/
def periodHolomorphicDivPreimage
    (L : Submodule ℤ ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (hf0 : f 0 = 0) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ dslope f 0 (regularizedPeriodWeight q.1.1),
    memℓp_infty ⟨R, by
      rintro _ ⟨q, rfl⟩
      have hw : regularizedPeriodWeight q.1.1 ∈ Metric.ball (0 : ℂ) 1 := by
        simpa [Metric.mem_ball] using norm_regularizedPeriodWeight_lt_one q.1.1
      have hbound := Complex.norm_dslope_le_div_of_mapsTo_ball hd
        (by simpa [hf0] using hmap) hw
      simpa using hbound⟩⟩

@[simp] theorem periodHolomorphicDivPreimage_apply
    (L : Submodule ℤ ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (hf0 : f 0 = 0) (q : NonzeroPeriod L) :
    periodHolomorphicDivPreimage L f R hd hmap hf0 q =
      dslope f 0 (regularizedPeriodWeight q.1.1) := rfl

theorem periodHolomorphicEvaluation_mem_range_of_eq_zero
    (L : Submodule ℤ ℂ) (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (hf0 : f 0 = 0) :
    periodHolomorphicEvaluation L f R hmap ∈
      Set.range (periodIncidenceMultiplier L) := by
  refine ⟨periodHolomorphicDivPreimage L f R hd hmap hf0, ?_⟩
  apply lp.ext
  funext q
  have hw0 : regularizedPeriodWeight q.1.1 ≠ 0 :=
    regularizedPeriodWeight_ne_zero q.2
  rw [periodIncidenceMultiplier_apply, periodHolomorphicDivPreimage_apply,
    periodHolomorphicEvaluation_apply, dslope_of_ne _ hw0, slope_def_module]
  simp [hf0, hw0]

/-- Every multiplier output converges to zero along the small-period sequence. -/
private theorem tendsto_periodIncidenceMultiplier_smallPeriods_zero
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) :
    ∃ q : ℕ → NonzeroPeriod L,
      Tendsto (fun n ↦ regularizedPeriodWeight (q n).1.1) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ periodIncidenceMultiplier L x (q n)) atTop (𝓝 0) := by
  obtain ⟨p, hpL, hpne, hp0⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
  have hweight : Tendsto (fun n ↦ regularizedPeriodWeight (q n).1.1)
      atTop (𝓝 0) := by
    simpa [q] using tendsto_regularizedPeriodWeight_zero hp0
  have hweightNorm : Tendsto (fun n ↦ ‖regularizedPeriodWeight (q n).1.1‖)
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp hweight
  have hproduct : Tendsto
      (fun n ↦ regularizedPeriodWeight (q n).1.1 * x (q n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
      (g := fun n ↦ ‖regularizedPeriodWeight (q n).1.1‖ * ‖x‖)
    · exact Eventually.of_forall fun _ ↦ norm_nonneg _
    · exact Eventually.of_forall fun n ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x (q n)) (norm_nonneg _)
    · simpa using hweightNorm.mul_const ‖x‖
  refine ⟨q, hweight, ?_⟩
  simpa [periodIncidenceMultiplier_apply] using hproduct

/-- The distance from a holomorphic evaluation to an exact incidence output is at least its
constant term. -/
theorem norm_periodHolomorphicEvaluation_sub_multiplier_ge_norm_zero
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) :
    ‖f 0‖ ≤ ‖periodHolomorphicEvaluation L f R hmap - periodIncidenceMultiplier L x‖ := by
  obtain ⟨q, hweight, hmult⟩ :=
    tendsto_periodIncidenceMultiplier_smallPeriods_zero L hL x
  have hfcont : ContinuousAt f 0 :=
    (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
  have hfeval : Tendsto
      (fun n ↦ periodHolomorphicEvaluation L f R hmap (q n)) atTop (𝓝 (f 0)) := by
    simpa using! hfcont.tendsto.comp hweight
  have hnorm : Tendsto
      (fun n ↦ ‖periodHolomorphicEvaluation L f R hmap (q n) -
        periodIncidenceMultiplier L x (q n)‖) atTop (𝓝 ‖f 0‖) := by
    simpa using (hfeval.sub hmult).norm
  apply le_of_tendsto hnorm
  exact Eventually.of_forall fun n ↦
    lp.norm_apply_le_norm ENNReal.top_ne_zero
      (periodHolomorphicEvaluation L f R hmap - periodIncidenceMultiplier L x) (q n)

theorem periodHolomorphicEvaluation_mem_closure_range_iff
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R)) :
    periodHolomorphicEvaluation L f R hmap ∈
        closure (Set.range (periodIncidenceMultiplier L)) ↔
      f 0 = 0 := by
  constructor
  · intro hclosure
    by_contra hf0
    have hnorm0 : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ :=
      Metric.mem_closure_iff.1 hclosure (‖f 0‖ / 2) (half_pos hnorm0)
    rw [dist_eq_norm] at hy
    have hge := norm_periodHolomorphicEvaluation_sub_multiplier_ge_norm_zero
      L hL f R hd hmap x
    linarith
  · intro hf0
    exact subset_closure (periodHolomorphicEvaluation_mem_range_of_eq_zero L f R hd hmap hf0)

theorem periodHolomorphicEvaluation_mem_range_iff
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R)) :
    periodHolomorphicEvaluation L f R hmap ∈
        Set.range (periodIncidenceMultiplier L) ↔
      f 0 = 0 := by
  constructor
  · intro hrange
    exact (periodHolomorphicEvaluation_mem_closure_range_iff L hL f R hd hmap).1
      (subset_closure hrange)
  · exact periodHolomorphicEvaluation_mem_range_of_eq_zero L f R hd hmap

/-- Membership in the order-`r` powered range forces analytic vanishing order at least `r`. -/
theorem natCast_le_analyticOrderAt_of_periodHolomorphicEvaluation_mem_poweredRange
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (r : ℕ)
    (hrange : periodHolomorphicEvaluation L f R hmap ∈
      Set.range (poweredPeriodIncidenceMultiplier L r)) :
    r ≤ analyticOrderAt f 0 := by
  have hf0 : AnalyticAt ℂ f 0 := hf 0 (by simp)
  by_contra horder
  cases ho : analyticOrderAt f 0 with
  | top => exact horder (by simp [ho])
  | coe m =>
      have hmr : m < r := by
        simpa [ho, ENat.coe_le_coe, not_le] using horder
      obtain ⟨g, hg, hg0, hfg⟩ := (hf0.analyticOrderAt_eq_natCast).1 ho
      obtain ⟨a, ha⟩ := hrange
      obtain ⟨p, hpL, hpne, hp0⟩ :=
        exists_small_nonzero_of_not_discrete_intSubmodule L hL
      let q : ℕ → NonzeroPeriod L := fun n ↦ ⟨⟨p n, hpL n⟩, hpne n⟩
      let w : ℕ → ℂ := fun n ↦ regularizedPeriodWeight (q n).1.1
      have hw0 : Tendsto w atTop (𝓝 0) := by
        simpa [w, q] using tendsto_regularizedPeriodWeight_zero hp0
      have hwne : ∀ n, w n ≠ 0 := fun n ↦ by
        exact regularizedPeriodWeight_ne_zero (q n).2
      have hfactor : ∀ᶠ n in atTop, f (w n) = w n ^ m * g (w n) := by
        have := hw0.eventually hfg
        simpa [w] using this
      have hrangeCoord : ∀ n, w n ^ r * a (q n) = f (w n) := by
        intro n
        have hcoord := congrArg
          (fun x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ↦ x (q n)) ha
        simpa [w, periodHolomorphicEvaluation_apply,
          poweredPeriodIncidenceMultiplier_apply] using hcoord
      have hgeq : ∀ᶠ n in atTop, g (w n) = w n ^ (r - m) * a (q n) := by
        filter_upwards [hfactor] with n hn
        apply mul_left_cancel₀ (pow_ne_zero m (hwne n))
        calc
          w n ^ m * g (w n) = f (w n) := hn.symm
          _ = w n ^ r * a (q n) := (hrangeCoord n).symm
          _ = w n ^ m * (w n ^ (r - m) * a (q n)) := by
            rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hmr.le]
      have hpow0 : Tendsto (fun n ↦ w n ^ (r - m)) atTop (𝓝 0) := by
        have hp := (continuous_pow (r - m)).continuousAt.tendsto.comp hw0
        simpa [Nat.sub_ne_zero_of_lt hmr] using! hp
      have hpowNorm : Tendsto (fun n ↦ ‖w n ^ (r - m)‖) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp hpow0
      have hright0 : Tendsto (fun n ↦ w n ^ (r - m) * a (q n)) atTop (𝓝 0) := by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        apply squeeze_zero'
          (g := fun n ↦ ‖w n ^ (r - m)‖ * ‖a‖)
        · exact Eventually.of_forall fun _ ↦ norm_nonneg _
        · exact Eventually.of_forall fun n ↦ by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left
              (lp.norm_apply_le_norm ENNReal.top_ne_zero a (q n)) (norm_nonneg _)
        · simpa using hpowNorm.mul_const ‖a‖
      have hgzero : Tendsto (fun n ↦ g (w n)) atTop (𝓝 0) :=
        hright0.congr' (hgeq.mono fun _ hn ↦ hn.symm)
      have hglimit : Tendsto (fun n ↦ g (w n)) atTop (𝓝 (g 0)) :=
        hg.continuousAt.tendsto.comp hw0
      exact hg0 (tendsto_nhds_unique hglimit hgzero)

/-- A bounded holomorphic evaluation lying in every powered incidence range is identically zero.
This excludes the nonzero ambient flat radical from the holomorphic source. -/
theorem periodHolomorphicEvaluation_eq_zero_of_mem_poweredRanges
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R))
    (hflat : ∀ r : ℕ, periodHolomorphicEvaluation L f R hmap ∈
      Set.range (poweredPeriodIncidenceMultiplier L r)) :
    periodHolomorphicEvaluation L f R hmap = 0 := by
  have hf0 : AnalyticAt ℂ f 0 := hf 0 (by simp)
  have horder : analyticOrderAt f 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro r
    exact natCast_le_analyticOrderAt_of_periodHolomorphicEvaluation_mem_poweredRange
      L hL f R hf hmap r (hflat r)
  have hlocal : f =ᶠ[𝓝 0] 0 := analyticOrderAt_eq_top.mp horder
  have hzeroOn : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero Metric.isPreconnected_ball
      (by simp) hlocal
  apply lp.ext
  funext q
  rw [periodHolomorphicEvaluation_apply]
  exact hzeroOn (by
    simpa [Metric.mem_ball] using norm_regularizedPeriodWeight_lt_one q.1.1)

/-- Exact source-level capstone: completion creates no first-order holomorphic class, while the
all-power flat intersection contains no nonzero bounded holomorphic evaluation. -/
theorem holomorphic_period_incidence_exclusion
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (f : ℂ → ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hmap : Set.MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 R)) :
    (periodHolomorphicEvaluation L f R hmap ∈
          closure (Set.range (periodIncidenceMultiplier L)) ↔
        periodHolomorphicEvaluation L f R hmap ∈
          Set.range (periodIncidenceMultiplier L)) ∧
      ((∀ r : ℕ, periodHolomorphicEvaluation L f R hmap ∈
          Set.range (poweredPeriodIncidenceMultiplier L r)) →
        periodHolomorphicEvaluation L f R hmap = 0) := by
  refine ⟨?_, periodHolomorphicEvaluation_eq_zero_of_mem_poweredRanges L hL f R hf hmap⟩
  rw [periodHolomorphicEvaluation_mem_closure_range_iff L hL f R hf.differentiableOn hmap,
    periodHolomorphicEvaluation_mem_range_iff L hL f R hf.differentiableOn hmap]

end

end GaloisForLFunctions
