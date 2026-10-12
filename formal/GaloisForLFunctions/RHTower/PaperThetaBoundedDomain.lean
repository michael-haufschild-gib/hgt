import GaloisForLFunctions.RHTower.PaperThetaDivisorReflection
import GaloisForLFunctions.RHTower.PaperThetaStrictLogEndpoint

/-! # The complete strong-Lᵖ domain of the literal theta family

Divisor modes have actual bounded representatives. Every exponent greater than
one, including infinity, consequently selects precisely the same parameters.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

private theorem bound_of_two_limits {f : ℝ → ℂ} {l r : ℂ} (hf : Continuous f)
    (hl : Tendsto f atBot (𝓝 l)) (hr : Tendsto f atTop (𝓝 r)) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hl.norm.eventually (gt_mem_nhds (lt_add_one ‖l‖)))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hr.norm.eventually (gt_mem_nhds (lt_add_one ‖r‖)))
  have hK : IsCompact (f '' Icc a b) := isCompact_Icc.image hf
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  refine ⟨max (‖l‖ + 1) (max (‖r‖ + 1) M), fun x => ?_⟩
  by_cases hxa : x ≤ a
  · exact (ha x hxa).le.trans (le_max_left _ _)
  by_cases hbx : b ≤ x
  · exact (hb x hbx).le.trans ((le_max_left _ _).trans (le_max_right _ _))
  exact (hM (f x) ⟨x, ⟨by linarith, by linarith⟩, rfl⟩).trans
    ((le_max_right _ _).trans (le_max_right _ _))

private theorem left_trace_of_exception {z : ℂ} (hz : z = 0 ∨ XiC z = 0) :
    Tendsto (flatQuotient z) atBot (𝓝 (-1)) := by
  rcases hz with rfl | hXi
  · exact (tendsto_const_nhds (x := (-1 : ℂ))).congr fun x => (flatQuotient_zero x).symm
  · exact tendsto_divisor_flatQuotient_atBot ⟨z, hXi⟩

private theorem bound_of_exception {z : ℂ} (hz : z = 0 ∨ XiC z = 0) :
    ∃ C : ℝ, ∀ x, ‖flatQuotient z x‖ ≤ C :=
  bound_of_two_limits (continuous_flatQuotient z) (left_trace_of_exception hz)
    (tendsto_flatQuotient_atTop z)

private theorem memLp_top_of_quotient_bound {z : ℂ} {C : ℝ}
    (hC : ∀ x, ‖flatQuotient z x‖ ≤ C) :
    MemLp (flatModePullback z) ∞ unitIntervalMeasure := by
  apply memLp_top_of_bound (measurable_pullback_all z).aestronglyMeasurable C
  exact Eventually.of_forall fun t => by
    rw [flatModePullback_eq_flatQuotient]
    exact hC _

/-- Actual boundedness of the source-relative mode is exactly divisor-or-zero admission. -/
theorem bounded_flatQuotient_iff (z : ℂ) :
    (∃ C : ℝ, ∀ x, ‖flatQuotient z x‖ ≤ C) ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    exact (memLp_pullback_iff_all z).mp ((memLp_top_of_quotient_bound hC).mono_exponent le_top)
  · exact bound_of_exception

/-- Essential boundedness requires no extra source or endpoint premise. -/
theorem memLp_top_pullback_iff (z : ℂ) :
    MemLp (flatModePullback z) ∞ unitIntervalMeasure ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    exact (memLp_pullback_iff_all z).mp (h.mono_exponent le_top)
  · intro hz
    obtain ⟨C, hC⟩ := bound_of_exception hz
    exact memLp_top_of_quotient_bound hC

theorem memLp_top_circleMode_iff (z : ℂ) :
    MemLp (circleMode z) ∞ circleMeasure ↔ z = 0 ∨ XiC z = 0 := by
  rw [← measurePreserving_circle.map_eq,
    memLp_map_measure_iff (measurable_circleMode_all z).aestronglyMeasurable
      Period.measurable_circle.aemeasurable]
  change MemLp (fun t => circleMode z (Period.circle t)) ∞ unitIntervalMeasure ↔ _
  exact (memLp_congr_ae (circleMode_circle_ae z)).trans (memLp_top_pullback_iff z)

/-- Every strong exponent has the same exact original quantile domain. -/
theorem memLp_strong_pullback_iff (z : ℂ) (p : StrongLpExponent) :
    MemLp (flatModePullback z) p.val unitIntervalMeasure ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro hp
    apply (memLp_pullback_iff_all z).mp
    apply (memLp_iff_all_logPowers z).mpr
    intro a
    have h := integrable_logPower_strongLp unitIntervalMeasure p (hp.toLp (flatModePullback z)) a
    refine h.congr ?_
    filter_upwards [hp.coeFn_toLp] with t ht
    simp only [pullbackLogPower, ht]
  · intro hz
    exact ((memLp_top_pullback_iff z).mpr hz).mono_exponent le_top

theorem memLp_strong_circleMode_iff (z : ℂ) (p : StrongLpExponent) :
    MemLp (circleMode z) p.val circleMeasure ↔ z = 0 ∨ XiC z = 0 := by
  rw [← measurePreserving_circle.map_eq,
    memLp_map_measure_iff (measurable_circleMode_all z).aestronglyMeasurable
      Period.measurable_circle.aemeasurable]
  change MemLp (fun t => circleMode z (Period.circle t)) p.val unitIntervalMeasure ↔ _
  exact (memLp_congr_ae (circleMode_circle_ae z)).trans (memLp_strong_pullback_iff z p)

/-- A finite left source trace exists precisely on the bounded domain, and must equal -1. -/
theorem finite_left_trace_iff (z c : ℂ) :
    Tendsto (flatQuotient z) atBot (𝓝 c) ↔ (z = 0 ∨ XiC z = 0) ∧ c = -1 := by
  constructor
  · intro h
    have hz := (bounded_flatQuotient_iff z).mp
      (bound_of_two_limits (continuous_flatQuotient z) h (tendsto_flatQuotient_atTop z))
    exact ⟨hz, tendsto_nhds_unique h (left_trace_of_exception hz)⟩
  · rintro ⟨hz, rfl⟩
    exact left_trace_of_exception hz

/-- The actual circle representative is uniformly bounded at every divisor-or-zero point. -/
theorem exists_bound_circleMode (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    ∃ C : ℝ, ∀ x, ‖circleMode z.val x‖ ≤ C := by
  obtain ⟨C, hC⟩ := bound_of_exception z.property
  refine ⟨C, fun x => ?_⟩
  rw [circleMode, flatModePullback_eq_flatQuotient]
  exact hC _

end RHTower.PaperThetaEndpoint
