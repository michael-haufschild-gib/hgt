import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalProducerConvergence

/-!
# Exact physical truncation tails

The squared approximation error splits into disjoint lower and upper tails.
Each tail vanishes separately, and their square roots give the explicit
separate-tail bound for the compact producer.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

/-- Positive interval truncation loses exactly its two disjoint physical tails. -/
theorem norm_sq_intervalRestriction_sub_positive (q : Velocity) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖physicalIntervalRestriction a b q - positivePhysicalVelocity q‖ ^ 2 =
      (∫ t in Ioc 0 a, (q t) ^ 2) + ∫ t in Ioi b, (q t) ^ 2 := by
  rw [norm_sq_velocity, ← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioi, ← integral_add
      ((integrable_velocity_sq q).indicator measurableSet_Ioc)
      ((integrable_velocity_sq q).indicator measurableSet_Ioi)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (physicalIntervalRestriction a b q) (positivePhysicalVelocity q),
    ae_physicalIntervalRestriction a b q, ae_positivePhysicalVelocity q] with t hs hr hp
  change ((physicalIntervalRestriction a b q - positivePhysicalVelocity q : Velocity) t) ^ 2 =
    (Ioc (0 : ℝ) a).indicator (fun s => (q s) ^ 2) t +
      (Ioi b).indicator (fun s => (q s) ^ 2) t
  simp only [Pi.sub_apply] at hs
  rw [hs, hr, hp]
  by_cases ht : 0 < t
  · have hp : t ∈ Ioi (0 : ℝ) := ht
    by_cases hta : t ≤ a
    · have hm : t ∉ Ioc a b := fun h => (not_lt_of_ge hta) h.1
      have hl : t ∈ Ioc (0 : ℝ) a := ⟨ht, hta⟩
      have hu : t ∉ Ioi b := not_lt.mpr (hta.trans hab)
      rw [indicator_of_notMem hm, indicator_of_mem hp, indicator_of_mem hl,
        indicator_of_notMem hu, zero_sub, neg_sq, add_zero]
    · have hat : a < t := lt_of_not_ge hta
      have hl : t ∉ Ioc (0 : ℝ) a := fun h => hta h.2
      by_cases htb : t ≤ b
      · have hm : t ∈ Ioc a b := ⟨hat, htb⟩
        have hu : t ∉ Ioi b := not_lt.mpr htb
        rw [indicator_of_mem hm, indicator_of_mem hp, indicator_of_notMem hl,
          indicator_of_notMem hu, sub_self]
        norm_num
      · have hm : t ∉ Ioc a b := fun h => htb h.2
        have hu : t ∈ Ioi b := lt_of_not_ge htb
        rw [indicator_of_notMem hm, indicator_of_mem hp, indicator_of_notMem hl,
          indicator_of_mem hu, zero_sub, neg_sq, zero_add]
  · have hm : t ∉ Ioc a b := fun h => ht (lt_of_le_of_lt ha h.1)
    have hp : t ∉ Ioi (0 : ℝ) := ht
    have hl : t ∉ Ioc (0 : ℝ) a := fun h => ht h.1
    have hu : t ∉ Ioi b := not_lt.mpr (((le_of_not_gt ht).trans ha).trans hab)
    rw [indicator_of_notMem hm, indicator_of_notMem hp, indicator_of_notMem hl,
      indicator_of_notMem hu]
    norm_num

/-- Exact two-tail identity for the specified exponential truncation. -/
theorem norm_sq_truncatedVelocity_sub_positive_eq_tails (n : ℕ) (q : Velocity) :
    ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2 =
      (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2) +
        ∫ t in Ioi (producerBeta n), (q t) ^ 2 :=
  norm_sq_intervalRestriction_sub_positive q (producerAlpha_pos n).le
    (producerAlpha_le_producerBeta n)

/-- Both squared physical tails tend separately to zero. -/
theorem producer_physical_tail_integrals_tendsto (q : Velocity) :
    Tendsto (fun n => ∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ t in Ioi (producerBeta n), (q t) ^ 2) atTop (𝓝 0) := by
  have he : Tendsto (fun n => ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [sq, zero_mul] using
      (tendsto_iff_norm_sub_tendsto_zero.mp (truncatedVelocity_tendsto q)).pow 2
  have hlow (n : ℕ) : 0 ≤ ∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2 :=
    integral_nonneg fun t => sq_nonneg (q t)
  have hupp (n : ℕ) : 0 ≤ ∫ t in Ioi (producerBeta n), (q t) ^ 2 :=
    integral_nonneg fun t => sq_nonneg (q t)
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he hlow
    intro n
    change (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2) ≤
      ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2
    rw [norm_sq_truncatedVelocity_sub_positive_eq_tails]
    exact le_add_of_nonneg_right (hupp n)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he hupp
    intro n
    change (∫ t in Ioi (producerBeta n), (q t) ^ 2) ≤
      ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ^ 2
    rw [norm_sq_truncatedVelocity_sub_positive_eq_tails]
    exact le_add_of_nonneg_left (hlow n)

/-- Both physical tail norms vanish separately. -/
theorem producer_physical_tail_norms_tendsto (q : Velocity) :
    Tendsto (fun n => Real.sqrt (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.sqrt (∫ t in Ioi (producerBeta n), (q t) ^ 2)) atTop (𝓝 0) := by
  constructor
  · simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (producer_physical_tail_integrals_tendsto q).1
  · simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (producer_physical_tail_integrals_tendsto q).2

/-- The truncation error is bounded by the sum of the two physical tail norms. -/
theorem norm_truncatedVelocity_sub_positive_le_tail_norms (n : ℕ) (q : Velocity) :
    ‖truncatedVelocity n q - positivePhysicalVelocity q‖ ≤
      Real.sqrt (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2) +
        Real.sqrt (∫ t in Ioi (producerBeta n), (q t) ^ 2) := by
  have he := norm_sq_truncatedVelocity_sub_positive_eq_tails n q
  have hl := Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg (q t)) :
    0 ≤ ∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2)
  have hu := Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg (q t)) :
    0 ≤ ∫ t in Ioi (producerBeta n), (q t) ^ 2)
  have hln := Real.sqrt_nonneg (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2)
  have hun := Real.sqrt_nonneg (∫ t in Ioi (producerBeta n), (q t) ^ 2)
  nlinarith only [he, hl, hu, hln, hun, norm_nonneg
    (truncatedVelocity n q - positivePhysicalVelocity q), mul_nonneg hln hun]

/-- The complete producer error is controlled by two tails, compensation, and box approximation. -/
theorem norm_smoothedCompensatedVelocity_sub_positive_le_tail_norms (n : ℕ) (q : Velocity) :
    ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ≤
      Real.sqrt (∫ t in Ioc 0 (producerAlpha n), (q t) ^ 2) +
        Real.sqrt (∫ t in Ioi (producerBeta n), (q t) ^ 2) +
        Real.exp (-producerScale n / 2) * ‖q‖ +
        ‖physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
          positivePhysicalVelocity q‖ :=
  (norm_smoothedCompensatedVelocity_sub_positive_le n q).trans
    (add_le_add (add_le_add (norm_truncatedVelocity_sub_positive_le_tail_norms n q) le_rfl) le_rfl)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
