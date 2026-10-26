import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalProducerConvergence

/-!
# Quantitative physical regularity of compact logarithmic producers

Square-root energy bounds control the actual box derivative and affine
commutator. Physical primitive convergence includes the endpoint zero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

/-- The compensated velocity satisfies the exact square-root energy ceiling. -/
theorem norm_compensatedVelocity_le_sqrt (n : ℕ) (q : Velocity) :
    ‖compensatedVelocity n q‖ ≤ Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖ := by
  have hsq := norm_sq_compensatedVelocity_le n q
  have he : (Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖) ^ 2 =
      (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hn : 0 ≤ Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖ := by positivity
  nlinarith only [hsq, he, hn, norm_nonneg (compensatedVelocity n q)]

/-- The square-root coefficient is at most one plus the compensation-decay coefficient. -/
theorem producer_sqrt_energy_coefficient_le (n : ℕ) :
    Real.sqrt (1 + Real.exp (-producerScale n)) ≤ 1 + Real.exp (-producerScale n / 2) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + Real.exp (-producerScale n))
  have he : Real.exp (-producerScale n / 2) ^ 2 = Real.exp (-producerScale n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  nlinarith only [hs, he, Real.sqrt_nonneg (1 + Real.exp (-producerScale n)),
    Real.exp_pos (-producerScale n / 2)]

theorem norm_compensatedVelocity_le_one_add_decay (n : ℕ) (q : Velocity) :
    ‖compensatedVelocity n q‖ ≤ (1 + Real.exp (-producerScale n / 2)) * ‖q‖ :=
  (norm_compensatedVelocity_le_sqrt n q).trans
    (mul_le_mul_of_nonneg_right (producer_sqrt_energy_coefficient_le n) (norm_nonneg q))

/-- The smoothed profile is an actual continuous representative of the producer. -/
theorem smoothedCompensatedProfile_regular (n : ℕ) (q : Velocity) :
    Continuous (smoothedCompensatedProfile n q) ∧
      smoothedCompensatedVelocity n q =ᵐ[volume] smoothedCompensatedProfile n q ∧
      MemLp (smoothedCompensatedProfile n q) 2 volume ∧
      MemLp (deriv (smoothedCompensatedProfile n q)) 2 volume :=
  ⟨continuous_physicalBoxProfile _ _, ae_physicalBoxAverage _ _,
    memLp_physicalBoxProfile _ _, memLp_deriv_physicalBoxProfile _ _⟩

/-- Every finite physical interval has absolute continuity of the actual profile. -/
theorem absolutelyContinuous_smoothedCompensatedProfile (n : ℕ) (q : Velocity) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (smoothedCompensatedProfile n q) a b :=
  absolutelyContinuous_physicalBoxProfile _ _ a b

/-- The a.e. profile derivative is the explicitly constructed L² difference quotient. -/
theorem ae_deriv_smoothedCompensatedProfile (n : ℕ) (q : Velocity) :
    deriv (smoothedCompensatedProfile n q) =ᵐ[volume]
      ((producerStep n)⁻¹ • (physicalTranslation (producerStep n) (compensatedVelocity n q) -
        compensatedVelocity n q) : Velocity) := by
  exact ae_deriv_physicalBoxProfile (-2 * producerScale n) (compensatedVelocity n q)

/-- The derivative's physical L² norm has the specified exact coefficient. -/
theorem norm_smoothedCompensatedProfile_derivative_le (n : ℕ) (q : Velocity) :
    ‖(producerStep n)⁻¹ • (physicalTranslation (producerStep n) (compensatedVelocity n q) -
        compensatedVelocity n q)‖ ≤
      2 * (producerStep n)⁻¹ * Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖ := by
  have hb := physicalBoxDerivative_norm_le (-2 * producerScale n) (compensatedVelocity n q)
  change ‖(producerStep n)⁻¹ •
    (physicalTranslation (producerStep n) (compensatedVelocity n q) - compensatedVelocity n q)‖ ≤
      (2 / producerStep n) * ‖compensatedVelocity n q‖ at hb
  calc
    _ ≤ (2 / producerStep n) * ‖compensatedVelocity n q‖ := hb
    _ ≤ (2 / producerStep n) * (Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖) :=
      mul_le_mul_of_nonneg_left (norm_compensatedVelocity_le_sqrt n q)
        (div_nonneg (by norm_num) (producerStep_pos n).le)
    _ = _ := by ring

/-- The affine commutator obeys the square root of its exact energy bound, for all real parameters. -/
theorem smoothedCompensatedVelocity_affine_norm_le (a b : ℝ) (n : ℕ) (q : Velocity) :
    ‖physicalAffineCommutator a b (smoothedCompensatedVelocity n q)‖ ≤
      2 * Real.sqrt |a| * min 1 (|b * (a - 1)| / producerStep n) *
        Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖ := by
  have hmin : 0 ≤ min 1 (|b * (a - 1)| / producerStep n) :=
    le_min (by norm_num) (div_nonneg (abs_nonneg _) (producerStep_pos n).le)
  have hb := smoothedCompensatedVelocity_affine_energy_le a b n q
  have he : (2 * Real.sqrt |a| * min 1 (|b * (a - 1)| / producerStep n) *
        Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖) ^ 2 =
      4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
        (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt (abs_nonneg a), Real.sq_sqrt (by positivity :
      0 ≤ 1 + Real.exp (-producerScale n))]
    norm_num
  have hn : 0 ≤ 2 * Real.sqrt |a| * min 1 (|b * (a - 1)| / producerStep n) *
      Real.sqrt (1 + Real.exp (-producerScale n)) * ‖q‖ := by positivity
  nlinarith only [hb, he, hn, norm_nonneg
    (physicalAffineCommutator a b (smoothedCompensatedVelocity n q))]

/-- Physical trace error is controlled through its endpoint, including endpoint zero. -/
theorem primitive_sub_sq_le_physical_norm (u q : Velocity) {t : ℝ} (ht : 0 ≤ t) :
    (primitive u t - primitive q t) ^ 2 ≤ t * ‖u - positivePhysicalVelocity q‖ ^ 2 := by
  have hz : primitive (u - positivePhysicalVelocity q) 0 = 0 := by
    simp only [primitive, intervalIntegral.integral_same]
  have hb := increment_sq_le_energy (u - positivePhysicalVelocity q) 0 ⟨t, ht⟩
  simp only [zero_add, hz, sub_zero, primitive_sub_velocity] at hb
  change (primitive u t - primitive (positivePhysicalVelocity q) t) ^ 2 ≤
    t * energy (u - positivePhysicalVelocity q) 0 t at hb
  rw [primitive_positivePhysicalVelocity q t ht] at hb
  have he : energy (u - positivePhysicalVelocity q) 0 t ≤
      ‖u - positivePhysicalVelocity q‖ ^ 2 := by
    rw [energy, intervalIntegral.integral_of_le ht, norm_sq_velocity]
    exact setIntegral_le_integral (integrable_velocity_sq _)
      (Eventually.of_forall fun s => sq_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left he ht)

/-- Uniform primitive convergence on every bounded positive physical interval. -/
theorem primitive_smoothedCompensatedVelocity_tendstoUniformlyOn (q : Velocity) {T : ℝ}
    (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun n => primitive (smoothedCompensatedVelocity n q))
      (primitive q) atTop (Icc 0 T) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp (smoothedCompensatedVelocity_tendsto q)
  have hb : Tendsto (fun n => Real.sqrt T *
      ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul (Real.sqrt T)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn t ht
  rw [Real.dist_eq, abs_sub_comm]
  apply lt_of_le_of_lt _ hn
  have hs := primitive_sub_sq_le_physical_norm (smoothedCompensatedVelocity n q) q ht.1
  have hst := mul_le_mul_of_nonneg_right ht.2
    (sq_nonneg ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖)
  have he : (Real.sqrt T * ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖) ^ 2 =
      T * ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hT]
  have hp : 0 ≤ Real.sqrt T * ‖smoothedCompensatedVelocity n q - positivePhysicalVelocity q‖ :=
    mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg _)
  nlinarith only [hs, hst, he, hp,
    sq_abs (primitive (smoothedCompensatedVelocity n q) t - primitive q t),
    abs_nonneg (primitive (smoothedCompensatedVelocity n q) t - primitive q t)]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
