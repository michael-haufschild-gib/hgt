import GaloisForLFunctions.RHTower.WeilLogShiftQuantileMomentEnvelope

/-! Integrability and integral convergence of the actual quantile error envelope. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilQuantileMomentEnvelope_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (p : ℕ) (f g : α → ℝ)
    (hf : Integrable (fun x => f x ^ (2 * p)) μ)
    (hg : Integrable (fun x => g x ^ (2 * p)) μ) :
    Integrable (fun x => finiteWeilQuantileMomentEnvelope p (f x) (g x)) μ := by
  exact (((integrable_const (1 : ℝ)).add
    ((((integrable_const (2 : ℝ)).add hf).add hg).const_mul ((2 : ℝ) ^ p))).const_mul
      ((2 : ℝ) ^ p)).const_mul ((2 : ℝ) ^ p)

theorem finiteWeilQuantileMomentEnvelope_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (p : ℕ) (f g : α → ℝ)
    (hf : Integrable (fun x => f x ^ (2 * p)) μ)
    (hg : Integrable (fun x => g x ^ (2 * p)) μ) :
    (∫ x, finiteWeilQuantileMomentEnvelope p (f x) (g x) ∂μ) =
      (2 : ℝ) ^ p * ((2 : ℝ) ^ p * (1 + (2 : ℝ) ^ p *
        (2 + (∫ x, f x ^ (2 * p) ∂μ) + ∫ x, g x ^ (2 * p) ∂μ))) := by
  have h2 : Integrable (fun x => 2 + f x ^ (2 * p)) μ := (integrable_const (2 : ℝ)).add hf
  have h3 : Integrable (fun x => 2 + f x ^ (2 * p) + g x ^ (2 * p)) μ := h2.add hg
  have hscaled : Integrable (fun x => (2 : ℝ) ^ p * (2 + f x ^ (2 * p) + g x ^ (2 * p))) μ :=
    h3.const_mul ((2 : ℝ) ^ p)
  unfold finiteWeilQuantileMomentEnvelope
  rw [integral_const_mul, integral_const_mul,
    integral_add (integrable_const (1 : ℝ)) hscaled,
    integral_const_mul, integral_add h2 hg,
    integral_add (integrable_const (2 : ℝ)) hf]
  simp

theorem finiteWeilCanonicalJointQuantile_envelope_integrable (r k p : ℕ) :
    Integrable (fun u : ℝ => finiteWeilQuantileMomentEnvelope p
      (quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) u)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  letI := isProbabilityMeasure_restrict_Ioo_zero_one
  exact finiteWeilQuantileMomentEnvelope_integrable p _ _
    (finiteWeilCanonicalProjectedIndex_quantile_pow_integrable r k (2 * p))
    (finiteWeilProjectedGaussian_quantile_pow_integrable 1 0 (2 * p))

theorem finiteWeilGaussianQuantile_envelope_integrable (p : ℕ) :
    Integrable (fun u : ℝ => finiteWeilQuantileMomentEnvelope p
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  letI := isProbabilityMeasure_restrict_Ioo_zero_one
  exact finiteWeilQuantileMomentEnvelope_integrable p _ _
    (finiteWeilProjectedGaussian_quantile_pow_integrable 1 0 (2 * p))
    (finiteWeilProjectedGaussian_quantile_pow_integrable 1 0 (2 * p))

theorem ae_tendsto_finiteWeilCanonicalJointQuantile_envelope (t : ℕ → ℕ) (p : ℕ) :
    ∀ᵐ u : ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)), Tendsto
      (fun r => finiteWeilQuantileMomentEnvelope p
        (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u)
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)) atTop
      (𝓝 (finiteWeilQuantileMomentEnvelope p
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u))) := by
  filter_upwards [ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile t] with u hu
  exact (((((hu.pow (2 * p)).const_add 2).add tendsto_const_nhds).const_mul
    ((2 : ℝ) ^ p)).const_add 1).const_mul ((2 : ℝ) ^ p) |>.const_mul ((2 : ℝ) ^ p)

theorem tendsto_finiteWeilCanonicalJointQuantile_envelope_integral (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => ∫ u : ℝ, finiteWeilQuantileMomentEnvelope p
      (quantile (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u)
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) atTop
      (𝓝 (∫ u : ℝ, finiteWeilQuantileMomentEnvelope p
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
        (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)
          ∂(volume.restrict (Ioo (0 : ℝ) 1)))) := by
  letI := isProbabilityMeasure_restrict_Ioo_zero_one
  have hg := finiteWeilProjectedGaussian_quantile_pow_integrable 1 0 (2 * p)
  have hlim := (((((tendsto_finiteWeilCanonicalProjectedIndex_quantile_moment t (2 * p)).const_add 2).add
    (tendsto_const_nhds (x := ∫ u : ℝ,
      (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u) ^ (2 * p)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))))).const_mul ((2 : ℝ) ^ p)).const_add 1).const_mul
    ((2 : ℝ) ^ p) |>.const_mul ((2 : ℝ) ^ p)
  rw [finiteWeilQuantileMomentEnvelope_integral p _ _ hg hg]
  exact hlim.congr fun r => (finiteWeilQuantileMomentEnvelope_integral p _ _
    (finiteWeilCanonicalProjectedIndex_quantile_pow_integrable r (2 * (r + 1) ^ 2 + t r) (2 * p)) hg).symm

end RHTower
