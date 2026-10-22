import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewAdjointWitness
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewNormalizationCore

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct Convolution
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

set_option maxHeartbeats 100000 in
theorem integrable_suzukiRawSourceKernel_pair
    (a : SuzukiPositiveAperture) (f q : SuzukiApertureZeroMean a) :
    Integrable (fun p : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 =>
      (GaloisForLFunctions.RHTower.suzukiSourceScrew
          ((p.1 : ℝ) - (p.2 : ℝ)) : ℂ) *
        (f : SuzukiApertureIntervalL2 a.1) p.2 *
          (starRingEnd ℂ) ((q : SuzukiApertureIntervalL2 a.1) p.1))
      ((volume : Measure (SuzukiApertureInterval a.1)).prod volume) := by
  refine (integrable_suzukiRawScrewKernel_pair a.1
    (f : SuzukiApertureIntervalL2 a.1)
    (q : SuzukiApertureIntervalL2 a.1)).congr
      (Filter.Eventually.of_forall fun p => ?_)
  change suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ)) *
      (f : SuzukiApertureIntervalL2 a.1) p.2 *
        (starRingEnd ℂ) ((q : SuzukiApertureIntervalL2 a.1) p.1) = _
  rw [suzukiScrewG_eq_sourceScrew_core]

set_option maxHeartbeats 100000 in
theorem integrable_suzukiSourceEndpoint_mul
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    Integrable (fun u : SuzukiApertureInterval a.1 =>
      (GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - (u : ℝ)) : ℂ) *
        (f : SuzukiApertureIntervalL2 a.1) u) volume := by
  let right : SuzukiApertureInterval a.1 :=
    ⟨a.1, by constructor <;> linarith [a.2]⟩
  obtain ⟨C, hC⟩ := exists_suzukiRawScrewKernel_norm_bound a.1
  have hmult : AEStronglyMeasurable
      (fun u : SuzukiApertureInterval a.1 =>
        (GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - (u : ℝ)) : ℂ))
      volume := by
    have hG : AEStronglyMeasurable
        (fun u : SuzukiApertureInterval a.1 =>
          suzukiScrewG (a.1 - (u : ℝ))) volume :=
      (continuous_suzukiScrewG.comp
        (continuous_const.sub continuous_subtype_val)).aestronglyMeasurable
    refine hG.congr (Filter.Eventually.of_forall fun u => ?_)
    change suzukiScrewG (a.1 - (u : ℝ)) =
      (GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - (u : ℝ)) : ℂ)
    rw [suzukiScrewG_eq_sourceScrew_core]
  have hbound : ∀ u : SuzukiApertureInterval a.1,
      ‖(GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - (u : ℝ)) : ℂ)‖ ≤ C := by
    intro u
    have h := hC right u
    rw [suzukiScrewG_eq_sourceScrew_core] at h
    exact h
  exact ((Lp.memLp (f : SuzukiApertureIntervalL2 a.1)).integrable (by norm_num)).bdd_mul
    hmult (Filter.Eventually.of_forall hbound)

set_option maxHeartbeats 100000 in
theorem integrable_suzukiSourceEndpointKernel_pair
    (a : SuzukiPositiveAperture) (f q : SuzukiApertureZeroMean a) :
    Integrable (fun p : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 =>
      (GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - (p.2 : ℝ)) : ℂ) *
        (f : SuzukiApertureIntervalL2 a.1) p.2 *
          (starRingEnd ℂ) ((q : SuzukiApertureIntervalL2 a.1) p.1))
      ((volume : Measure (SuzukiApertureInterval a.1)).prod volume) := by
  have hq := integrable_conj_suzukiApertureCoe a.1
    (q : SuzukiApertureIntervalL2 a.1)
  have hf := integrable_suzukiSourceEndpoint_mul a f
  refine (hq.mul_prod hf).congr (Filter.Eventually.of_forall fun p => ?_)
  ring

set_option maxHeartbeats 200000

/-- The reverse-primitive adjoint witness maps exactly to Suzuki's raw zero-mean screw
compression.  This is the range identity behind Suzuki's inclusion
`Gₐ(L²₀(-a,a)) ⊆ Dom(D*)`. -/
theorem suzukiDirichletInverseAdjointCLM_adjointWitness_eq
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    suzukiDirichletInverseAdjointCLM a
        (suzukiRawScrewAdjointWitness a
          (f : SuzukiApertureIntervalL2 a.1)) =
      suzukiScrewZeroMeanOperator a f := by
  apply ext_inner_left ℂ
  intro q
  rw [inner_suzukiScrewZeroMeanOperator_eq_raw]
  change inner ℂ q
      (suzukiApertureZeroMeanProjection a
        (suzukiApertureUpperPrimitiveCLM a
          (suzukiRawScrewAdjointWitness a
            (f : SuzukiApertureIntervalL2 a.1)))) = _
  rw [suzukiApertureZeroMeanProjection,
    (SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [inner_suzukiApertureL2_eq_integral]
  let μ : Measure (SuzukiApertureInterval a.1) := volume
  let F : SuzukiApertureIntervalL2 a.1 := f
  let Q : SuzukiApertureIntervalL2 a.1 := q
  let A : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    (GaloisForLFunctions.RHTower.suzukiSourceScrew
        ((p.1 : ℝ) - (p.2 : ℝ)) : ℂ) * F p.2 *
      (starRingEnd ℂ) (Q p.1)
  let E : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    (GaloisForLFunctions.RHTower.suzukiSourceScrew
        (a.1 - (p.2 : ℝ)) : ℂ) * F p.2 *
      (starRingEnd ℂ) (Q p.1)
  have hA : Integrable A (μ.prod μ) := by
    simpa only [A, F, Q, μ] using integrable_suzukiRawSourceKernel_pair a f q
  have hE : Integrable E (μ.prod μ) := by
    simpa only [E, F, Q, μ] using
      integrable_suzukiSourceEndpointKernel_pair a f q
  have hEzero : (∫ p, E p ∂(μ.prod μ)) = 0 := by
    calc
      (∫ p, E p ∂(μ.prod μ)) =
          ∫ p, (starRingEnd ℂ) (Q p.1) *
            ((GaloisForLFunctions.RHTower.suzukiSourceScrew
                (a.1 - (p.2 : ℝ)) : ℂ) * F p.2) ∂(μ.prod μ) := by
            apply integral_congr_ae
            filter_upwards with p
            simp only [E]
            ring
      _ = (∫ t : SuzukiApertureInterval a.1,
              (starRingEnd ℂ) (Q t) ∂μ) *
            ∫ u : SuzukiApertureInterval a.1,
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                (a.1 - (u : ℝ)) : ℂ) * F u ∂μ :=
          integral_prod_mul (μ := μ) (ν := μ)
            (fun t : SuzukiApertureInterval a.1 =>
              (starRingEnd ℂ) (Q t))
            (fun u : SuzukiApertureInterval a.1 =>
              (GaloisForLFunctions.RHTower.suzukiSourceScrew
                (a.1 - (u : ℝ)) : ℂ) * F u)
      _ = 0 := by
        change (∫ t : SuzukiApertureInterval a.1,
          (starRingEnd ℂ) ((q : SuzukiApertureIntervalL2 a.1) t) ∂volume) * _ = 0
        rw [integral_conj_suzukiAperture_eq_zero a q, zero_mul]
  calc
    (∫ t : SuzukiApertureInterval a.1,
        (starRingEnd ℂ) ((q : SuzukiApertureIntervalL2 a.1) t) *
          suzukiApertureUpperPrimitiveCLM a
            (suzukiRawScrewAdjointWitness a
              (f : SuzukiApertureIntervalL2 a.1)) t ∂volume) =
        ∫ t : SuzukiApertureInterval a.1,
          (starRingEnd ℂ) (Q t) *
            suzukiApertureUpperPrefix a.1
              (suzukiRawScrewAdjointWitness a F) t ∂μ := by
          apply integral_congr_ae
          filter_upwards [suzukiApertureUpperPrimitive_coeFn a.1
            (suzukiRawScrewAdjointWitness a F)] with t ht
          change (starRingEnd ℂ) (Q t) *
              (suzukiApertureUpperPrimitive a.1
                (suzukiRawScrewAdjointWitness a F)) t = _
          rw [ht]
    _ = ∫ t : SuzukiApertureInterval a.1, ∫ u : SuzukiApertureInterval a.1,
          (A (t, u) - E (t, u)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [suzukiApertureUpperPrefix_adjointWitness a F t,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      simp only [A, E]
      push_cast
      ring
    _ = ∫ p, (A p - E p) ∂(μ.prod μ) := by
      rw [integral_integral (hA.sub hE)]
    _ = (∫ p, A p ∂(μ.prod μ)) - ∫ p, E p ∂(μ.prod μ) := by
      simpa only [Pi.sub_apply] using integral_sub hA hE
    _ = ∫ p, A p ∂(μ.prod μ) := by rw [hEzero, sub_zero]
    _ = ∫ t : SuzukiApertureInterval a.1, ∫ u : SuzukiApertureInterval a.1,
          suzukiScrewG ((t : ℝ) - (u : ℝ)) * F u *
            (starRingEnd ℂ) (Q t) ∂μ ∂μ := by
      calc
        (∫ p, A p ∂(μ.prod μ)) =
            ∫ t : SuzukiApertureInterval a.1,
              ∫ u : SuzukiApertureInterval a.1, A (t, u) ∂μ ∂μ := by
          symm
          simpa only using integral_integral hA
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with t
          apply integral_congr_ae
          filter_upwards with u
          simp only [A]
          rw [suzukiScrewG_eq_sourceScrew_core]
    _ = suzukiRawScrewIntervalForm a.1 F Q := rfl

end RHTower

end
