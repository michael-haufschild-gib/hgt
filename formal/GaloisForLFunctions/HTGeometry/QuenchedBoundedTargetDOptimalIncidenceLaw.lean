import GaloisForLFunctions.HTGeometry.BoundedTargetDOptimalIncidenceLaw

open Filter MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Annealed one-target moments imply a quenched complete-continuum capture
tail.  One D-optimal reporter is chosen before the draw, so no circuit union
or draw-dependent selector occurs. -/
theorem measure_draws_with_large_boundedTargetCapture_le
    {Y X C : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [Nonempty C] {n : ℕ}
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (mu : Measure X) [IsFiniteMeasure mu]
    (hmu : mu.real Set.univ ≤ 1)
    (target : C → Fin (n + 1) → ℂ)
    (state : Y → X → Fin (n + 1) → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hbounded : Bornology.IsBounded (Set.range target))
    (hspan : Submodule.span ℂ (Set.range target) = ⊤)
    (hprodJoint : ∀ i j, Integrable
      (fun p : Y × X ↦ state p.1 p.2 i * star (state p.1 p.2 j))
      (nu.prod mu))
    (hprodSection : ∀ y i j, Integrable
      (fun x ↦ state y x i * star (state y x j)) mu)
    (hmeasCapture : Measurable (fun y ↦
      mu.real (finitePositiveReporterCaptureEvent
        target (state y) threshold)))
    (q : ℝ)
    (hmomentJoint : ∀ c, ∫ p : Y × X,
      ‖finiteComplexInner (state p.1 p.2) (target c)‖ ^ (2 : ℕ)
        ∂(nu.prod mu) ≤ q)
    (level : ℝ) (hlevel : 0 < level) :
    nu.real {y | level ≤ threshold *
        mu.real (finitePositiveReporterCaptureEvent
          target (state y) threshold)} ≤
      ((n + 1 : ℝ) * q) / level := by
  have htargetNe : (Set.range target).Nonempty := Set.range_nonempty target
  obtain ⟨M, hMbody, hMpd, hleverage⟩ :=
    exists_boundedDOptimalCovariance htargetNe hbounded hspan
  let jointState : Y × X → Fin (n + 1) → ℂ :=
    fun p ↦ state p.1 p.2
  have hJointEnergy : Integrable
      (fun p ↦ finitePositiveReporterSourceEnergy M (jointState p))
      (nu.prod mu) :=
    finitePositiveReporterSourceEnergy_integrable
      (nu.prod mu) jointState M hprodJoint
  have hSectionEnergy : ∀ y, Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy M (state y x)) mu := by
    intro y
    exact finitePositiveReporterSourceEnergy_integrable
      mu (state y) M (hprodSection y)
  let captureMass : Y → ℝ := fun y ↦
    threshold * mu.real
      (finitePositiveReporterCaptureEvent target (state y) threshold)
  let sourceMass : Y → ℝ := fun y ↦
    (n + 1 : ℝ) *
      ∫ x, finitePositiveReporterSourceEnergy M (state y x) ∂mu
  have hcaptureLe : ∀ y, captureMass y ≤ sourceMass y := by
    intro y
    exact finitePositiveReporter_completeIncidence_bound
      mu M hMpd target (state y) threshold hthreshold (n + 1 : ℝ)
        (by positivity)
        (fun c ↦ by
          simpa [finitePositiveReporterTargetLeverage] using
            hleverage (target c) ⟨c, rfl⟩)
        (hSectionEnergy y)
  have hcaptureNonneg : ∀ y, 0 ≤ captureMass y := by
    intro y
    exact mul_nonneg hthreshold.le (measureReal_nonneg)
  have hcaptureMeas : Measurable captureMass := by
    exact hmeasCapture.const_mul threshold
  have hcaptureBound : ∀ y, |captureMass y| ≤ threshold := by
    intro y
    rw [abs_of_nonneg (hcaptureNonneg y)]
    dsimp [captureMass]
    have hmass : mu.real
        (finitePositiveReporterCaptureEvent target (state y) threshold) ≤ 1 := by
      exact (measureReal_mono (Set.subset_univ _)).trans hmu
    nlinarith
  have hcaptureInt : Integrable captureMass nu :=
    (integrable_const threshold).mono' hcaptureMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs]
        exact hcaptureBound y)
  have hsourceInt : Integrable sourceMass nu := by
    dsimp [sourceMass]
    exact hJointEnergy.integral_prod_left.const_mul (n + 1 : ℝ)
  have hray : ∀ v ∈ Set.range target,
      (star v ⬝ᵥ
        (finitePositiveReporterSourceCovariance (nu.prod mu) jointState *ᵥ v)).re ≤ q := by
    intro v hv
    obtain ⟨c, rfl⟩ := hv
    calc
      (star (target c) ⬝ᵥ
          (finitePositiveReporterSourceCovariance (nu.prod mu) jointState *ᵥ
            target c)).re =
          ((finitePositiveReporterSourceCovariance (nu.prod mu) jointState *
            finiteBuresTargetRay (target c)).trace).re :=
        (traceProduct_ray
          (finitePositiveReporterSourceCovariance (nu.prod mu) jointState)
          (target c)).symm
      _ = ∫ p, finitePositiveReporterSourceEnergy
            (finiteBuresTargetRay (target c)) (jointState p) ∂(nu.prod mu) :=
        finitePositiveReporter_re_trace_covariance_mul_eq_integral
          (nu.prod mu) jointState (finiteBuresTargetRay (target c)) hprodJoint
      _ = ∫ p, ‖finiteComplexInner (jointState p) (target c)‖ ^ (2 : ℕ)
            ∂(nu.prod mu) := by
        apply integral_congr_ae
        filter_upwards [] with p
        exact sourceEnergy_targetRay
          (jointState p) (target c)
      _ ≤ q := hmomentJoint c
  have hpair :
      ((finitePositiveReporterSourceCovariance (nu.prod mu) jointState * M).trace).re ≤ q :=
    traceProduct_le_on_occupiedBody
      (finitePositiveReporterSourceCovariance (nu.prod mu) jointState)
      hray M hMbody
  have hmeanSource : ∫ y, sourceMass y ∂nu ≤ (n + 1 : ℝ) * q := by
    calc
      ∫ y, sourceMass y ∂nu =
          (n + 1 : ℝ) * ∫ y, ∫ x,
            finitePositiveReporterSourceEnergy M (state y x) ∂mu ∂nu := by
        rw [integral_const_mul]
      _ = (n + 1 : ℝ) * ∫ p,
            finitePositiveReporterSourceEnergy M (jointState p) ∂(nu.prod mu) := by
        rw [MeasureTheory.integral_prod _ hJointEnergy]
      _ = (n + 1 : ℝ) *
          ((finitePositiveReporterSourceCovariance (nu.prod mu) jointState * M).trace).re := by
        rw [finitePositiveReporter_re_trace_covariance_mul_eq_integral
          (nu.prod mu) jointState M hprodJoint]
      _ ≤ (n + 1 : ℝ) * q :=
        mul_le_mul_of_nonneg_left hpair (by positivity)
  have hmeanCapture : ∫ y, captureMass y ∂nu ≤ (n + 1 : ℝ) * q := by
    exact (integral_mono hcaptureInt hsourceInt hcaptureLe).trans hmeanSource
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hcaptureNonneg) hcaptureInt level
  rw [le_div_iff₀ hlevel, mul_comm]
  exact hmark.trans hmeanCapture

end

end GaloisForLFunctions.HTGeometry
