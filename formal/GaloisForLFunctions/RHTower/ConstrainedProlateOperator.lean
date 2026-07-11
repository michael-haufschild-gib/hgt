import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Concrete constrained prolate operator

This module builds the operator layer used by the constrained-prolate cards from the project's
actual Fourier and cutoff operators.

For aperture `a`, it defines the compressed Fourier block `Tₐ = Pₐ F Pₐ` on even
`L²(ℝ)`, the concentration `Tₐ†Tₐ = Tₐ²`, and the leakage `I - Tₐ²`.  It also constructs the
central-interval indicator as the exact Riesz vector of the integral functional and compresses
the concentration and leakage operators to its orthogonal complement.

All results here are unconditional.  In particular, no prolate eigenbasis, Fuchs asymptotic,
spectral-gap estimate, Weil positivity, or RH statement is assumed.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The unitary Fourier transform restricted to the actual even `L²(ℝ)` carrier. -/
def evenFourierTransform : evenSubspace →L[ℂ] evenSubspace :=
  fourierUnitary.toLinearIsometry.toContinuousLinearMap.restrict (by
    intro f hf
    apply (mem_evenSubspace_iff _).mpr
    change l2Reflection (fourierUnitary f) = fourierUnitary f
    rw [← fourierUnitary_l2Reflection, (mem_evenSubspace_iff f).mp hf])

@[simp] theorem coe_evenFourierTransform_apply (f : evenSubspace) :
    ((evenFourierTransform f : evenSubspace) : SoninL2) = fourierUnitary f := rfl

@[simp] theorem evenFourierTransform_involutive (f : evenSubspace) :
    evenFourierTransform (evenFourierTransform f) = f := by
  apply Subtype.ext
  change fourierUnitary (fourierUnitary (f : SoninL2)) = f
  have hf : l2Reflection (f : SoninL2) = f := (mem_evenSubspace_iff f).mp f.property
  have hsymm : fourierUnitary.symm (f : SoninL2) = fourierUnitary f := by
    rw [fourierUnitary_symm_eq_reflection_fourier]
    rw [← fourierUnitary_l2Reflection, hf]
  rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]

theorem evenFourierTransform_isometry (f : evenSubspace) :
    ‖evenFourierTransform f‖ = ‖f‖ := by
  exact fourierUnitary.norm_map f

theorem evenFourierTransform_symmetric : evenFourierTransform.IsSymmetric := by
  intro f g
  calc
    inner ℂ (evenFourierTransform f) g =
        inner ℂ (evenFourierTransform f)
          (evenFourierTransform (evenFourierTransform g)) := by
      rw [evenFourierTransform_involutive]
    _ = inner ℂ f (evenFourierTransform g) :=
      fourierUnitary.inner_map_map f (evenFourierTransform g)

theorem adjoint_evenFourierTransform :
    evenFourierTransform† = evenFourierTransform :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr evenFourierTransform_symmetric

/-- The full `Pₐ F Pₐ` block preserves the even carrier. -/
theorem cutoffFourierCutoff_central_mapsTo_evenSubspace (a : ℝ) :
    Set.MapsTo (cutoffFourierCutoff (-a) a (-a) a) evenSubspace evenSubspace := by
  intro f hf
  exact indicatorCutoff_central_mapsTo_evenSubspace a
    ((by
      apply (mem_evenSubspace_iff _).mpr
      change l2Reflection (fourierUnitary _) = fourierUnitary _
      rw [← fourierUnitary_l2Reflection, (mem_evenSubspace_iff _).mp
        (indicatorCutoff_central_mapsTo_evenSubspace a hf)]) :
      fourierUnitary
        (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) ∈ evenSubspace)

/-- The actual compact compressed Fourier operator `Tₐ = Pₐ F Pₐ` on even `L²(ℝ)`. -/
def evenTimeBandFourier (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (cutoffFourierCutoff (-a) a (-a) a).restrict
    (cutoffFourierCutoff_central_mapsTo_evenSubspace a)

@[simp] theorem coe_evenTimeBandFourier_apply (a : ℝ) (f : evenSubspace) :
    ((evenTimeBandFourier a f : evenSubspace) : SoninL2) =
      cutoffFourierCutoff (-a) a (-a) a f := rfl

theorem evenTimeBandFourier_eq_mul (a : ℝ) :
    evenTimeBandFourier a =
      evenIndicatorCutoff a * evenFourierTransform * evenIndicatorCutoff a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  rfl

theorem isCompactOperator_evenTimeBandFourier (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (evenTimeBandFourier a) := by
  have hfull : IsCompactOperator (cutoffFourierCutoff (-a) a (-a) a) :=
    isCompactOperator_cutoffFourierCutoff (-a) a (-a) a (by linarith)
  exact (hfull.comp_clm evenSubspace.subtypeL).codRestrict
    (fun f => (cutoffFourierCutoff_central_mapsTo_evenSubspace a f.property))
    (completeSpace_coe_iff_isComplete.mp
      (inferInstance : CompleteSpace evenSubspace)).isClosed

theorem adjoint_evenTimeBandFourier (a : ℝ) :
    (evenTimeBandFourier a)† = evenTimeBandFourier a := by
  rw [evenTimeBandFourier_eq_mul]
  change ((evenIndicatorCutoff a ∘L evenFourierTransform) ∘L evenIndicatorCutoff a)† = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenIndicatorCutoff, adjoint_evenFourierTransform]
  noncomm_ring

/-- The concentration operator `Tₐ†Tₐ`; self-adjointness of `Tₐ` identifies this with `Tₐ²`. -/
def evenProlateConcentration (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (evenTimeBandFourier a)† ∘L evenTimeBandFourier a

theorem evenProlateConcentration_eq_sq (a : ℝ) :
    evenProlateConcentration a = evenTimeBandFourier a * evenTimeBandFourier a := by
  rw [evenProlateConcentration, adjoint_evenTimeBandFourier]
  rfl

theorem evenProlateConcentration_isPositive (a : ℝ) :
    (evenProlateConcentration a).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self (evenTimeBandFourier a)

theorem isCompactOperator_evenProlateConcentration (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (evenProlateConcentration a) := by
  exact (isCompactOperator_evenTimeBandFourier a ha).clm_comp
    ((evenTimeBandFourier a)†)

/-- The prolate leakage operator `Bₐ = I - Tₐ²`. -/
def evenProlateLeakage (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  1 - evenProlateConcentration a

lemma norm_evenIndicatorCutoff_le (a : ℝ) (f : evenSubspace) :
    ‖evenIndicatorCutoff a f‖ ≤ ‖f‖ := by
  change ‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
    (f : SoninL2)‖ ≤ ‖(f : SoninL2)‖
  rw [indicatorCutoff_eq_physicalForbidden_starProjection]
  exact (physicalForbidden (centralInterval a)
    (measurableSet_centralInterval a)).norm_starProjection_apply_le f

theorem norm_evenTimeBandFourier_le (a : ℝ) (f : evenSubspace) :
    ‖evenTimeBandFourier a f‖ ≤ ‖f‖ := by
  rw [evenTimeBandFourier_eq_mul]
  calc
    ‖evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a f))‖
        ≤ ‖evenFourierTransform (evenIndicatorCutoff a f)‖ :=
      norm_evenIndicatorCutoff_le a _
    _ = ‖evenIndicatorCutoff a f‖ := evenFourierTransform_isometry _
    _ ≤ ‖f‖ := norm_evenIndicatorCutoff_le a f

theorem evenProlateLeakage_inner_eq (a : ℝ) (f : evenSubspace) :
    inner ℂ (evenProlateLeakage a f) f =
      ((‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2 : ℝ) : ℂ) := by
  rw [evenProlateLeakage, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, evenProlateConcentration]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  simp [inner_self_eq_norm_sq_to_K]

theorem evenProlateLeakage_isPositive (a : ℝ) :
    (evenProlateLeakage a).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  constructor
  · exact LinearMap.IsSymmetric.one.sub
      (evenProlateConcentration_isPositive a).isSymmetric
  intro f
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, evenProlateLeakage_inner_eq]
  change 0 ≤ ‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2
  have h := norm_evenTimeBandFourier_le a f
  nlinarith [norm_nonneg f, norm_nonneg (evenTimeBandFourier a f)]

/-- The unnormalized indicator of the central interval, as a vector in even `L²(ℝ)`. -/
def evenCentralIndicator (a : ℝ) : evenSubspace :=
  ⟨indicatorConstLp 2 (measurableSet_centralInterval a) measure_Icc_lt_top.ne (1 : ℂ), by
    apply (mem_evenSubspace_iff _).mpr
    apply Lp.ext
    have hneg := (indicatorConstLp_coeFn (p := 2) (μ := volume)
      (s := centralInterval a) (hs := measurableSet_centralInterval a)
      (hμs := measure_Icc_lt_top.ne) (c := (1 : ℂ))).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
    filter_upwards [l2Reflection_ae
      (indicatorConstLp 2 (measurableSet_centralInterval a) measure_Icc_lt_top.ne (1 : ℂ)),
      hneg,
      indicatorConstLp_coeFn (p := 2) (μ := volume)
        (s := centralInterval a) (hs := measurableSet_centralInterval a)
        (hμs := measure_Icc_lt_top.ne) (c := (1 : ℂ))] with x href hleft hright
    have hleft' :
        (indicatorConstLp 2 (measurableSet_centralInterval a)
          measure_Icc_lt_top.ne (1 : ℂ) : SoninL2) (-x) =
          (centralInterval a).indicator (fun _ => (1 : ℂ)) (-x) := by
      simpa [Function.comp_apply] using hleft
    rw [href, hleft', hright]
    by_cases hx : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((neg_mem_centralInterval_iff a x).2 hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (mt (neg_mem_centralInterval_iff a x).1 hx)]⟩

noncomputable instance constrainedProlateConstraintSpan_completeSpace (a : ℝ) :
    CompleteSpace (Submodule.span ℂ {evenCentralIndicator a}) :=
  FiniteDimensional.complete ℂ _

/-- The zero-integral constraint, expressed by its exact Riesz vector. -/
def constrainedProlateSubspace (a : ℝ) : Submodule ℂ evenSubspace :=
  (Submodule.span ℂ {evenCentralIndicator a})ᗮ

noncomputable instance constrainedProlateSubspace_hasOrthogonalProjection (a : ℝ) :
    (constrainedProlateSubspace a).HasOrthogonalProjection := by
  unfold constrainedProlateSubspace
  infer_instance

noncomputable instance constrainedProlateSubspace_completeSpace (a : ℝ) :
    CompleteSpace (constrainedProlateSubspace a) := by
  unfold constrainedProlateSubspace
  infer_instance

theorem mem_constrainedProlateSubspace_iff (a : ℝ) (f : evenSubspace) :
    f ∈ constrainedProlateSubspace a ↔
      ∫ x : ℝ in centralInterval a, (f : SoninL2) x = 0 := by
  rw [constrainedProlateSubspace, Submodule.mem_orthogonal_singleton_iff_inner_left]
  rw [inner_eq_zero_symm]
  change inner ℂ
    (indicatorConstLp 2 (measurableSet_centralInterval a) measure_Icc_lt_top.ne (1 : ℂ))
      (f : SoninL2) = 0 ↔ _
  rw [MeasureTheory.L2.inner_indicatorConstLp_one]

/-- The concentration operator compressed to the exact zero-integral subspace. -/
def constrainedProlateConcentration (a : ℝ) :
    constrainedProlateSubspace a →L[ℂ] constrainedProlateSubspace a :=
  (constrainedProlateSubspace a).orthogonalProjection ∘L
    evenProlateConcentration a ∘L (constrainedProlateSubspace a).subtypeL

theorem constrainedProlateConcentration_isPositive (a : ℝ) :
    ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := constrainedProlateSubspace a)
      (constrainedProlateConcentration a) := by
  exact (evenProlateConcentration_isPositive a).orthogonalProjection_comp
    (constrainedProlateSubspace a)

theorem isCompactOperator_constrainedProlateConcentration (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (constrainedProlateConcentration a) := by
  exact ((isCompactOperator_evenProlateConcentration a ha).comp_clm
    (constrainedProlateSubspace a).subtypeL).clm_comp
      (constrainedProlateSubspace a).orthogonalProjection

/-- The actual constrained prolate leakage operator: identity minus the compressed concentration. -/
def constrainedProlateLeakage (a : ℝ) :
    constrainedProlateSubspace a →L[ℂ] constrainedProlateSubspace a :=
  (1 : constrainedProlateSubspace a →L[ℂ] constrainedProlateSubspace a) -
    constrainedProlateConcentration a

theorem constrainedProlateLeakage_eq_compression (a : ℝ) :
    constrainedProlateLeakage a =
      (constrainedProlateSubspace a).orthogonalProjection ∘L
        evenProlateLeakage a ∘L (constrainedProlateSubspace a).subtypeL := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [constrainedProlateLeakage, constrainedProlateConcentration,
    evenProlateLeakage, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply]
  rw [map_sub]
  rw [Submodule.subtypeL_apply]
  rw [(constrainedProlateSubspace a).orthogonalProjection_mem_subspace_eq_self]

theorem constrainedProlateLeakage_isPositive (a : ℝ) :
    ContinuousLinearMap.IsPositive (𝕜 := ℂ) (E := constrainedProlateSubspace a)
      (constrainedProlateLeakage a) := by
  rw [constrainedProlateLeakage_eq_compression]
  exact (evenProlateLeakage_isPositive a).orthogonalProjection_comp
    (constrainedProlateSubspace a)

theorem constrainedProlateLeakage_sub_identity_isCompact (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (constrainedProlateLeakage a -
      (1 : constrainedProlateSubspace a →L[ℂ] constrainedProlateSubspace a)) := by
  have h := (isCompactOperator_constrainedProlateConcentration a ha).neg
  have heq : constrainedProlateLeakage a -
      (1 : constrainedProlateSubspace a →L[ℂ] constrainedProlateSubspace a) =
      -constrainedProlateConcentration a := by
    rw [constrainedProlateLeakage]
    abel
  rwa [heq]

end RHTower

