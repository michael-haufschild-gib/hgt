import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.HTGeometry.GreedySingularValues
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
open scoped ComplexOrder InnerProduct InnerProductSpace

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

/-- The symmetric physical cutoff remains an idempotent projection after restriction to the
even carrier. -/
theorem evenIndicatorCutoff_idempotent (a : ℝ) :
    IsIdempotentElem (evenIndicatorCutoff a) := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) = _
  have h := indicatorCutoff_idempotent (centralInterval a) (measurableSet_centralInterval a)
  exact DFunLike.congr_fun (show
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) ∘L
        indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) =
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) by
      simpa only [ContinuousLinearMap.mul_def] using h) (f : SoninL2)

/-- The paper's even time-limited carrier: the range of the physical aperture projection. -/
def evenTimeLimitedSubspace (a : ℝ) : Submodule ℂ evenSubspace :=
  LinearMap.range (evenIndicatorCutoff a).toLinearMap

noncomputable instance evenTimeLimitedSubspace_completeSpace (a : ℝ) :
    CompleteSpace (evenTimeLimitedSubspace a) := by
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (evenIndicatorCutoff_idempotent a)).completeSpace_coe

/-- Membership in the time-limited carrier is equivalent to being fixed by the aperture cutoff. -/
theorem mem_evenTimeLimitedSubspace_iff (a : ℝ) (f : evenSubspace) :
    f ∈ evenTimeLimitedSubspace a ↔ evenIndicatorCutoff a f = f := by
  exact LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (evenIndicatorCutoff_idempotent a))

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

/-- The paper's actual constrained carrier: even, supported in the aperture, and orthogonal to the
Riesz vector of the integral functional. -/
def constrainedProlateSubspace (a : ℝ) : Submodule ℂ evenSubspace :=
  evenTimeLimitedSubspace a ⊓
    (Submodule.span ℂ {evenCentralIndicator a})ᗮ

noncomputable instance constrainedProlateSubspace_completeSpace (a : ℝ) :
    CompleteSpace (constrainedProlateSubspace a) := by
  unfold constrainedProlateSubspace evenTimeLimitedSubspace
  exact ((ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (evenIndicatorCutoff_idempotent a)).inter
      (Submodule.isClosed_orthogonal _)).completeSpace_coe

noncomputable instance constrainedProlateSubspace_hasOrthogonalProjection (a : ℝ) :
    (constrainedProlateSubspace a).HasOrthogonalProjection := by infer_instance

theorem mem_constrainedProlateSubspace_iff (a : ℝ) (f : evenSubspace) :
    f ∈ constrainedProlateSubspace a ↔
      evenIndicatorCutoff a f = f ∧
      ∫ x : ℝ in centralInterval a, (f : SoninL2) x = 0 := by
  rw [constrainedProlateSubspace, Submodule.mem_inf, mem_evenTimeLimitedSubspace_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  change evenIndicatorCutoff a f = f ∧
    inner ℂ
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

/-- On the actual constrained carrier, the compressed quadratic form is exactly the physical
Fourier leakage.  Orthogonal compression changes the vector output but not its pairing with a
constrained test vector. -/
theorem constrainedProlateLeakage_inner_eq (a : ℝ)
    (f : constrainedProlateSubspace a) :
    inner ℂ (constrainedProlateLeakage a f) f =
      ((‖f‖ ^ 2 - ‖evenTimeBandFourier a (f : evenSubspace)‖ ^ 2 : ℝ) : ℂ) := by
  rw [constrainedProlateLeakage_eq_compression]
  change inner ℂ
      ((constrainedProlateSubspace a).orthogonalProjection
        (evenProlateLeakage a (f : evenSubspace))) f = _
  rw [(constrainedProlateSubspace a).inner_orthogonalProjection_eq_of_mem_right]
  exact evenProlateLeakage_inner_eq a (f : evenSubspace)

theorem constrainedProlateLeakage_inner_nonneg (a : ℝ)
    (f : constrainedProlateSubspace a) :
    0 ≤ inner ℂ (constrainedProlateLeakage a f) f :=
  (constrainedProlateLeakage_isPositive a).inner_nonneg_left f

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

/-! ## Unconditional concentration spectrum -/

/-- Every output of the compressed Fourier block lies in the physical aperture range. -/
theorem evenTimeBandFourier_mem_timeLimited (a : ℝ) (f : evenSubspace) :
    evenTimeBandFourier a f ∈ evenTimeLimitedSubspace a := by
  change evenTimeBandFourier a f ∈ LinearMap.range (evenIndicatorCutoff a).toLinearMap
  refine ⟨evenFourierTransform (evenIndicatorCutoff a f), ?_⟩
  rw [evenTimeBandFourier_eq_mul]
  rfl

theorem evenProlateConcentration_mem_timeLimited (a : ℝ) (f : evenSubspace) :
    evenProlateConcentration a f ∈ evenTimeLimitedSubspace a := by
  rw [evenProlateConcentration_eq_sq]
  exact evenTimeBandFourier_mem_timeLimited a _

/-- The decreasing greedy eigenvalue sequence of the concrete compact positive concentration
operator.  These are the squared concentration values, with multiplicity. -/
noncomputable def evenProlateConcentrationValue (a : ℝ) (n : ℕ) : ℝ :=
  ContinuousLinearMap.svVal (evenProlateConcentration a) n

/-- The corresponding greedy concentration modes. A mode is zero exactly at exhausted stages. -/
noncomputable def evenProlateConcentrationMode (a : ℝ) (n : ℕ) : evenSubspace :=
  ContinuousLinearMap.svVec (evenProlateConcentration a) n

theorem evenProlateConcentrationValue_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ evenProlateConcentrationValue a n :=
  ContinuousLinearMap.svVal_nonneg _ n

theorem evenProlateConcentrationValue_antitone (a : ℝ) :
    Antitone (evenProlateConcentrationValue a) :=
  ContinuousLinearMap.svVal_antitone _

/-- The eigen-equation holds unconditionally, including exhausted zero modes. -/
theorem evenProlateConcentration_apply_mode (a : ℝ) (n : ℕ) :
    evenProlateConcentration a (evenProlateConcentrationMode a n) =
      (evenProlateConcentrationValue a n : ℂ) • evenProlateConcentrationMode a n :=
  ContinuousLinearMap.apply_svVec _ n

theorem evenProlateConcentrationMode_orthogonal_of_ne
    (a : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (evenProlateConcentrationMode a m)
      (evenProlateConcentrationMode a n) = 0 :=
  ContinuousLinearMap.inner_svVec_svVec_of_ne _ hmn

/-- Every live greedy mode has unit norm. -/
theorem norm_evenProlateConcentrationMode_of_value_ne_zero
    (a : ℝ) (ha : 0 < a) {n : ℕ}
    (hn : evenProlateConcentrationValue a n ≠ 0) :
    ‖evenProlateConcentrationMode a n‖ = 1 := by
  exact ContinuousLinearMap.norm_svVec_of_ne_zero
    (isCompactOperator_evenProlateConcentration a ha)
    (evenProlateConcentration_isPositive a).isSymmetric
    (fun x => (evenProlateConcentration_isPositive a).re_inner_nonneg_right x) hn

/-- Compactness forces the concentration eigenvalues to vanish. -/
theorem evenProlateConcentrationValue_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (evenProlateConcentrationValue a) Filter.atTop (nhds 0) := by
  exact ContinuousLinearMap.svVal_tendsto_zero
    (isCompactOperator_evenProlateConcentration a ha)
    (evenProlateConcentration_isPositive a).isSymmetric
    (fun x => (evenProlateConcentration_isPositive a).re_inner_nonneg_right x)

/-- Every nonzero concentration mode is automatically supported in the physical aperture. -/
theorem evenProlateConcentrationMode_mem_timeLimited_of_value_ne_zero
    (a : ℝ) {n : ℕ} (hn : evenProlateConcentrationValue a n ≠ 0) :
    evenProlateConcentrationMode a n ∈ evenTimeLimitedSubspace a := by
  let μ : ℂ := (evenProlateConcentrationValue a n : ℂ)
  have hμ : μ ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hout := evenProlateConcentration_mem_timeLimited a
    (evenProlateConcentrationMode a n)
  have heig := evenProlateConcentration_apply_mode a n
  have hscaled : μ⁻¹ • evenProlateConcentration a
      (evenProlateConcentrationMode a n) ∈ evenTimeLimitedSubspace a :=
    (evenTimeLimitedSubspace a).smul_mem μ⁻¹ hout
  rw [heig] at hscaled
  change μ⁻¹ • μ • evenProlateConcentrationMode a n ∈
    evenTimeLimitedSubspace a at hscaled
  rw [inv_smul_smul₀ hμ] at hscaled
  exact hscaled

theorem norm_evenProlateConcentration_le (a : ℝ) (f : evenSubspace) :
    ‖evenProlateConcentration a f‖ ≤ ‖f‖ := by
  rw [evenProlateConcentration_eq_sq]
  exact (norm_evenTimeBandFourier_le a _).trans
    (norm_evenTimeBandFourier_le a f)

theorem norm_evenProlateConcentration_le_one (a : ℝ) :
    ‖evenProlateConcentration a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_evenProlateConcentration_le a f

theorem evenProlateConcentrationValue_le_one (a : ℝ) (n : ℕ) :
    evenProlateConcentrationValue a n ≤ 1 := by
  calc
    evenProlateConcentrationValue a n
        ≤ ‖evenProlateConcentration a‖ :=
      ContinuousLinearMap.orthSup_le_opNorm _ _ _
    _ ≤ 1 := norm_evenProlateConcentration_le_one a

/-- The leakage deficits corresponding to the concrete decreasing concentration spectrum. -/
noncomputable def evenProlateLeakageValue (a : ℝ) (n : ℕ) : ℝ :=
  1 - evenProlateConcentrationValue a n

theorem evenProlateLeakageValue_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ evenProlateLeakageValue a n :=
  sub_nonneg.mpr (evenProlateConcentrationValue_le_one a n)

theorem evenProlateLeakageValue_monotone (a : ℝ) :
    Monotone (evenProlateLeakageValue a) := by
  intro m n hmn
  exact sub_le_sub_left (evenProlateConcentrationValue_antitone a hmn) 1

theorem evenProlateLeakageValue_tendsto_one (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (evenProlateLeakageValue a) Filter.atTop (nhds 1) := by
  simpa [evenProlateLeakageValue] using
    (tendsto_const_nhds.sub (evenProlateConcentrationValue_tendsto_zero a ha))

/-- The concentration modes diagonalize the full even leakage operator with complementary
eigenvalues. -/
theorem evenProlateLeakage_apply_mode (a : ℝ) (n : ℕ) :
    evenProlateLeakage a (evenProlateConcentrationMode a n) =
      (evenProlateLeakageValue a n : ℂ) • evenProlateConcentrationMode a n := by
  rw [evenProlateLeakage, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, evenProlateConcentration_apply_mode]
  simp only [evenProlateLeakageValue, Complex.ofReal_sub, Complex.ofReal_one]
  module

end RHTower
