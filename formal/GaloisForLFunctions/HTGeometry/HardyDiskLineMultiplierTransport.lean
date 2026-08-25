import GaloisForLFunctions.HTGeometry.HardyDiskLineCayleyUnitary
import GaloisForLFunctions.HTGeometry.HardyMultiplierZeroModelDimension
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneNormalizedBlaschkeCayley
import GaloisForLFunctions.HTGeometry.IndexedBlaschkeIsometry

/-!
# Operator transport through the exact Hardy Cayley unitary

The equal-Gram Cayley unitary is upgraded from its action on reproducing features to exact
conjugation of arbitrary bounded Hardy operators.  In particular, a disk multiplier and its
adjoint transport to the literal upper-half-plane boundary Hardy space, with the expected adjoint
eigenvalue on every Cauchy feature.
-/

open Complex MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

/-- The exact disk-to-line Hardy unitary as a continuous linear map. -/
def hardyDiskLineCayleyCLM : HardyDisk →L[ℂ] UpperHardyL2 :=
  hardyDiskLineCayleyUnitary.toLinearIsometry.toContinuousLinearMap

/-- The inverse exact Hardy Cayley unitary as a continuous linear map. -/
def hardyLineDiskCayleyCLM : UpperHardyL2 →L[ℂ] HardyDisk :=
  hardyDiskLineCayleyUnitary.symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem norm_hardyDiskLineCayleyCLM (f : HardyDisk) :
    ‖hardyDiskLineCayleyCLM f‖ = ‖f‖ :=
  hardyDiskLineCayleyUnitary.norm_map f

@[simp] theorem norm_hardyLineDiskCayleyCLM (f : UpperHardyL2) :
    ‖hardyLineDiskCayleyCLM f‖ = ‖f‖ :=
  hardyDiskLineCayleyUnitary.symm.norm_map f

@[simp] theorem hardyLineDiskCayleyCLM_apply_hardyDiskLineCayleyCLM
    (f : HardyDisk) :
    hardyLineDiskCayleyCLM (hardyDiskLineCayleyCLM f) = f := by
  exact hardyDiskLineCayleyUnitary.symm_apply_apply f

@[simp] theorem hardyDiskLineCayleyCLM_apply_hardyLineDiskCayleyCLM
    (f : UpperHardyL2) :
    hardyDiskLineCayleyCLM (hardyLineDiskCayleyCLM f) = f := by
  exact hardyDiskLineCayleyUnitary.apply_symm_apply f

theorem inner_hardyDiskLineCayleyCLM (f g : HardyDisk) :
    inner ℂ (hardyDiskLineCayleyCLM f) (hardyDiskLineCayleyCLM g) =
      inner ℂ f g :=
  hardyDiskLineCayleyUnitary.inner_map_map f g

theorem inner_hardyLineDiskCayleyCLM (f g : UpperHardyL2) :
    inner ℂ (hardyLineDiskCayleyCLM f) (hardyLineDiskCayleyCLM g) =
      inner ℂ f g :=
  hardyDiskLineCayleyUnitary.symm.inner_map_map f g

/-- Unitary conjugation of a bounded disk-Hardy operator to literal upper Hardy boundary space. -/
def cayleyTransportHardyOperator (T : HardyDisk →L[ℂ] HardyDisk) :
    UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  hardyDiskLineCayleyCLM.comp (T.comp hardyLineDiskCayleyCLM)

@[simp] theorem cayleyTransportHardyOperator_apply
    (T : HardyDisk →L[ℂ] HardyDisk) (f : HardyDisk) :
    cayleyTransportHardyOperator T (hardyDiskLineCayleyCLM f) =
      hardyDiskLineCayleyCLM (T f) := by
  simp [cayleyTransportHardyOperator]

theorem norm_cayleyTransportHardyOperator
    (T : HardyDisk →L[ℂ] HardyDisk) :
    ‖cayleyTransportHardyOperator T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun f => ?_
    rw [cayleyTransportHardyOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    calc
      ‖hardyDiskLineCayleyCLM (T (hardyLineDiskCayleyCLM f))‖ =
          ‖T (hardyLineDiskCayleyCLM f)‖ :=
        hardyDiskLineCayleyUnitary.norm_map _
      _ ≤ ‖T‖ * ‖hardyLineDiskCayleyCLM f‖ := T.le_opNorm _
      _ = ‖T‖ * ‖f‖ := by rw [norm_hardyLineDiskCayleyCLM]
  · refine ContinuousLinearMap.opNorm_le_bound T
      (norm_nonneg (cayleyTransportHardyOperator T)) fun f => ?_
    have hbound := (cayleyTransportHardyOperator T).le_opNorm
      (hardyDiskLineCayleyCLM f)
    rw [cayleyTransportHardyOperator_apply,
      norm_hardyDiskLineCayleyCLM, norm_hardyDiskLineCayleyCLM] at hbound
    exact hbound

/-- A bounded disk multiplier transported to literal upper Hardy boundary space. -/
def cayleyTransportHardyMultiplier (F : DiskMultiplier) :
    UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  cayleyTransportHardyOperator (hardyMul F)

@[simp] theorem cayleyTransportHardyMultiplier_apply
    (F : DiskMultiplier) (f : HardyDisk) :
    cayleyTransportHardyMultiplier F (hardyDiskLineCayleyCLM f) =
      hardyDiskLineCayleyCLM (hardyMul F f) :=
  cayleyTransportHardyOperator_apply (hardyMul F) f

/-- Transport of the multiplier adjoint.  This explicit conjugate is useful independently of
adjoint functoriality because its action on every total Cauchy feature is pointwise. -/
def cayleyTransportHardyMultiplierAdjoint (F : DiskMultiplier) :
    UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  cayleyTransportHardyOperator (hardyMul F).adjoint

theorem cayleyTransportHardyMultiplierAdjoint_apply_feature
    (F : DiskMultiplier) (w : UpperHalfPlanePoint) :
    cayleyTransportHardyMultiplierAdjoint F (cayleyLineHardyFeature w) =
      (starRingEnd ℂ) (F.fn (upperToDiskCayley w.1)) •
        cayleyLineHardyFeature w := by
  rw [← hardyDiskLineCayleyUnitary_apply_feature w]
  change cayleyTransportHardyOperator (hardyMul F).adjoint
      (hardyDiskLineCayleyCLM (cayleyDiskHardyFeature w)) =
    (starRingEnd ℂ) (F.fn (upperToDiskCayley w.1)) •
      hardyDiskLineCayleyCLM (cayleyDiskHardyFeature w)
  rw [cayleyTransportHardyOperator_apply]
  rw [cayleyDiskHardyFeature, adjoint_hardyMul_hardyKernel]
  exact map_smul hardyDiskLineCayleyCLM _ _

/-- Unitary conjugation commutes with the Hilbert-space adjoint. -/
theorem adjoint_cayleyTransportHardyOperator
    (T : HardyDisk →L[ℂ] HardyDisk) :
    (cayleyTransportHardyOperator T).adjoint =
      cayleyTransportHardyOperator T.adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ
      f (hardyDiskLineCayleyCLM (T (hardyLineDiskCayleyCLM g))) =
    inner ℂ (hardyDiskLineCayleyCLM
      (T.adjoint (hardyLineDiskCayleyCLM f))) g
  rw [← hardyDiskLineCayleyCLM_apply_hardyLineDiskCayleyCLM f,
    ← hardyDiskLineCayleyCLM_apply_hardyLineDiskCayleyCLM g,
    inner_hardyDiskLineCayleyCLM, inner_hardyDiskLineCayleyCLM]
  simp only [hardyLineDiskCayleyCLM_apply_hardyDiskLineCayleyCLM]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem adjoint_cayleyTransportHardyMultiplier (F : DiskMultiplier) :
    (cayleyTransportHardyMultiplier F).adjoint =
      cayleyTransportHardyMultiplierAdjoint F :=
  adjoint_cayleyTransportHardyOperator (hardyMul F)

theorem adjoint_cayleyTransportHardyMultiplier_apply_feature
    (F : DiskMultiplier) (w : UpperHalfPlanePoint) :
    (cayleyTransportHardyMultiplier F).adjoint (cayleyLineHardyFeature w) =
      (starRingEnd ℂ) (F.fn (upperToDiskCayley w.1)) •
        cayleyLineHardyFeature w := by
  rw [adjoint_cayleyTransportHardyMultiplier]
  exact cayleyTransportHardyMultiplierAdjoint_apply_feature F w

/-! ## Exact comparison with concrete half-plane Blaschke multiplication -/

/-- Cauchy evaluation is multiplicative under one concrete upper-half-plane inner factor. -/
theorem upperHardyCauchyEval_upperHardyInnerBlaschke
    (p z : UpperHalfPlanePoint) (f : UpperHardyL2) :
    upperHardyCauchyEval z.1 z.2
        (upperHardyInnerBlaschke p.1 p.2 f) =
      upperHalfPlaneBlaschkeFactor p.1 z.1 *
        upperHardyCauchyEval z.1 z.2 f := by
  rw [upperHardyCauchyEval_apply, upperHardyCauchyEval_apply]
  have hpne : p.1.im ≠ 0 := ne_of_gt p.2
  have hzne : z.1.im ≠ 0 := ne_of_gt z.2
  have hcp : ((starRingEnd ℂ) p.1).im < 0 := by simpa using p.2
  have hcpz : (starRingEnd ℂ) p.1 - z.1 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [p.2, z.2]
  have hint1 := RHTower.integrable_lp_div_sub (ne_of_lt hcp)
    ((f : UpperHardyL2) : RealLineL2)
  have hint2 := RHTower.integrable_lp_div_sub hzne
    ((f : UpperHardyL2) : RealLineL2)
  have hae : (fun x : ℝ =>
      ((upperHardyInnerBlaschke p.1 p.2 f : UpperHardyL2) : RealLineL2) x /
        (((x : ℝ) : ℂ) - z.1)) =ᵐ[volume]
      fun x : ℝ =>
        (((starRingEnd ℂ) p.1 - p.1) /
            ((starRingEnd ℂ) p.1 - z.1)) *
              (((f : UpperHardyL2) : RealLineL2) x /
                (((x : ℝ) : ℂ) - (starRingEnd ℂ) p.1)) +
          ((z.1 - p.1) / (z.1 - (starRingEnd ℂ) p.1)) *
              (((f : UpperHardyL2) : RealLineL2) x /
                (((x : ℝ) : ℂ) - z.1)) := by
    filter_upwards [RHTower.coeFn_blaschkeMulInv p.1
      ((f : UpperHardyL2) : RealLineL2)] with x hx
    rw [show ((upperHardyInnerBlaschke p.1 p.2 f : UpperHardyL2) :
        RealLineL2) x =
      RHTower.blaschkeMulInv p.1 ((f : UpperHardyL2) : RealLineL2) x from rfl,
      hx, mul_comm (RHTower.blaschkeSymbolInv p.1 x), mul_div_assoc,
      RHTower.blaschkeInv_partialFraction hpne hzne hcpz x]
    ring
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    RHTower.integral_cauchyTransform_eq_zero f.property hcp,
    mul_zero, zero_add]
  rfl

/-- Every Cauchy feature is an adjoint eigenvector of concrete half-plane inner multiplication. -/
theorem adjoint_upperHardyInnerBlaschke_apply_feature
    (p z : UpperHalfPlanePoint) :
    (upperHardyInnerBlaschke p.1 p.2).adjoint
        (lowerCauchyFeatureAt z.1 z.2) =
      (starRingEnd ℂ) (upperHalfPlaneBlaschkeFactor p.1 z.1) •
        lowerCauchyFeatureAt z.1 z.2 := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left,
    _root_.inner_smul_left (lowerCauchyFeatureAt z.1 z.2) f
      ((starRingEnd ℂ) (upperHalfPlaneBlaschkeFactor p.1 z.1)),
    Complex.conj_conj]
  change upperHardyCauchyEval z.1 z.2
      (upperHardyInnerBlaschke p.1 p.2 f) =
    upperHalfPlaneBlaschkeFactor p.1 z.1 *
      upperHardyCauchyEval z.1 z.2 f
  exact upperHardyCauchyEval_upperHardyInnerBlaschke p z f

theorem adjoint_upperHardyInnerBlaschke_apply_cayleyLineHardyFeature
    (p z : UpperHalfPlanePoint) :
    (upperHardyInnerBlaschke p.1 p.2).adjoint
        (cayleyLineHardyFeature z) =
      (starRingEnd ℂ) (upperHalfPlaneBlaschkeFactor p.1 z.1) •
        cayleyLineHardyFeature z := by
  simp only [cayleyLineHardyFeature, map_smul,
    adjoint_upperHardyInnerBlaschke_apply_feature, smul_smul]
  rw [mul_comm]

/-- Exact one-factor Cayley intertwining.  The transported phase-normalized disk factor is the
concrete upper-half-plane boundary multiplier, with precisely the normalized Cayley unit. -/
def cayleyNormalizedBlaschkeMultiplier (p : UpperHalfPlanePoint) : DiskMultiplier :=
  normalizedBlaschkeMultiplier (upperToDiskCayley p.1) (by
    simpa only [upperToDiskCayley] using
      GaloisForLFunctions.cayley_upperHalfPlane_to_disk p.1 p.2)

theorem cayleyTransport_normalizedBlaschkeMultiplier_eq
    (p : UpperHalfPlanePoint) :
    cayleyTransportHardyMultiplier
        (cayleyNormalizedBlaschkeMultiplier p) =
      normalizedCayleyBlaschkeUnit p.1 •
        upperHardyInnerBlaschke p.1 p.2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply sub_eq_zero.mp
  let d : UpperHardyL2 :=
    cayleyTransportHardyMultiplier
        (cayleyNormalizedBlaschkeMultiplier p) f -
      normalizedCayleyBlaschkeUnit p.1 • upperHardyInnerBlaschke p.1 p.2 f
  have htotal := topologicalClosure_span_cayleyLineHardyFeature_eq_top
  rw [RHTower.topologicalClosure_span_eq_top_iff] at htotal
  apply htotal d
  intro s hs
  rcases hs with ⟨z, rfl⟩
  have heval : inner ℂ (cayleyLineHardyFeature z) d = 0 := by
    dsimp only [d]
    rw [inner_sub_right,
      _root_.inner_smul_right (cayleyLineHardyFeature z)
        (upperHardyInnerBlaschke p.1 p.2 f)
        (normalizedCayleyBlaschkeUnit p.1)]
    have htransport := ContinuousLinearMap.adjoint_inner_left
      (cayleyTransportHardyMultiplier
        (cayleyNormalizedBlaschkeMultiplier p))
      f (cayleyLineHardyFeature z)
    rw [adjoint_cayleyTransportHardyMultiplier_apply_feature,
      _root_.inner_smul_left (cayleyLineHardyFeature z) f
        ((starRingEnd ℂ) ((cayleyNormalizedBlaschkeMultiplier p).fn
          (upperToDiskCayley z.1))), Complex.conj_conj] at htransport
    have hconcrete := ContinuousLinearMap.adjoint_inner_left
      (upperHardyInnerBlaschke p.1 p.2) f (cayleyLineHardyFeature z)
    rw [adjoint_upperHardyInnerBlaschke_apply_cayleyLineHardyFeature,
      _root_.inner_smul_left (cayleyLineHardyFeature z) f
        ((starRingEnd ℂ) (upperHalfPlaneBlaschkeFactor p.1 z.1)),
      Complex.conj_conj] at hconcrete
    rw [← htransport, ← hconcrete]
    change normalizedBlaschkeFactor (upperToDiskCayley p.1)
        (upperToDiskCayley z.1) *
          inner ℂ (cayleyLineHardyFeature z) f -
      normalizedCayleyBlaschkeUnit p.1 *
        (upperHalfPlaneBlaschkeFactor p.1 z.1 *
          inner ℂ (cayleyLineHardyFeature z) f) = 0
    rw [normalizedBlaschkeFactor_upperToDiskCayley p.2 z.2]
    ring
  have hreverse : inner ℂ d (cayleyLineHardyFeature z) = 0 := by
    have hstar := congrArg (starRingEnd ℂ) heval
    rw [map_zero] at hstar
    exact (inner_conj_symm d (cayleyLineHardyFeature z)).symm.trans hstar
  exact hreverse

end GaloisForLFunctions.HTGeometry
