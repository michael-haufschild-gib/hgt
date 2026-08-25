import GaloisForLFunctions.HTGeometry.SzegoOuterCyclic
import GaloisForLFunctions.HTGeometry.OneSidedFeatureGramIsometry
import GaloisForLFunctions.HTGeometry.HardyShiftCommutant

/-!
# Inner--outer factorization of bounded disk multipliers

The canonical Szegő outer factor has the same boundary modulus as the original multiplier and
dense Hardy-multiplier range.  Equality of boundary moduli therefore identifies the two
multiplication operators on that dense range by an isometry.  Its continuous extension commutes
with the unilateral shift, hence the Hardy commutant theorem supplies the inner factor.
-/

open Complex MeasureTheory Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hardy multiplication norms depend only on the a.e. boundary modulus of the multiplier. -/
theorem norm_hardyMul_eq_of_ae_norm_boundary_eq
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (f : HardyDisk) :
    ‖hardyMul phi f‖ = ‖hardyMul psi f‖ := by
  let b : Lp ℂ 2 circleLebesgue := hardyDiskBoundary f
  have hpoint : ∀ᵐ z ∂circleLebesgue,
      ‖((diskMultiplierBoundaryMul phi b : Lp ℂ 2 circleLebesgue) :
          Circle → ℂ) z‖ ^ 2 =
        ‖((diskMultiplierBoundaryMul psi b : Lp ℂ 2 circleLebesgue) :
          Circle → ℂ) z‖ ^ 2 := by
    filter_upwards [diskMultiplierBoundaryMul_coeFn phi b,
      diskMultiplierBoundaryMul_coeFn psi b, hmod] with z hphi hpsi hz
    rw [hphi, hpsi, norm_mul, norm_mul, hz]
  have hsq :
      ‖diskMultiplierBoundaryMul phi b‖ ^ 2 =
        ‖diskMultiplierBoundaryMul psi b‖ ^ 2 := by
    rw [lpTwo_norm_sq_eq_integral, lpTwo_norm_sq_eq_integral]
    exact integral_congr_ae hpoint
  have hphiNorm : ‖hardyMul phi f‖ = ‖diskMultiplierBoundaryMul phi b‖ := by
    rw [← LinearIsometry.norm_map hardyDiskBoundary (hardyMul phi f),
      ← diskMultiplierBoundaryMul_apply]
  have hpsiNorm : ‖hardyMul psi f‖ = ‖diskMultiplierBoundaryMul psi b‖ := by
    rw [← LinearIsometry.norm_map hardyDiskBoundary (hardyMul psi f),
      ← diskMultiplierBoundaryMul_apply]
  rw [hphiNorm, hpsiNorm]
  nlinarith [norm_nonneg (diskMultiplierBoundaryMul phi b),
    norm_nonneg (diskMultiplierBoundaryMul psi b)]

/-- The canonical outer factor and the original multiplier induce equal Hardy multiplication
norms. -/
theorem norm_hardyMul_outerFactor_eq
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (f : HardyDisk) :
    ‖hardyMul (diskMultiplierOuterFactor phi hphi) f‖ =
      ‖hardyMul phi f‖ := by
  apply norm_hardyMul_eq_of_ae_norm_boundary_eq
  filter_upwards [ae_norm_sq_diskMultiplierOuterFactor_boundary phi hphi,
    diskMultiplierBoundarySafe_ae phi hphi] with z hsq hsafe
  rw [hsafe] at hsq
  nlinarith [norm_nonneg
      (diskMultiplierBoundaryFun (diskMultiplierOuterFactor phi hphi) z),
    norm_nonneg (diskMultiplierBoundaryFun phi z)]

/-- Equal norm pullbacks give equal Gram kernels for the original and outer multiplication
operators. -/
theorem inner_hardyMul_outerFactor_eq
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (f g : HardyDisk) :
    inner ℂ (hardyMul (diskMultiplierOuterFactor phi hphi) f)
        (hardyMul (diskMultiplierOuterFactor phi hphi) g) =
      inner ℂ (hardyMul phi f) (hardyMul phi g) := by
  have hplus :
      ‖hardyMul (diskMultiplierOuterFactor phi hphi) f +
          hardyMul (diskMultiplierOuterFactor phi hphi) g‖ =
        ‖hardyMul phi f + hardyMul phi g‖ := by
    simpa only [map_add] using
      norm_hardyMul_outerFactor_eq phi hphi (f + g)
  have hminus :
      ‖hardyMul (diskMultiplierOuterFactor phi hphi) f -
          hardyMul (diskMultiplierOuterFactor phi hphi) g‖ =
        ‖hardyMul phi f - hardyMul phi g‖ := by
    simpa only [map_sub] using
      norm_hardyMul_outerFactor_eq phi hphi (f - g)
  have hIminus :
      ‖hardyMul (diskMultiplierOuterFactor phi hphi) f -
          (RCLike.I : ℂ) • hardyMul (diskMultiplierOuterFactor phi hphi) g‖ =
        ‖hardyMul phi f - (RCLike.I : ℂ) • hardyMul phi g‖ := by
    simpa only [map_sub, map_smul] using
      norm_hardyMul_outerFactor_eq phi hphi (f - (RCLike.I : ℂ) • g)
  have hIplus :
      ‖hardyMul (diskMultiplierOuterFactor phi hphi) f +
          (RCLike.I : ℂ) • hardyMul (diskMultiplierOuterFactor phi hphi) g‖ =
        ‖hardyMul phi f + (RCLike.I : ℂ) • hardyMul phi g‖ := by
    simpa only [map_add, map_smul] using
      norm_hardyMul_outerFactor_eq phi hphi (f + (RCLike.I : ℂ) • g)
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  rw [hplus, hminus, hIminus, hIplus]

/-- Feature synthesis over the full Hardy domain is dense when the multiplier itself has dense
range. -/
theorem dense_featureSynthesis_hardyMul_outerFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    Dense ((LinearMap.range (featureSynthesis
      (fun f : HardyDisk => hardyMul (diskMultiplierOuterFactor phi hphi) f)) :
        Submodule ℂ HardyDisk) : Set HardyDisk) := by
  have hdense : DenseRange
      (hardyMul (diskMultiplierOuterFactor phi hphi) : HardyDisk → HardyDisk) :=
    (isOuterDiskMultiplier_iff_denseRange _).mp
      (isOuterDiskMultiplier_diskMultiplierOuterFactor phi hphi)
  apply hdense.mono
  rintro _ ⟨f, rfl⟩
  exact ⟨Finsupp.single f 1, by simp⟩

/-- Canonical Hardy-space isometry carrying the outer multiplier range to the original
multiplier range. -/
noncomputable def diskMultiplierOuterComparisonIsometry
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    HardyDisk →ₗᵢ[ℂ] HardyDisk :=
  denseSourceFeatureGramIsometry
    (fun f : HardyDisk => hardyMul (diskMultiplierOuterFactor phi hphi) f)
    (fun f : HardyDisk => hardyMul phi f)
    (inner_hardyMul_outerFactor_eq phi hphi)
    (dense_featureSynthesis_hardyMul_outerFactor phi hphi)

/-- The comparison isometry has its defining action on the full outer multiplier range. -/
theorem diskMultiplierOuterComparisonIsometry_apply_outer
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (f : HardyDisk) :
    diskMultiplierOuterComparisonIsometry phi hphi
        (hardyMul (diskMultiplierOuterFactor phi hphi) f) =
      hardyMul phi f := by
  exact denseSourceFeatureGramIsometry_apply
    (fun f : HardyDisk => hardyMul (diskMultiplierOuterFactor phi hphi) f)
    (fun f : HardyDisk => hardyMul phi f)
    (inner_hardyMul_outerFactor_eq phi hphi)
    (dense_featureSynthesis_hardyMul_outerFactor phi hphi) f

/-- The dense-range comparison isometry commutes with the unilateral shift. -/
theorem diskMultiplierOuterComparisonIsometry_commutes_shift
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (x : HardyDisk) :
    diskMultiplierOuterComparisonIsometry phi hphi
        (hardyMul diskShift x) =
      hardyMul diskShift (diskMultiplierOuterComparisonIsometry phi hphi x) := by
  let outer := diskMultiplierOuterFactor phi hphi
  let T := diskMultiplierOuterComparisonIsometry phi hphi
  have hdense : DenseRange (hardyMul outer : HardyDisk → HardyDisk) :=
    (isOuterDiskMultiplier_iff_denseRange outer).mp
      (isOuterDiskMultiplier_diskMultiplierOuterFactor phi hphi)
  have heq :
      (fun y : HardyDisk => T (hardyMul diskShift y)) =
        fun y : HardyDisk => hardyMul diskShift (T y) := by
    apply hdense.equalizer
    · exact T.continuous.comp (hardyMul diskShift).continuous
    · exact (hardyMul diskShift).continuous.comp T.continuous
    · funext f
      change T (hardyMul diskShift (hardyMul outer f)) =
        hardyMul diskShift (T (hardyMul outer f))
      calc
        T (hardyMul diskShift (hardyMul outer f)) =
            T (hardyMul outer (hardyMul diskShift f)) := by
              rw [hardyMul_comm]
        _ = hardyMul phi (hardyMul diskShift f) :=
          diskMultiplierOuterComparisonIsometry_apply_outer phi hphi _
        _ = hardyMul diskShift (hardyMul phi f) := by
          rw [hardyMul_comm]
        _ = hardyMul diskShift (T (hardyMul outer f)) := by
          rw [diskMultiplierOuterComparisonIsometry_apply_outer phi hphi f]
  exact congrFun heq x

/-- The comparison isometry, regarded as a bounded Hardy operator. -/
noncomputable def diskMultiplierOuterComparisonOperator
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    HardyDisk →L[ℂ] HardyDisk :=
  (diskMultiplierOuterComparisonIsometry phi hphi).toContinuousLinearMap

theorem norm_diskMultiplierOuterComparisonOperator
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    ‖diskMultiplierOuterComparisonOperator phi hphi‖ = 1 := by
  let T := diskMultiplierOuterComparisonIsometry phi hphi
  have hupper : ‖T.toContinuousLinearMap‖ ≤ 1 := by
    apply T.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro x
    change ‖T x‖ ≤ 1 * ‖x‖
    rw [T.norm_map, one_mul]
  have hlower : 1 ≤ ‖T.toContinuousLinearMap‖ := by
    have h := T.toContinuousLinearMap.le_opNorm hardyOne
    change ‖T hardyOne‖ ≤ ‖T.toContinuousLinearMap‖ * ‖hardyOne‖ at h
    rw [T.norm_map, norm_hardyOne_eq_one, mul_one] at h
    exact h
  change ‖T.toContinuousLinearMap‖ = 1
  exact le_antisymm hupper hlower

/-- Inner factor supplied by the scalar Hardy-shift commutant theorem. -/
noncomputable def diskMultiplierInnerFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    DiskMultiplier :=
  diskMultiplierOfShiftCommutant
    (diskMultiplierOuterComparisonOperator phi hphi)
    (diskMultiplierOuterComparisonIsometry_commutes_shift phi hphi)

theorem diskMultiplierInnerFactor_bd
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    (diskMultiplierInnerFactor phi hphi).bd = 1 := by
  exact norm_diskMultiplierOuterComparisonOperator phi hphi

/-- Multiplication by the inner factor is exactly the comparison isometry. -/
theorem hardyMul_diskMultiplierInnerFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    hardyMul (diskMultiplierInnerFactor phi hphi) =
      diskMultiplierOuterComparisonOperator phi hphi := by
  exact hardyMul_diskMultiplierOfShiftCommutant
    (diskMultiplierOuterComparisonOperator phi hphi)
    (diskMultiplierOuterComparisonIsometry_commutes_shift phi hphi)

/-- The canonical inner factor acts isometrically on all of Hardy space. -/
theorem hardyMultiplierIsometry_diskMultiplierInnerFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    HardyMultiplierIsometry (diskMultiplierInnerFactor phi hphi) := by
  intro f
  rw [hardyMul_diskMultiplierInnerFactor]
  exact LinearIsometry.norm_map
    (diskMultiplierOuterComparisonIsometry phi hphi) f

/-- The inner factor has unimodular boundary values almost everywhere. -/
theorem ae_norm_diskMultiplierInnerFactor_boundary_eq_one
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun (diskMultiplierInnerFactor phi hphi) z‖ = 1 :=
  ae_norm_diskMultiplierBoundaryFun_eq_one
    (diskMultiplierInnerFactor phi hphi)
    (diskMultiplierInnerFactor_bd phi hphi)
    (hardyMultiplierIsometry_diskMultiplierInnerFactor phi hphi)

/-- Exact Hardy-vector inner--outer factorization. -/
theorem hardyOf_innerFactor_mul_outerFactor
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    hardyOf ((diskMultiplierInnerFactor phi hphi).mul
      (diskMultiplierOuterFactor phi hphi)) = hardyOf phi := by
  change hardyMul ((diskMultiplierInnerFactor phi hphi).mul
      (diskMultiplierOuterFactor phi hphi)) hardyOne =
    hardyMul phi hardyOne
  rw [← hardyMul_mul, hardyMul_diskMultiplierInnerFactor]
  exact diskMultiplierOuterComparisonIsometry_apply_outer phi hphi hardyOne

/-- Exact analytic inner--outer product identity throughout the open disk. -/
theorem diskMultiplierInnerFactor_mul_outerFactor_fn
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (diskMultiplierInnerFactor phi hphi).fn z *
        (diskMultiplierOuterFactor phi hphi).fn z = phi.fn z := by
  have hz' : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have h := congrArg (fun f : HardyDisk => hardyFun f z)
    (hardyOf_innerFactor_mul_outerFactor phi hphi)
  rw [hardyFun_hardyOf _ hz', hardyFun_hardyOf phi hz'] at h
  exact h

/-- Exact real-line boundary factorization, independent of representative choices. -/
theorem diskMultiplierLineBoundary_innerFactor_mul_outerFactor_ae
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    (fun x => diskMultiplierLineBoundary (diskMultiplierInnerFactor phi hphi) x *
      diskMultiplierLineBoundary (diskMultiplierOuterFactor phi hphi) x) =ᵐ[volume]
        diskMultiplierLineBoundary phi := by
  have hmul := diskMultiplierLineBoundary_mul_ae
    (diskMultiplierInnerFactor phi hphi)
    (diskMultiplierOuterFactor phi hphi)
  have hcongr :
      diskMultiplierLineBoundary ((diskMultiplierInnerFactor phi hphi).mul
        (diskMultiplierOuterFactor phi hphi)) =ᵐ[volume]
          diskMultiplierLineBoundary phi := by
    apply diskMultiplierLineBoundary_congr_ae
    intro z hz
    exact diskMultiplierInnerFactor_mul_outerFactor_fn phi hphi z hz
  exact hmul.symm.trans hcongr

end

end GaloisForLFunctions.HTGeometry
