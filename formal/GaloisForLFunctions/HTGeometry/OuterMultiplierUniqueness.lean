import GaloisForLFunctions.HTGeometry.DiskMultiplierInnerOuterFactor
import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension

/-!
# Uniqueness of bounded outer multipliers

Equal boundary moduli induce a canonical Hardy-space isometry between multiplier ranges.  When
both multipliers are outer this isometry is onto.  A surjective isometry commuting with the
unilateral shift is scalar, proving uniqueness of the outer factor up to a unimodular constant.
-/

open Complex MeasureTheory Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hardy multiplication Gram kernels depend only on the a.e. boundary modulus. -/
theorem inner_hardyMul_eq_of_ae_norm_boundary_eq
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (f g : HardyDisk) :
    inner ℂ (hardyMul phi f) (hardyMul phi g) =
      inner ℂ (hardyMul psi f) (hardyMul psi g) := by
  have hplus :
      ‖hardyMul phi f + hardyMul phi g‖ =
        ‖hardyMul psi f + hardyMul psi g‖ := by
    simpa only [map_add] using
      norm_hardyMul_eq_of_ae_norm_boundary_eq phi psi hmod (f + g)
  have hminus :
      ‖hardyMul phi f - hardyMul phi g‖ =
        ‖hardyMul psi f - hardyMul psi g‖ := by
    simpa only [map_sub] using
      norm_hardyMul_eq_of_ae_norm_boundary_eq phi psi hmod (f - g)
  have hIminus :
      ‖hardyMul phi f - (RCLike.I : ℂ) • hardyMul phi g‖ =
        ‖hardyMul psi f - (RCLike.I : ℂ) • hardyMul psi g‖ := by
    simpa only [map_sub, map_smul] using
      norm_hardyMul_eq_of_ae_norm_boundary_eq phi psi hmod
        (f - (RCLike.I : ℂ) • g)
  have hIplus :
      ‖hardyMul phi f + (RCLike.I : ℂ) • hardyMul phi g‖ =
        ‖hardyMul psi f + (RCLike.I : ℂ) • hardyMul psi g‖ := by
    simpa only [map_add, map_smul] using
      norm_hardyMul_eq_of_ae_norm_boundary_eq phi psi hmod
        (f + (RCLike.I : ℂ) • g)
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  rw [hplus, hminus, hIminus, hIplus]

/-- A surjective Hardy isometry commuting with the unilateral shift is multiplication by one
unimodular scalar. -/
theorem hardyShiftCommutingSurjectiveIsometry_eq_scalar
    (T : HardyDisk →ₗᵢ[ℂ] HardyDisk)
    (hcomm : ∀ x, T (hardyMul diskShift x) = hardyMul diskShift (T x))
    (hsurj : Function.Surjective T) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, T x = c • x := by
  let c : ℂ := (T hardyOne) 0
  have horth : ∀ y : HardyDisk,
      inner ℂ (hardyMul diskShift y) (T hardyOne) = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← hcomm]
    rw [T.inner_map_map]
    rw [← inner_conj_symm]
    have h0 : ‖(0 : ℂ)‖ < 1 := by norm_num
    have hk : hardyKernel h0 = hardyOne := hardyKernel_zero_eq_hardyOne
    have hzero : inner ℂ hardyOne (hardyMul diskShift x) = 0 := by
      rw [← hk, inner_hardyKernel h0,
        hardyFun_hardyMul diskShift x h0, diskShift]
      norm_num
    rw [hzero, map_zero]
  have hTone : T hardyOne = c • hardyOne := by
    apply lp.ext
    funext n
    by_cases hn : n = 0
    · subst n
      simp [c, hardyOne, lp.single_apply]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hs : hardyMul diskShift
          (lp.single 2 m (1 : ℂ) : HardyDisk) =
          (lp.single 2 (m + 1) (1 : ℂ) : HardyDisk) := by
        rw [← shift_pow_hardyOne, ← shift_pow_hardyOne]
        rw [pow_succ']
        rfl
      have hz := horth (lp.single 2 m (1 : ℂ) : HardyDisk)
      rw [hs, lp.inner_single_left] at hz
      simpa [hardyOne, lp.single_apply] using hz
  have hscalar : ∀ x, T x = c • x := by
    intro x
    apply hardyDisk_ext
    intro z hz
    have hfun := hardyFun_shiftCommutant T.toContinuousLinearMap hcomm x hz
    change hardyFun (T x) z = hardyFun (T hardyOne) z * hardyFun x z at hfun
    change hardyFun (T x) z = hardyFun (c • x) z
    calc
      hardyFun (T x) z = hardyFun (T hardyOne) z * hardyFun x z := hfun
      _ = hardyFun (c • hardyOne) z * hardyFun x z := by rw [hTone]
      _ = (c * 1) * hardyFun x z := by
        rw [hardyFun_smul c hardyOne hz, hardyFun_hardyOne hz]
      _ = c * hardyFun x z := by ring
      _ = hardyFun (c • x) z := (hardyFun_smul c x hz).symm
  refine ⟨c, ?_, hscalar⟩
  simpa [hTone, norm_smul, norm_hardyOne_eq_one] using T.norm_map hardyOne

private theorem dense_featureSynthesis_hardyMul_of_outer
    (psi : DiskMultiplier) (hpsi : IsOuterDiskMultiplier psi) :
    Dense ((LinearMap.range (featureSynthesis
      (fun f : HardyDisk => hardyMul psi f)) :
        Submodule ℂ HardyDisk) : Set HardyDisk) := by
  have hdense : DenseRange (hardyMul psi : HardyDisk → HardyDisk) :=
    (isOuterDiskMultiplier_iff_denseRange psi).mp hpsi
  apply hdense.mono
  rintro _ ⟨f, rfl⟩
  exact ⟨Finsupp.single f 1, by simp⟩

/-- Canonical isometry carrying one outer multiplier range to another multiplier range with the
same boundary modulus. -/
noncomputable def outerBoundaryComparisonIsometry
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (hpsi : IsOuterDiskMultiplier psi) :
    HardyDisk →ₗᵢ[ℂ] HardyDisk :=
  denseSourceFeatureGramIsometry
    (fun f : HardyDisk => hardyMul psi f)
    (fun f : HardyDisk => hardyMul phi f)
    (by
      intro f g
      exact (inner_hardyMul_eq_of_ae_norm_boundary_eq
        phi psi hmod f g).symm)
    (dense_featureSynthesis_hardyMul_of_outer psi hpsi)

theorem outerBoundaryComparisonIsometry_apply
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (hpsi : IsOuterDiskMultiplier psi) (f : HardyDisk) :
    outerBoundaryComparisonIsometry phi psi hmod hpsi (hardyMul psi f) =
      hardyMul phi f := by
  exact denseSourceFeatureGramIsometry_apply
    (fun f : HardyDisk => hardyMul psi f)
    (fun f : HardyDisk => hardyMul phi f)
    (by
      intro f g
      exact (inner_hardyMul_eq_of_ae_norm_boundary_eq
        phi psi hmod f g).symm)
    (dense_featureSynthesis_hardyMul_of_outer psi hpsi) f

theorem outerBoundaryComparisonIsometry_commutes_shift
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (hpsi : IsOuterDiskMultiplier psi) (x : HardyDisk) :
    outerBoundaryComparisonIsometry phi psi hmod hpsi
        (hardyMul diskShift x) =
      hardyMul diskShift
        (outerBoundaryComparisonIsometry phi psi hmod hpsi x) := by
  let T := outerBoundaryComparisonIsometry phi psi hmod hpsi
  have hdense : DenseRange (hardyMul psi : HardyDisk → HardyDisk) :=
    (isOuterDiskMultiplier_iff_denseRange psi).mp hpsi
  have heq :
      (fun y : HardyDisk => T (hardyMul diskShift y)) =
        fun y : HardyDisk => hardyMul diskShift (T y) := by
    apply hdense.equalizer
    · exact T.continuous.comp (hardyMul diskShift).continuous
    · exact (hardyMul diskShift).continuous.comp T.continuous
    · funext f
      change T (hardyMul diskShift (hardyMul psi f)) =
        hardyMul diskShift (T (hardyMul psi f))
      calc
        T (hardyMul diskShift (hardyMul psi f)) =
            T (hardyMul psi (hardyMul diskShift f)) := by rw [hardyMul_comm]
        _ = hardyMul phi (hardyMul diskShift f) :=
          outerBoundaryComparisonIsometry_apply phi psi hmod hpsi _
        _ = hardyMul diskShift (hardyMul phi f) := by rw [hardyMul_comm]
        _ = hardyMul diskShift (T (hardyMul psi f)) := by
          rw [outerBoundaryComparisonIsometry_apply phi psi hmod hpsi f]
  exact congrFun heq x

/-- When both multipliers are outer, the comparison isometry is onto. -/
theorem outerBoundaryComparisonIsometry_surjective
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (hphi : IsOuterDiskMultiplier phi)
    (hpsi : IsOuterDiskMultiplier psi) :
    Function.Surjective
      (outerBoundaryComparisonIsometry phi psi hmod hpsi) := by
  let T := outerBoundaryComparisonIsometry phi psi hmod hpsi
  have hdensePhi : DenseRange (hardyMul phi : HardyDisk → HardyDisk) :=
    (isOuterDiskMultiplier_iff_denseRange phi).mp hphi
  have hrange : Set.range (hardyMul phi : HardyDisk → HardyDisk) ⊆
      Set.range (T : HardyDisk → HardyDisk) := by
    rintro _ ⟨f, rfl⟩
    refine ⟨hardyMul psi f, ?_⟩
    exact outerBoundaryComparisonIsometry_apply phi psi hmod hpsi f
  have hdenseT : DenseRange (T : HardyDisk → HardyDisk) :=
    hdensePhi.mono hrange
  have hclosed : IsClosed (Set.range (T : HardyDisk → HardyDisk)) := by
    have h := isClosed_coe_range_of_isometry
      (T := T.toContinuousLinearMap) T.norm_map
    exact h
  intro y
  have hy : y ∈ closure (Set.range (T : HardyDisk → HardyDisk)) := by
    rw [hdenseT.closure_range]
    trivial
  rw [hclosed.closure_eq] at hy
  exact hy

/-- Two bounded outer multipliers with equal a.e. boundary moduli differ by one unimodular
constant throughout the disk. -/
theorem outerDiskMultiplier_unique_up_to_unimodular
    (phi psi : DiskMultiplier)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun phi z‖ =
        ‖diskMultiplierBoundaryFun psi z‖)
    (hphi : IsOuterDiskMultiplier phi)
    (hpsi : IsOuterDiskMultiplier psi) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1,
      phi.fn z = c * psi.fn z := by
  let T := outerBoundaryComparisonIsometry phi psi hmod hpsi
  obtain ⟨c, hc, hT⟩ := hardyShiftCommutingSurjectiveIsometry_eq_scalar T
    (outerBoundaryComparisonIsometry_commutes_shift phi psi hmod hpsi)
    (outerBoundaryComparisonIsometry_surjective phi psi hmod hphi hpsi)
  refine ⟨c, hc, ?_⟩
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have happly := outerBoundaryComparisonIsometry_apply
    phi psi hmod hpsi hardyOne
  rw [hT] at happly
  have hfun := congrArg (fun f : HardyDisk => hardyFun f z) happly
  calc
    phi.fn z = hardyFun (c • hardyMul psi hardyOne) z := by
      have hphiVal : hardyFun (hardyMul phi hardyOne) z = phi.fn z := by
        simpa [hardyOf] using hardyFun_hardyOf phi hz'
      exact hphiVal.symm.trans hfun.symm
    _ = c * hardyFun (hardyMul psi hardyOne) z :=
      hardyFun_smul c (hardyMul psi hardyOne) hz'
    _ = c * psi.fn z := by
      rw [hardyFun_hardyMul psi hardyOne hz', hardyFun_hardyOne hz', mul_one]

end

end GaloisForLFunctions.HTGeometry
