import GaloisForLFunctions.HTGeometry.SzegoOuterCyclic
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Square-integrable Smirnov boundaries are Hardy boundaries

An outer denominator admits contractive cyclic approximants converging to one.  Multiplying a
square-integrable Smirnov boundary by those approximants gives bounded analytic boundaries and
converges in `L²`; closedness of the Hardy boundary range supplies the exact Hardy vector.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A Smirnov quotient whose circle boundary is in `L²` is the boundary of an `H²` function. -/
theorem DiskSmirnovBoundary.exists_hardyDisk_of_memLp_two_circleBoundary
    (F : DiskSmirnovBoundary)
    (hF : MemLp F.circleBoundary 2 circleLebesgue) :
    ∃ f : HardyDisk,
      (⇑(hardyDiskBoundary f) : Circle → ℂ) =ᵐ[circleLebesgue]
        F.circleBoundary := by
  let D := F.denominator
  let hD : ∃ z ∈ ball (0 : ℂ) 1, D.fn z ≠ 0 := F.denominator_outer.exists_nonzero
  let O := diskMultiplierOuterFactor D hD
  let q : Lp ℂ 2 circleLebesgue := hF.toLp F.circleBoundary
  have hsafe := diskMultiplierBoundarySafe_ae D hD
  have hsq := ae_norm_sq_diskMultiplierOuterFactor_boundary D hD
  have hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun D z‖ = ‖diskMultiplierBoundaryFun O z‖ := by
    filter_upwards [hsafe, hsq] with z hzSafe hzSq
    change ‖diskMultiplierBoundaryFun D z‖ =
      ‖diskMultiplierBoundaryFun (diskMultiplierOuterFactor D hD) z‖
    rw [hzSafe] at hzSq
    nlinarith [norm_nonneg (diskMultiplierBoundaryFun D z),
      norm_nonneg (diskMultiplierBoundaryFun O z)]
  have hOouter : IsOuterDiskMultiplier O :=
    isOuterDiskMultiplier_diskMultiplierOuterFactor D hD
  obtain ⟨c, hc, hDO⟩ := outerDiskMultiplier_unique_up_to_unimodular
    D O hmod F.denominator_outer hOouter
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  let invn : ℕ → DiskMultiplier := fun n =>
    diskMultiplierOuterTruncatedInverse D hD n
  let u : ℕ → DiskMultiplier := fun n =>
    diskMultiplierOuterCyclicApprox D hD n
  let v : ℕ → DiskMultiplier := fun n =>
    (DiskMultiplier.const c⁻¹).mul (F.numerator.mul (invn n))
  have hDbd : diskMultiplierBoundaryFun D =ᵐ[circleLebesgue]
      fun z => c * diskMultiplierBoundaryFun O z := by
    have hhardy : hardyOf D = hardyOf ((DiskMultiplier.const c).mul O) := by
      apply hardyOf_congr
      intro z hz
      rw [hDO z hz]
      simp [DiskMultiplier.mul, DiskMultiplier.const]
    have hboundary := congrArg hardyDiskBoundary hhardy
    have hmul := diskMultiplierBoundaryFun_mul_ae (DiskMultiplier.const c) O
    have hconst := diskMultiplierBoundaryFun_const_ae c
    filter_upwards [hmul, hconst] with z hzMul hzConst
    change diskMultiplierBoundaryFun D z = c * diskMultiplierBoundaryFun O z
    change ((hardyDiskBoundary (hardyOf D) : Lp ℂ 2 circleLebesgue) : Circle → ℂ) z = _
    rw [hboundary]
    change diskMultiplierBoundaryFun ((DiskMultiplier.const c).mul O) z = _
    rw [hzMul, hzConst]
  have huBoundary (n : ℕ) : diskMultiplierBoundaryFun (u n) =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun O z *
        diskMultiplierBoundaryFun (invn n) z := by
    have hhardy : hardyOf (u n) = hardyOf (O.mul (invn n)) := by
      apply hardyOf_congr
      intro z hz
      rfl
    have hboundary := congrArg hardyDiskBoundary hhardy
    have hmul := diskMultiplierBoundaryFun_mul_ae O (invn n)
    filter_upwards [hmul] with z hzMul
    change diskMultiplierBoundaryFun (u n) z = _
    change ((hardyDiskBoundary (hardyOf (u n)) : Lp ℂ 2 circleLebesgue) :
      Circle → ℂ) z = _
    rw [hboundary]
    change diskMultiplierBoundaryFun (O.mul (invn n)) z = _
    rw [hzMul]
  have hvBoundary (n : ℕ) : diskMultiplierBoundaryFun (v n) =ᵐ[circleLebesgue]
      fun z => c⁻¹ *
        (diskMultiplierBoundaryFun F.numerator z *
          diskMultiplierBoundaryFun (invn n) z) := by
    have houter := diskMultiplierBoundaryFun_mul_ae
      (DiskMultiplier.const c⁻¹) (F.numerator.mul (invn n))
    have hinner := diskMultiplierBoundaryFun_mul_ae F.numerator (invn n)
    have hconst := diskMultiplierBoundaryFun_const_ae c⁻¹
    filter_upwards [houter, hinner, hconst] with z hzOuter hzInner hzConst
    change diskMultiplierBoundaryFun (v n) z = _
    rw [hzOuter, hzInner, hzConst]
  have hqCoe : (⇑q : Circle → ℂ) =ᵐ[circleLebesgue] F.circleBoundary :=
    hF.coeFn_toLp
  have hanalytic (n : ℕ) :
      diskMultiplierBoundaryMul (u n) q = hardyDiskBoundary (hardyOf (v n)) := by
    apply Lp.ext
    filter_upwards [diskMultiplierBoundaryMul_coeFn (u n) q, hqCoe,
      huBoundary n, hvBoundary n, hDbd,
      F.denominator_circle_ne_zero_ae] with z hzMul hzQ hzU hzV hzD hzDne
    change (diskMultiplierBoundaryMul (u n) q : Circle → ℂ) z =
      diskMultiplierBoundaryFun (v n) z
    rw [hzMul, hzQ, hzU, hzV]
    change (diskMultiplierBoundaryFun O z * diskMultiplierBoundaryFun (invn n) z) *
        (diskMultiplierBoundaryFun F.numerator z /
          diskMultiplierBoundaryFun D z) = _
    rw [hzD]
    have hO0 : diskMultiplierBoundaryFun O z ≠ 0 := by
      intro hzero
      apply hzDne
      rw [hzD, hzero, mul_zero]
    field_simp [hc0, hO0]
  have huT : Tendsto
      (fun n => hardyDiskBoundary (hardyOf (u n))) atTop
      (nhds (hardyDiskBoundary hardyOne)) := by
    exact (hardyDiskBoundary.continuous.tendsto hardyOne).comp
      (tendsto_hardyOf_diskMultiplierOuterCyclicApprox D hD)
  obtain ⟨ns, hns, huAE⟩ := exists_subseq_ae_tendsto huT
  have hone : (⇑(hardyDiskBoundary hardyOne) : Circle → ℂ) =ᵐ[circleLebesgue]
      fun _ => 1 := by
    rw [hardyOne, hardyDiskBoundary_single]
    filter_upwards [circleMonomialLp_coeFn_ae circleLebesgue 0] with z hz
    simpa using hz
  have huAE' : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => diskMultiplierBoundaryFun (u (ns i)) z)
        atTop (nhds 1) := by
    filter_upwards [huAE, hone] with z hz hzone
    change Tendsto (fun i => diskMultiplierBoundaryFun (u (ns i)) z)
      atTop (nhds 1)
    simpa only [diskMultiplierBoundaryFun, hzone] using hz
  have huBound : ∀ᵐ z ∂circleLebesgue, ∀ i : ℕ,
      ‖diskMultiplierBoundaryFun (u (ns i)) z‖ ≤ 1 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ae_norm_diskMultiplierBoundaryFun_le (u (ns i))] with z hz
    simpa [u, diskMultiplierOuterCyclicApprox] using hz
  let energy : ℕ → Circle → ℝ := fun i z =>
    ‖diskMultiplierBoundaryFun (u (ns i)) z * q z - q z‖ ^ 2
  have henergyMeas (i : ℕ) : AEStronglyMeasurable (energy i) circleLebesgue := by
    exact (((Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf (u (ns i))))).mul
      (Lp.aestronglyMeasurable q)).sub (Lp.aestronglyMeasurable q)).norm.pow 2
  have hboundInt : Integrable (fun z : Circle => 4 * ‖q z‖ ^ 2) circleLebesgue := by
    have hqMem : MemLp (⇑q : Circle → ℂ) 2 circleLebesgue := Lp.memLp q
    exact (hqMem.integrable_norm_pow (by norm_num)).const_mul 4
  have henergyBound (i : ℕ) : ∀ᵐ z ∂circleLebesgue,
      ‖energy i z‖ ≤ 4 * ‖q z‖ ^ 2 := by
    filter_upwards [huBound] with z hz
    dsimp [energy]
    rw [abs_of_nonneg (sq_nonneg _)]
    have htri :
        ‖diskMultiplierBoundaryFun (u (ns i)) z * q z - q z‖ ≤ 2 * ‖q z‖ := by
      calc
        _ ≤ ‖diskMultiplierBoundaryFun (u (ns i)) z * q z‖ + ‖q z‖ :=
          norm_sub_le _ _
        _ = ‖diskMultiplierBoundaryFun (u (ns i)) z‖ * ‖q z‖ + ‖q z‖ := by
          rw [norm_mul]
        _ ≤ 2 * ‖q z‖ := by nlinarith [hz i, norm_nonneg (q z)]
    nlinarith [norm_nonneg
      (diskMultiplierBoundaryFun (u (ns i)) z * q z - q z)]
  have henergyLim : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => energy i z) atTop (nhds 0) := by
    filter_upwards [huAE'] with z hz
    have hmul : Tendsto
        (fun i => diskMultiplierBoundaryFun (u (ns i)) z * q z)
        atTop (nhds (1 * q z)) := hz.mul tendsto_const_nhds
    have hsub := hmul.sub tendsto_const_nhds
    have hnorm := hsub.norm
    simpa [energy] using hnorm.pow 2
  have henergyIntegral : Tendsto
      (fun i => ∫ z, energy i z ∂circleLebesgue) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := energy) (f := fun _ : Circle => (0 : ℝ))
      (bound := fun z : Circle => 4 * ‖q z‖ ^ 2)
      henergyMeas hboundInt henergyBound henergyLim
    simpa using h
  have hLpT : Tendsto
      (fun i => diskMultiplierBoundaryMul (u (ns i)) q) atTop (nhds q) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto
        (fun i => ‖diskMultiplierBoundaryMul (u (ns i)) q - q‖ ^ 2)
        atTop (nhds 0) := by
      convert henergyIntegral using 1
      funext i
      rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (diskMultiplierBoundaryMul (u (ns i)) q) q,
        diskMultiplierBoundaryMul_coeFn (u (ns i)) q] with z hzSub hzMul
      rw [hzSub]
      simp only [Pi.sub_apply, hzMul]
      rfl
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    convert hsqrt using 1
    · funext i
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  have hclosed : IsClosed (Set.range (hardyDiskBoundary :
      HardyDisk → Lp ℂ 2 circleLebesgue)) :=
    hardyDiskBoundary.isometry.isClosedEmbedding.isClosed_range
  have hqRange : q ∈ Set.range (hardyDiskBoundary :
      HardyDisk → Lp ℂ 2 circleLebesgue) := by
    apply hclosed.mem_of_tendsto hLpT
    exact Filter.Eventually.of_forall fun i => by
      refine ⟨hardyOf (v (ns i)), ?_⟩
      exact (hanalytic (ns i)).symm
  obtain ⟨f, hf⟩ := hqRange
  refine ⟨f, ?_⟩
  filter_upwards [hqCoe] with z hz
  change (hardyDiskBoundary f : Circle → ℂ) z = F.circleBoundary z
  rw [hf]
  exact hz

end

end GaloisForLFunctions.HTGeometry
