import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePeriodRegularity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePeriodPhysicalValue
import Mathlib.Analysis.Meromorphic.Order

/-! Identification of the actual physical quotient pairing by the meromorphic identity principle. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section

/-- The original cleared quotient integral and the derived continuation agree as germs everywhere. -/
theorem clearedResidualPeriod_eventuallyEq_continuation (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) (u : ℂ) :
    clearedResidualPeriod q =ᶠ[𝓝[≠] u]
      (fun v => clearFactor v * nativePeriodContinuation q (v+1/2)) := by
  let d := fun v => clearedResidualPeriod q v - clearFactor v * nativePeriodContinuation q (v+1/2)
  have hd : MeromorphicOn d univ := by
    intro v _
    have hP : AnalyticAt ℂ clearFactor v := by unfold clearFactor; fun_prop
    have hJ : MeromorphicAt (fun w : ℂ => nativePeriodContinuation q (w+1/2)) v :=
      (nativePeriodContinuation_meromorphic q (v+1/2)).comp_analyticAt
        (g := fun w : ℂ => w+1/2) (x := v) (analyticAt_id.add analyticAt_const)
    exact ((clearedResidualPeriod_differentiable q).analyticAt v).meromorphicAt.sub
      (hP.meromorphicAt.mul hJ)
  have ha : meromorphicOrderAt d (3+I) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hr : ∀ᶠ v : ℂ in 𝓝 (3+I), 2 < (v+1/2).re :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by norm_num)
    have hi : ∀ᶠ v : ℂ in 𝓝 (3+I), v.im ≠ 0 :=
      ((show IsOpen {x : ℝ | x ≠ 0} from isOpen_ne).preimage
        Complex.continuous_im).mem_nhds (by norm_num)
    filter_upwards [hr.filter_mono nhdsWithin_le_nhds,hi.filter_mono nhdsWithin_le_nhds] with v hv hiv
    dsimp [d]
    rw [clearedResidualPeriod_eq q v hiv,nativePeriodContinuation_eq_original q hq _ hv]
    simp
  have hu : meromorphicOrderAt d u = ⊤ := by
    by_contra h
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ u) (mem_univ (3+I)) h) ha
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hu] with v hv
  exact sub_eq_zero.mp hv

private theorem physical_clearFactor_ne_zero (q : XiZeroCopy) :
    clearFactor (((q.1:ℂ)-1)/2) ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have h0 : ((q.1:ℂ)-1)/2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  have hm : 2*(((q.1:ℂ)-1)/2)-1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  have hp : 2*(((q.1:ℂ)-1)/2)+1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hi (by linarith)
  exact mul_ne_zero (mul_ne_zero h0 hm) hp

/-- The actual absolutely convergent physical quotient integral equals the full continued value. -/
theorem scalarResidualPeriod_physical_eq_continuation (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) :
    scalarResidualPeriod q (((q.1:ℂ)-1)/2) = nativePeriodContinuation q ((q.1:ℂ)/2) := by
  let u : ℂ := ((q.1:ℂ)-1)/2
  have he : u+1/2 = (q.1:ℂ)/2 := by dsimp [u]; ring
  have hJ : ContinuousAt (fun v : ℂ => nativePeriodContinuation q (v+1/2)) u := by
    have hc := (nativePeriodContinuation_physical_analytic q).continuousAt
    rw [← he] at hc
    exact hc.comp (f := fun v : ℂ => v+1/2) (by fun_prop)
  have hP : ContinuousAt clearFactor u := by unfold clearFactor; fun_prop
  have hvalue := tendsto_nhds_unique_of_eventuallyEq
    (((clearedResidualPeriod_differentiable q).continuous.continuousAt (x := u)).mono_left
      nhdsWithin_le_nhds)
    ((hP.mul hJ).mono_left nhdsWithin_le_nhds)
    (clearedResidualPeriod_eventuallyEq_continuation q hq u)
  have hi : u.im ≠ 0 := by
    dsimp [u]
    simpa using div_ne_zero (xi_divisor_support_im_ne_zero q.1) (by norm_num : (2:ℝ) ≠ 0)
  simp only [Pi.mul_apply] at hvalue
  rw [clearedResidualPeriod_eq q u hi,he] at hvalue
  exact mul_left_cancel₀ (physical_clearFactor_ne_zero q) hvalue

/-- The physical original quotient pairing retains the reflected cutoff correction. -/
theorem scalarResidualPeriod_physical_value (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re) :
    scalarResidualPeriod q (((q.1:ℂ)-1)/2) =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2+
      reflectedCompletedLambda ((q.1:ℂ)-1)*nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)) := by
  rw [scalarResidualPeriod_physical_eq_continuation q hq,nativePeriodContinuation_physical_value]

/-- Dropping the reflected correction from the actual physical pairing requires its moment to vanish. -/
theorem scalarResidualPeriod_physical_eq_diagonal_iff (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) :
    scalarResidualPeriod q (((q.1:ℂ)-1)/2) =
      (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2))/2 ↔
      nativePrincipalMomentContinuation q (-((q.1:ℂ)/2)) = 0 := by
  rw [scalarResidualPeriod_physical_eq_continuation q hq]
  exact nativePhysicalPeriod_eq_diagonal_iff q

end
end RHTower.D4BMJointSource
