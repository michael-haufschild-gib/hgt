import GaloisForLFunctions.RHTower.ThetaCuspRatioCriticalBarrierGlobal
import GaloisForLFunctions.RHTower.DeBruijnLaguerreEvolution

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology


def criticalRate (x : ℝ) : ℝ :=
  (k x/u x)*HTGeometry.ThetaCriticalBarrier.A ((k x)⁻¹) (u x^2) (boundaryRatio x)
def criticalWeight (x : ℝ) : ℝ := (k x/u x)*t x

theorem criticalSpeed_split (x : ℝ) :
    criticalErrorSpeed x=criticalRate x*criticalError x+criticalWeight x*criticalBoundaryForce x := by
  unfold criticalErrorSpeed
  rw [HTGeometry.ThetaCriticalBarrier.G_split,← criticalError_eq]
  unfold criticalRate criticalWeight criticalBoundaryForce t
  ring

private theorem criticalRate_differentiable {x : ℝ} (hx : 0<x) :
    DifferentiableAt ℝ criticalRate x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hdK := (dk hx.le).differentiableAt
  have hdU := (du hx.le).differentiableAt
  have hdQ := (dBoundaryRatio hx).differentiableAt
  unfold criticalRate HTGeometry.ThetaCriticalBarrier.A HTGeometry.ThetaCriticalBarrier.b
  fun_prop

private theorem criticalWeight_differentiable {x : ℝ} (hx : 0<x) :
    DifferentiableAt ℝ criticalWeight x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  exact ((dk hx.le).differentiableAt.div (du hx.le).differentiableAt hu).mul
    (dt hx.le).differentiableAt

theorem criticalError_pos {x : ℝ} (hx : 0<x) : 0<criticalError x := by
  have hn := criticalError_nonneg hx
  rcases hn.eq_or_lt with he | he
  · have hz : criticalError x=0 := he.symm
    have hm : IsLocalMin criticalError x := by
      change ∀ᶠ y in 𝓝 x, criticalError x≤criticalError y
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [hz]
      exact criticalError_nonneg hy
    have hdz : criticalErrorSpeed x=0 := hm.hasDerivAt_eq_zero (dCriticalError hx)
    have hw : 0<criticalWeight x := by
      have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
      have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
      exact mul_pos (div_pos hk hu) (t_pos hx.le)
    have hg : criticalBoundaryForce x=0 := by
      have hb := criticalErrorSpeed_boundary hx hz
      change criticalErrorSpeed x=criticalWeight x*criticalBoundaryForce x at hb
      rw [hdz] at hb
      exact (mul_eq_zero.mp hb.symm).resolve_left hw.ne'
    have hd := ((criticalRate_differentiable hx).hasDerivAt.mul (dCriticalError hx)).add
      ((criticalWeight_differentiable hx).hasDerivAt.mul (dCriticalForce hx))
    have hds : HasDerivAt criticalErrorSpeed (criticalWeight x*criticalForceSpeed x) x := by
      convert hd using 1 <;> first | rfl | skip
      · funext y
        exact criticalSpeed_split y
      · simp [hz,hdz,hg]
    have heq : deriv criticalError =ᶠ[𝓝 x] criticalErrorSpeed := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact (dCriticalError hy).deriv
    have hdd := hds.congr_of_eventuallyEq heq
    have hneg : deriv (deriv criticalError) x<0 := by
      rw [hdd.deriv]
      exact mul_neg_of_pos_of_neg hw (criticalForceSpeed_neg hx hz.le hg)
    have hnonneg := RHTower.DeBruijn.deriv_deriv_nonneg_of_isLocalMin hm
      (dCriticalError hx).continuousAt
    exact False.elim ((not_lt_of_ge hnonneg) hneg)
  · exact he

/-- A strict global source constraint at the critical third-slope boundary. -/
theorem boundaryRatio_gt_critical_barrier {x : ℝ} (hx : 0<x) :
    1/12-7/(72*k x)<boundaryRatio x := by
  have he := criticalError_pos hx
  rw [criticalError_eq] at he
  unfold HTGeometry.ThetaCriticalBarrier.b at he
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hb : 7*(k x)⁻¹/72=7/(72*k x) := by field_simp [hk]
  rw [hb] at he
  linarith only [he]

theorem expandingMode_critical_upper {x : ℝ} (hx : 0<x) :
    kineticGap x-12*k x*(1-3*J x/u x)<(7/6)*k x*t x := by
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have ht := t_pos hx.le
  have hi : (7/6)*k x*t x-(kineticGap x-12*k x*(1-3*J x/u x))=
      12*(k x)^2*t x*criticalError x := by
    unfold kineticGap criticalError shiftedBoundaryRatio boundaryRatio
    field_simp [hk.ne',hu.ne',ht.ne']
    ring
  have hp : 0<12*(k x)^2*t x*criticalError x := by
    have he := criticalError_pos hx
    positivity
  rw [← hi] at hp
  linarith only [hp]


end
end RHTower.ThetaCuspModularRatio
