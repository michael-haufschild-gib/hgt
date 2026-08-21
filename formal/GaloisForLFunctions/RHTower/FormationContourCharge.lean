import GaloisForLFunctions.RHTower.RenormalizedFormationWorkDivisor
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount
import GaloisForLFunctions.Bottcher.ArgumentPrinciple

/-!
# The contour charge of renormalized formation work

The branch-free work form of the survival transfer is holomorphic except at the strict-right zeta
zeros, where its residue is the vanishing order.  Integrating it over a zero-avoiding circle inside
the strict right half-plane therefore counts the enclosed zeta divisor with multiplicity.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The punctured strict right half-plane. -/
def workDomain : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z ≠ 1}

theorem isOpen_workDomain : IsOpen workDomain := by
  have h1 : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  exact h1.inter h2

theorem shellResidueUnit_ne_zero_of_zeta {k : ℕ} (hk : 12 ≤ k) {z : ℂ} (hz : z ∈ workDomain)
    (hζ : riemannZeta z ≠ 0) : shellResidueUnit k z ≠ 0 := by
  obtain ⟨hre, hne1⟩ := hz
  rw [shellResidueUnit, zetaResidueUnit, Function.update_of_ne hne1]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hne1) hζ) (shellMultiplier_ne_zero hk hre)

theorem shellResidueUnit_eq_zero_iff {k : ℕ} (hk : 12 ≤ k) {z : ℂ} (hz : z ∈ workDomain) :
    shellResidueUnit k z = 0 ↔ riemannZeta z = 0 := by
  constructor
  · intro h
    by_contra hζ
    exact shellResidueUnit_ne_zero_of_zeta hk hz hζ h
  · intro h
    obtain ⟨hre, hne1⟩ := hz
    rw [shellResidueUnit, zetaResidueUnit, Function.update_of_ne hne1, h]
    ring

/-- **Contour charge** (DWP.12).  The branch-free work form integrates over a zero-avoiding circle
to `2πi` times the enclosed zeta divisor. -/
theorem circleIntegral_charge_survivalTransfer {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r)
    {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    (hsub : Metric.closedBall c R ⊆ workDomain)
    (hsphere : ∀ ζ ∈ Metric.sphere c t, riemannZeta ζ ≠ 0) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ Metric.ball c t) ∧
      (∀ z ∈ Metric.ball c t, riemannZeta z = 0 ↔ z ∈ Z) ∧
      (∮ ζ in C(c, t), -logDeriv (survivalTransfer m r) ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) *
          ∑ ρ ∈ Z, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hR : 0 < R := lt_trans ht htR
  have htsub : Metric.closedBall c t ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall (le_of_lt htR)
  -- the denominator
  have hden : DifferentiableOn ℂ (shellResidueUnit (r * m)) workDomain := fun z hz =>
    (analyticAt_shellResidueUnit hkm hz.1).differentiableAt.differentiableWithinAt
  have hdenSphere : ∀ ζ ∈ Metric.sphere c t, shellResidueUnit (r * m) ζ ≠ 0 := by
    intro ζ hζ
    exact shellResidueUnit_ne_zero_of_zeta hkm (hsub (htsub (Metric.sphere_subset_closedBall hζ)))
      (hsphere ζ hζ)
  obtain ⟨Z, hZball, hZmem, hZint⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zeroSet_circleIntegral_logDeriv ht htR
      isOpen_workDomain hsub hden hdenSphere
  refine ⟨Z, hZball, ?_, ?_⟩
  · intro z hz
    rw [← hZmem z hz]
    exact (shellResidueUnit_eq_zero_iff hkm (hsub (htsub (Metric.ball_subset_closedBall hz)))).symm
  · -- the numerator contributes nothing
    have hnumAn : AnalyticOnNhd ℂ (fun z => shellSource m ((r : ℂ) * z)) workDomain := by
      intro z hz
      exact analyticAt_shellSource_natCast_mul hm hr hz.1
    have hnumNe : ∀ z ∈ Metric.closedBall c t, shellSource m ((r : ℂ) * z) ≠ 0 := by
      intro z hz
      exact shellSource_natCast_mul_ne_zero hm hr (hsub (htsub hz)).1
    have hnum0 : (∮ z in C(c, t), deriv (fun w => shellSource m ((r : ℂ) * w)) z /
        shellSource m ((r : ℂ) * z)) = 0 :=
      Bottcher.circleIntegral_logDeriv_eq_zero (le_of_lt ht) isOpen_workDomain
        (htsub.trans hsub) hnumAn hnumNe
    -- integrability
    have hciDen : CircleIntegrable (logDeriv (shellResidueUnit (r * m))) c t := by
      refine ContinuousOn.circleIntegrable (le_of_lt ht) fun z hz => ?_
      have hzU : z ∈ workDomain := hsub (htsub (Metric.sphere_subset_closedBall hz))
      have hA : AnalyticAt ℂ (shellResidueUnit (r * m)) z := analyticAt_shellResidueUnit hkm hzU.1
      have : ContinuousAt (logDeriv (shellResidueUnit (r * m))) z :=
        (hA.deriv.continuousAt).div hA.continuousAt (hdenSphere z hz)
      exact this.continuousWithinAt
    have hciNum : CircleIntegrable (logDeriv (fun w => shellSource m ((r : ℂ) * w))) c t := by
      refine ContinuousOn.circleIntegrable (le_of_lt ht) fun z hz => ?_
      have hzU : z ∈ workDomain := hsub (htsub (Metric.sphere_subset_closedBall hz))
      have hA : AnalyticAt ℂ (fun w => shellSource m ((r : ℂ) * w)) z :=
        analyticAt_shellSource_natCast_mul hm hr hzU.1
      have : ContinuousAt (logDeriv (fun w => shellSource m ((r : ℂ) * w))) z :=
        (hA.deriv.continuousAt).div hA.continuousAt
          (hnumNe z (Metric.sphere_subset_closedBall hz))
      exact this.continuousWithinAt
    -- pointwise splitting on the sphere
    have hsplit : ∀ z ∈ Metric.sphere c t,
        -logDeriv (survivalTransfer m r) z
          = logDeriv (shellResidueUnit (r * m)) z
            - logDeriv (fun w => shellSource m ((r : ℂ) * w)) z := by
      intro z hz
      have hzU : z ∈ workDomain := hsub (htsub (Metric.sphere_subset_closedBall hz))
      have hnd : DifferentiableAt ℂ (fun w => shellSource m ((r : ℂ) * w)) z :=
        (analyticAt_shellSource_natCast_mul hm hr hzU.1).differentiableAt
      have hdd : DifferentiableAt ℂ (shellResidueUnit (r * m)) z :=
        (analyticAt_shellResidueUnit hkm hzU.1).differentiableAt
      have hsurv : survivalTransfer m r
          = fun w => shellSource m ((r : ℂ) * w) / shellResidueUnit (r * m) w := rfl
      rw [hsurv,
        logDeriv_div z (hnumNe z (Metric.sphere_subset_closedBall hz)) (hdenSphere z hz) hnd hdd]
      ring
    rw [circleIntegral.integral_congr (le_of_lt ht) hsplit,
      circleIntegral.integral_sub hciDen hciNum]
    have hnum0' : (∮ z in C(c, t), logDeriv (fun w => shellSource m ((r : ℂ) * w)) z) = 0 := by
      rw [show (fun z => logDeriv (fun w => shellSource m ((r : ℂ) * w)) z)
        = fun z => deriv (fun w => shellSource m ((r : ℂ) * w)) z /
          shellSource m ((r : ℂ) * z) from by
        funext z
        rw [logDeriv_apply]]
      exact hnum0
    rw [hnum0', sub_zero, hZint]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    congr 1
    have hρU : ρ ∈ workDomain := hsub (htsub (Metric.ball_subset_closedBall (hZball ρ hρ)))
    rw [GaloisForLFunctions.HTGeometry.zeroMult,
      analyticOrderAt_shellResidueUnit hkm hρU.1 hρU.2]

end

end RHTower
