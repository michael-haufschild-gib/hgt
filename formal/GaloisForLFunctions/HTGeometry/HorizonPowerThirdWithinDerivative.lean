import GaloisForLFunctions.HTGeometry.HorizonPowerThirdUniformBound

/-!
The literal source power's third radial derivative, connected to Lean's
within-derivative Taylor interface on the physical cutoff interval.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology Complex
noncomputable section
set_option autoImplicit false

private theorem literalSourceHorizonLog_contDiffAt {z : ℝ} (hz : z < 1)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n literalSourceHorizonLog z := by
  have hlin : ContDiffAt ℝ n (fun x : ℝ => 1 - x) z := by fun_prop
  have hpow : ContDiffAt ℝ n (fun y : ℝ => y ^ (1 / 2 : ℝ)) (1 - z) :=
    Real.contDiffAt_rpow_const_of_ne (n := n) (p := (1 / 2 : ℝ))
      (by linarith : 1 - z ≠ 0)
  have hroot : ContDiffAt ℝ n (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ)) z :=
    hpow.comp z hlin
  have hroot' : ContDiffAt ℝ n (fun x : ℝ => Real.sqrt (1 - x)) z := by
    apply hroot.congr_of_eventuallyEq
    filter_upwards with x
    rw [Real.sqrt_eq_rpow]
  have hheight : ContDiffAt ℝ n literalSourceHorizonHeight z := by
    change ContDiffAt ℝ n (fun x : ℝ => 1 + Real.sqrt (1 - x)) z
    exact contDiffAt_const.add hroot'
  exact hheight.log (by
    dsimp [literalSourceHorizonHeight]
    positivity)

theorem literalSourceHorizonPower_contDiffAt (α : ℂ) {z : ℝ} (hz : z < 1)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (literalSourceHorizonPower α) z := by
  have hlog : ContDiffAt ℝ n (fun x : ℝ => (literalSourceHorizonLog x : ℂ)) z := by
    have h := Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (literalSourceHorizonLog_contDiffAt hz n)
    change ContDiffAt ℝ n (Complex.ofReal ∘ literalSourceHorizonLog) z at h
    exact h
  change ContDiffAt ℝ n
    (fun x : ℝ => Complex.exp ((literalSourceHorizonLog x : ℂ) * α)) z
  exact (hlog.mul contDiffAt_const).cexp

private theorem literalSourceHorizonPower_iteratedDeriv_one_eventuallyEq
    (α : ℂ) {z : ℝ} (hz : z < 1) :
    iteratedDeriv 1 (literalSourceHorizonPower α) =ᶠ[𝓝 z]
      literalSourceHorizonPowerFirst α := by
  filter_upwards [eventually_lt_nhds hz] with x hx
  simpa only [iteratedDeriv_one] using
    (literalSourceHorizonPower_derivatives α hx).1.deriv

private theorem literalSourceHorizonPower_iteratedDeriv_two_eventuallyEq
    (α : ℂ) {z : ℝ} (hz : z < 1) :
    iteratedDeriv 2 (literalSourceHorizonPower α) =ᶠ[𝓝 z]
      literalSourceHorizonPowerSecond α := by
  filter_upwards [eventually_lt_nhds hz] with x hx
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [(literalSourceHorizonPower_iteratedDeriv_one_eventuallyEq α hx).deriv_eq]
  exact (literalSourceHorizonPower_derivatives α hx).2.deriv

theorem literalSourceHorizonPower_iteratedDeriv_one (α : ℂ) {z : ℝ} (hz : z < 1) :
    iteratedDeriv 1 (literalSourceHorizonPower α) z = literalSourceHorizonPowerFirst α z := by
  simpa only [iteratedDeriv_one] using (literalSourceHorizonPower_derivatives α hz).1.deriv

theorem literalSourceHorizonPower_iteratedDeriv_two (α : ℂ) {z : ℝ} (hz : z < 1) :
    iteratedDeriv 2 (literalSourceHorizonPower α) z = literalSourceHorizonPowerSecond α z := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [(literalSourceHorizonPower_iteratedDeriv_one_eventuallyEq α hz).deriv_eq]
  exact (literalSourceHorizonPower_derivatives α hz).2.deriv

theorem literalSourceHorizonPower_iteratedDeriv_three (α : ℂ) {z : ℝ} (hz : z < 1) :
    iteratedDeriv 3 (literalSourceHorizonPower α) z = horizonPowerThirdCore α z := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
  rw [(literalSourceHorizonPower_iteratedDeriv_two_eventuallyEq α hz).deriv_eq]
  exact (literalSourceHorizonPowerSecond_hasDerivAt α z hz).deriv

theorem literalSourceHorizonPower_iteratedDerivWithin_one (α : ℂ) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) (1 / 2)) :
    iteratedDerivWithin 1 (literalSourceHorizonPower α) (Icc 0 (1 / 2)) z =
      literalSourceHorizonPowerFirst α z := by
  have hlt : z < 1 := by linarith [hz.2]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (literalSourceHorizonPower_contDiffAt α hlt 1) hz]
  exact literalSourceHorizonPower_iteratedDeriv_one α hlt

theorem literalSourceHorizonPower_iteratedDerivWithin_two (α : ℂ) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) (1 / 2)) :
    iteratedDerivWithin 2 (literalSourceHorizonPower α) (Icc 0 (1 / 2)) z =
      literalSourceHorizonPowerSecond α z := by
  have hlt : z < 1 := by linarith [hz.2]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (literalSourceHorizonPower_contDiffAt α hlt 2) hz]
  exact literalSourceHorizonPower_iteratedDeriv_two α hlt

theorem literalSourceHorizonPower_iteratedDerivWithin_three (α : ℂ) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) (1 / 2)) :
    iteratedDerivWithin 3 (literalSourceHorizonPower α) (Icc 0 (1 / 2)) z =
      horizonPowerThirdCore α z := by
  have hlt : z < 1 := by linarith [hz.2]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (literalSourceHorizonPower_contDiffAt α hlt 3) hz]
  exact literalSourceHorizonPower_iteratedDeriv_three α hlt

theorem literalSourceHorizonPower_contDiffOn (α : ℂ) :
    ContDiffOn ℝ 3 (literalSourceHorizonPower α) (Icc (0 : ℝ) (1 / 2)) := by
  intro z hz
  exact (literalSourceHorizonPower_contDiffAt α (by linarith [hz.2]) 3).contDiffWithinAt

end
end GaloisForLFunctions.HTGeometry
