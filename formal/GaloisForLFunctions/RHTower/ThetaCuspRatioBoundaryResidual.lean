import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundarySelection
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # First-order trajectory selection at the critical third-slope boundary. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

theorem drift_square_tendsto : Tendsto (fun x => u x^2) atTop (𝓝 (9:ℝ)) := by
  have hc : Tendsto (fun _ : ℝ => (9:ℝ)) atTop (𝓝 9) := tendsto_const_nhds
  convert hc.sub t_tendsto_zero using 1
  · funext x
    dsimp [t]
    ring
  · ring

theorem k_mul_t_tendsto_zero : Tendsto (fun x => k x*t x) atTop (𝓝 0) := by
  have hh : Tendsto (fun x => (361/25:ℝ)*(k x)⁻¹) atTop (𝓝 0) := by
    simpa using inverse_k_tendsto_zero.const_mul (361/25:ℝ)
  apply squeeze_zero' ?_ ?_ hh
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hk : 0<k x := lt_trans (by norm_num) (k_gt hx)
    exact mul_nonneg hk.le (t_pos hx).le
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hk : 0<k x := lt_trans (by norm_num) (k_gt hx)
    have he := mul_le_mul_of_nonneg_right (kineticGap_lt hx).le (inv_nonneg.mpr hk.le)
    have hi : k x^2*t x*(k x)⁻¹=k x*t x := by field_simp [hk.ne']
    rwa [hi] at he

def inverseKVelocity (x : ℝ) : ℝ := -2*(k x)⁻¹*(1+(k x)⁻¹/3)*J x

theorem dInverseK {x : ℝ} (hx : 0≤x) :
    HasDerivAt (fun y => (k y)⁻¹) (inverseKVelocity x) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert (dk hx).inv hk using 1 <;> first | rfl | skip
  unfold inverseKVelocity
  field_simp [hk]

theorem inverseKVelocity_tendsto_zero : Tendsto inverseKVelocity atTop (𝓝 0) := by
  have hJ : IsBoundedUnder (·≤·) atTop (norm ∘ J) := by
    refine ⟨1,?_⟩
    change ∀ᶠ x in atTop, ‖J x‖≤1
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simpa [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (J_nonneg hx)] using (J_lt_one hx).le
  have hh := inverse_k_tendsto_zero
  have he : Tendsto (fun x => -2*(k x)⁻¹*(1+(k x)⁻¹/3)) atTop (𝓝 0) := by
    simpa using (hh.const_mul (-2:ℝ)).mul (tendsto_const_nhds.add (hh.div_const 3))
  change Tendsto (fun x => -2*(k x)⁻¹*(1+(k x)⁻¹/3)*J x) atTop (𝓝 0)
  simpa only [Pi.smul_apply,smul_eq_mul,Pi.mul_def] using
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded he hJ

theorem boundaryError_scaled_tendsto :
    Tendsto (fun x => k x*boundaryError x) atTop (𝓝 (7/2:ℝ)) := by
  have hh := inverse_k_tendsto_zero
  have hq := boundaryRatio_tendsto
  have hU := drift_square_tendsto.mul hq
  have hT := k_mul_t_tendsto_zero
  have h3 : Tendsto (fun _ : ℝ => (3:ℝ)) atTop (𝓝 3) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he := (((((h3.add (hh.const_mul (4/3:ℝ))).sub
    ((hT.mul hq).const_mul 5)).add (hU.const_mul (2/3:ℝ))).sub
    ((hh.mul hU).const_mul (2/9:ℝ))).add
    ((((h1.add (hh.div_const 3)).mul hT).mul
      (hU.mul hq)).const_mul (2/3:ℝ)))
  have heq : (fun x => k x*boundaryError x) =ᶠ[atTop]
      (fun x => 3+(4/3)*(k x)⁻¹-5*(k x*t x*boundaryRatio x)+
        (2/3)*(u x^2*boundaryRatio x)-(2/9)*((k x)⁻¹*(u x^2*boundaryRatio x))+
        (2/3)*((1+(k x)⁻¹/3)*(k x*t x)*(u x^2*boundaryRatio x*boundaryRatio x))) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
    unfold boundaryError
    field_simp [hk]
  apply Tendsto.congr' heq.symm
  convert he using 1 <;> norm_num

def boundaryResidual (a x : ℝ) : ℝ :=
  36*a+k x*boundaryError x-a*u x*inverseKVelocity x

theorem boundaryResidual_tendsto (a : ℝ) :
    Tendsto (boundaryResidual a) atTop (𝓝 (36*a+7/2)) := by
  have hu : IsBoundedUnder (·≤·) atTop (norm ∘ u) := by
    refine ⟨3,?_⟩
    change ∀ᶠ x in atTop, ‖u x‖≤3
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simpa [Function.comp_apply,Real.norm_eq_abs,
      abs_of_nonneg (thetaCuspModularMassDrift_nonneg hx)] using
      (thetaCuspModularMassDrift_lt_three hx).le
  have hz : Tendsto (fun x => inverseKVelocity x*u x) atTop (𝓝 0) := by
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.mul_def] using
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded inverseKVelocity_tendsto_zero hu
  have hc : Tendsto (fun _ : ℝ => 36*a) atTop (𝓝 (36*a)) := tendsto_const_nhds
  convert (hc.add boundaryError_scaled_tendsto).sub (hz.const_mul a) using 1
  · funext x
    unfold boundaryResidual
    ring
  · ring

end
end RHTower.ThetaCuspModularRatio
