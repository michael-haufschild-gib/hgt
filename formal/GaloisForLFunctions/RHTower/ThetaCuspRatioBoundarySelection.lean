import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryDynamics
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryEscape

/-! # Complete-source selection of the critical third-slope boundary direction. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

/-- Identification with the ratio of the two compactified source coordinates. -/
theorem boundaryRatio_compact {x : ℝ} (hx : 0<x) :
    k x*(1-3*J x/u x)/(k x^2*t x)=boundaryRatio x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have ht : t x≠0 := (t_pos hx.le).ne'
  unfold boundaryRatio
  field_simp [hu,hk,ht] <;> ring

theorem boundaryRatio_bound {x : ℝ} (hx : 1≤x) :
    boundaryRatio x≤3/(2*u 1^2) := by
  have hu1 : 0<u 1 := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (by norm_num))
  have hux : u 1≤u x := u_mono (show (0:ℝ)≤1 by norm_num) (show 0≤x by linarith) hx
  calc
    boundaryRatio x≤3/(2*u x^2) := (boundaryRatio_lt (by linarith)).le
    _ ≤ 3/(2*u 1^2) := by gcongr

theorem boundaryError_tendsto_zero : Tendsto boundaryError atTop (𝓝 0) := by
  let B : ℝ := 3/(2*u 1^2)
  let U : ℝ → ℝ := fun x => u x^2*boundaryRatio x
  have hq : IsBoundedUnder (·≤·) atTop (norm ∘ boundaryRatio) := by
    refine ⟨B,?_⟩
    change ∀ᶠ x in atTop, ‖boundaryRatio x‖≤B
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg
      (boundaryRatio_nonneg (show 0<x by linarith))] using boundaryRatio_bound hx
  have hUb : ∀ᶠ x in atTop, ‖U x‖≤3/2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (by linarith))
    have he := (lt_div_iff₀ (show 0<2*u x^2 by positivity)).mp
      (boundaryRatio_lt (show 0<x by linarith))
    have hq0 := boundaryRatio_nonneg (show 0<x by linarith)
    have hU0 : 0≤U x := by dsimp [U]; positivity
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hU0]
    dsimp [U]
    nlinarith only [he]
  have hU : IsBoundedUnder (·≤·) atTop (norm ∘ U) := ⟨3/2,hUb⟩
  have hUq : IsBoundedUnder (·≤·) atTop (norm ∘ (fun x => U x*boundaryRatio x)) := by
    refine ⟨(3/2)*B,?_⟩
    change ∀ᶠ x in atTop, ‖U x*boundaryRatio x‖≤(3/2)*B
    filter_upwards [hUb,eventually_ge_atTop (1:ℝ)] with x hxU hx
    have hq0 := boundaryRatio_nonneg (show 0<x by linarith)
    have hqB := boundaryRatio_bound hx
    have hU0 : 0≤U x := by dsimp [U]; positivity
    have hbU : U x≤3/2 := by simpa [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hU0] using hxU
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hU0 hq0)]
    exact mul_le_mul hbU hqB hq0 (by norm_num)
  have hm {a f : ℝ → ℝ} (ha : Tendsto a atTop (𝓝 0))
      (hf : IsBoundedUnder (·≤·) atTop (norm ∘ f)) :
      Tendsto (fun x => a x*f x) atTop (𝓝 0) := by
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.mul_def] using
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded ha hf
  have hh := inverse_k_tendsto_zero
  have hh2 : Tendsto (fun x => ((k x)⁻¹)^2) atTop (𝓝 0) := by simpa using hh.pow 2
  have hTq := hm t_tendsto_zero hq
  have hhU := hm hh hU
  have hh2U := hm hh2 hU
  have hTUq := hm t_tendsto_zero hUq
  have hlast : Tendsto (fun x => (1+(k x)⁻¹/3)*(t x*(U x*boundaryRatio x))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.add (hh.div_const 3)).mul hTUq
  have he := (((((hh.const_mul 3).add (hh2.const_mul (4/3:ℝ))).sub
    (hTq.const_mul 5)).add (hhU.const_mul (2/3:ℝ))).sub
    (hh2U.const_mul (2/9:ℝ))).add (hlast.const_mul (2/3:ℝ))
  convert he using 1
  · funext x
    dsimp [boundaryError,U]
    simp only [div_eq_mul_inv,inv_pow,mul_inv_rev]
    ring
  · norm_num

/-- The actual complete modular orbit selects the critical compactified direction. -/
theorem boundaryRatio_tendsto : Tendsto boundaryRatio atTop (𝓝 (1/12:ℝ)) := by
  apply HTGeometry.BoundedUnstableSelection.tendsto_equilibrium
    boundaryRatio (fun x => (k x/u x)*(36*(boundaryRatio x-1/12)+boundaryError x))
    (fun x => k x/u x) boundaryError 1 0 (3/(2*u 1^2)) (1/12) 36 (1/3)
    (by norm_num) (by norm_num)
  · intro x hx
    exact dBoundaryRatio (by linarith)
  · intro x hx
    exact ⟨boundaryRatio_nonneg (by linarith),boundaryRatio_bound hx⟩
  · intro x hx
    have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (by linarith))
    apply (le_div_iff₀ hu).mpr
    have hu3 := thetaCuspModularMassDrift_lt_three (show 0≤x by linarith)
    have hk := k_gt_fiveFourths (show 0≤x by linarith)
    linarith
  · intro x hx
    rfl
  · exact boundaryError_tendsto_zero

end
end RHTower.ThetaCuspModularRatio
