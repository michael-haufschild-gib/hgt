import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplacePowerLimits
import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLimit

/-! Transport of the actual first endpoint subtraction through the polynomial coordinate. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Absolute admission of the subtracted source alone controls its full endpoint cutoff. -/
theorem firstEndpointMellin_cutoff_of_integrable (F : ℝ → ℂ) (w : ℂ) (hw : w+1 ≠ 0)
    (hR : IntervalIntegrable (fun x : ℝ => (x:ℂ)^w*(F x-F 0)) volume 0 1) :
    Tendsto (fun e : ℝ => (∫ x in e..1, (x:ℂ)^w*F x)+F 0*(e:ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (firstEndpointMellin (fun _ => F) 1 w)) := by
  let R : ℝ → ℂ := fun x => (x:ℂ)^w*(F x-F 0)
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioc (0:ℝ) 1 := by
    have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin, he1.filter_mono nhdsWithin_le_nhds] with e he he1
    exact ⟨he,he1.le⟩
  have hid : Tendsto (fun e : ℝ => e) (𝓝[>] (0:ℝ)) (𝓝[uIcc (0:ℝ) 1] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hevent] with e he
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact ⟨he.1.le,he.2⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hR (right_mem_uIcc : (1:ℝ) ∈ uIcc (0:ℝ) 1)
  have hlim := ((hc 0 left_mem_uIcc).tendsto.comp hid).neg
  simp only [Function.comp_apply, ← intervalIntegral.integral_symm] at hlim
  have htotal := hlim.const_add (F 0/(w+1))
  have hfp : firstEndpointMellin (fun _ => F) 1 w = F 0/(w+1)+(∫ x in (0:ℝ)..1, R x) := by
    simp only [firstEndpointMellin,firstEndpointMellinRemainder,Complex.ofReal_one,
      Complex.one_cpow,mul_one]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [hfp]
  apply htotal.congr'
  filter_upwards [hevent] with e he
  have hRc : IntervalIntegrable R volume e 1 := hR.mono_set (by
    rw [uIcc_of_le he.2,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact fun x hx => ⟨he.1.le.trans hx.1,hx.2⟩)
  have hP : IntervalIntegrable (fun x : ℝ => (x:ℂ)^w) volume e 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc he.2
    intro x hx
    exact (power_derivatives w (he.1.trans_le hx.1)).1.continuousAt.continuousWithinAt
  have hsplit : (∫ x in e..1, (x:ℂ)^w*F x) =
      (∫ x in e..1, R x)+(∫ x in e..1, (x:ℂ)^w)*F 0 := by
    calc
      _ = ∫ x in e..1, R x+(x:ℂ)^w*F 0 := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [R]
        ring
      _ = _ := by rw [intervalIntegral.integral_add hRc (hP.mul_const _),intervalIntegral.integral_mul_const]
  have hp : (∫ x in e..1, (x:ℂ)^w)=(1-(e:ℂ)^(w+1))/(w+1) := by
    rw [integral_cpow (Or.inr ⟨by intro h; apply hw; rw [h]; ring,
      by rw [uIcc_of_le he.2]; exact fun h => (not_le_of_gt he.1) h.1⟩)]
    simp only [Complex.ofReal_one,Complex.one_cpow]
  rw [hsplit,hp]
  ring

/-- A differentiable coefficient difference annihilates the transported lower-order counterterm. -/
theorem fundamentalMoment_cpow_mul_sub_tendsto {G : ℝ → ℂ} {g w : ℂ}
    (hG : HasDerivAt G g 0) (hw : -2 < w.re) :
    Tendsto (fun x : ℝ => (x:ℂ)^(w+1)*(G x-G 0)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hs := hG.tendsto_slope_zero_right
  simp only [zero_add,Complex.real_smul,Complex.ofReal_inv] at hs
  have hp := (power_tendsto_zero (a := w+2) (by change 0 < w.re+2; linarith)).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hlim := hp.mul hs
  simp only [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hpow : (x:ℂ)^(w+2)=(x:ℂ)^(w+1)*(x:ℂ) := by
    rw [show w+2=(w+1)+1 by ring,Complex.cpow_add _ _ hx0,Complex.cpow_one]
  dsimp only [power]
  rw [hpow]
  field_simp

end
end RHTower.D4BMJointSource
