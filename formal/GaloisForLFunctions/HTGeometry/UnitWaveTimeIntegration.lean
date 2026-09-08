import GaloisForLFunctions.HTGeometry.UnitWaveDuhamelDerivative

/-! Integration by parts transfers a time derivative to the actual causal forcing. -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The cosine convolution retains the initial boundary term when the forcing is differentiated. -/
theorem unitWaveCosConvolution_eq (F F' : ℝ → FourierRealL2)
    (hF : Continuous F) (hF' : Continuous F') (hd : ∀ t, HasDerivAt F (F' t) t) (τ : ℝ) :
    (∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F σ)) =
      unitWaveSine τ (F 0)+unitWaveDuhamel F' τ := by
  have hD (σ : ℝ) : HasDerivAt (fun r => unitWaveSine (τ-r) (F r))
      (unitWaveSine (τ-σ) (F' σ)-kgCosOp (2*Real.pi*(τ-σ)) (F σ)) σ := by
    have hM (r : ℝ) : ‖(unitWaveSine (τ-r)).restrictScalars ℝ‖ ≤ (2*Real.pi)⁻¹ := by
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact unitWaveSine_norm_le _
    have hT := (unitWaveSine_hasDerivAt (τ-σ) (F σ)).scomp σ
      ((hasDerivAt_const σ τ).sub (hasDerivAt_id σ))
    have h := hasDerivAt_strong_apply hM
      (fun x => unitWaveSine_continuous_comp _ _ (continuous_const.sub continuous_id) continuous_const)
      (hd σ) hT
    convert h using 1 <;> first | rfl | simp [sub_eq_add_neg]
  have hi₁ := (unitWaveSine_continuous_comp (fun σ : ℝ => τ-σ) F'
    (continuous_const.sub continuous_id) hF').intervalIntegrable (μ := volume) 0 τ
  have hi₂ := (continuous_kgCosOp_comp (r := fun σ : ℝ => 2*Real.pi*(τ-σ))
    (continuous_const.mul (continuous_const.sub continuous_id)) hF).intervalIntegrable (μ := volume) 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hD σ) (hi₁.sub hi₂)
  rw [intervalIntegral.integral_sub hi₁ hi₂,sub_self,unitWaveSine_zero,zero_apply,
    sub_zero,zero_sub] at h
  change unitWaveDuhamel F' τ - _ = -unitWaveSine τ (F 0) at h
  have hh := congrArg (fun x => unitWaveSine τ (F 0)+x) (sub_eq_iff_eq_add.mp h)
  simpa only [← add_assoc,add_neg_cancel,zero_add] using hh.symm

/-- Zero initial forcing removes the boundary term by an established equality. -/
theorem unitWaveDuhamel_deriv_eq_of_zero (F F' : ℝ → FourierRealL2)
    (hF : Continuous F) (hF' : Continuous F') (hd : ∀ t, HasDerivAt F (F' t) t) (h₀ : F 0 = 0) :
    deriv (unitWaveDuhamel F) = unitWaveDuhamel F' := by
  funext τ
  rw [(unitWaveDuhamel_hasDerivAt F hF τ).deriv,unitWaveCosConvolution_eq F F' hF hF' hd τ,h₀,map_zero,zero_add]

/-- Time differentiability of the forcing yields a genuine second derivative in the Hilbert norm. -/
theorem unitWaveDuhamel_second_hasDerivAt (F F' : ℝ → FourierRealL2)
    (hF : Continuous F) (hF' : Continuous F') (hd : ∀ t, HasDerivAt F (F' t) t)
    (h₀ : F 0 = 0) (τ : ℝ) :
    HasDerivAt (deriv (unitWaveDuhamel F))
      (∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F' σ)) τ := by
  rw [unitWaveDuhamel_deriv_eq_of_zero F F' hF hF' hd h₀]
  exact unitWaveDuhamel_hasDerivAt F' hF' τ

end
end GaloisForLFunctions.HTGeometry
