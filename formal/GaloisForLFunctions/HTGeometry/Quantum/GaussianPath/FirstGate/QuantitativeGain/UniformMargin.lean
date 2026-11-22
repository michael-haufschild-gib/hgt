import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.QuantitativeGain.EndpointProjection

/-! # A quantitative gain from an endpoint variation -/
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Discarding a component of norm r from a unit vector changes the real
overlap with an infinitesimal rotation of norm at most two by at most 4r. -/
theorem variation_restriction (U K : E →L[ℂ] E) (hU : ∀ v, ‖U v‖=‖v‖) (hK : ‖K‖≤2)
    (v p : E) (hv : ‖v‖=1) (hp : ‖p‖≤1) :
    (⟪U p,K p⟫_ℂ).re-4*‖v-p‖ ≤ (⟪U v,K v⟫_ℂ).re := by
  have he : ⟪U v,K v⟫_ℂ-⟪U p,K p⟫_ℂ = ⟪U (v-p),K v⟫_ℂ+⟪U p,K (v-p)⟫_ℂ := by
    rw [U.map_sub,K.map_sub,inner_sub_left,inner_sub_right]
    abel
  have hm (x y : E) : |(⟪U x,K y⟫_ℂ).re| ≤ ‖x‖*(2*‖y‖) := by
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_inner_le_norm _ _).trans
    rw [hU]
    exact mul_le_mul_of_nonneg_left ((K.le_opNorm y).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _)))
      (norm_nonneg _)
  have h₁ := (abs_le.mp (hm (v-p) v)).1
  rw [hv,mul_one] at h₁
  have h₂ := (abs_le.mp ((hm p (v-p)).trans (mul_le_mul_of_nonneg_right hp (by positivity)))).1
  rw [one_mul] at h₂
  have h := congrArg Complex.re he
  simp only [Complex.sub_re,Complex.add_re] at h
  linarith only [h,h₁,h₂]

/-- A positive overlap slope b survives leakage into spectator levels with
real-part margin γ. The same angle works for all vectors in the unit sphere. -/
theorem uniform_contact_margin {γ b r : ℝ} (hγ : 0≤γ) (hγ' : γ≤2) :
    let t := γ*b/64
    t*b/2 ≤ γ*r^2+t*(b-8*r)-2*t^2 := by
  intro t
  have hsq := mul_nonneg hγ (sq_nonneg (r-b/16))
  have hsmall := mul_nonneg (sub_nonneg.mpr hγ') (mul_nonneg hγ (sq_nonneg b))
  dsimp only [t]
  nlinarith only [hsq,hsmall,mul_nonneg hγ (sq_nonneg b)]

#print axioms uniform_contact_margin
end
end GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
