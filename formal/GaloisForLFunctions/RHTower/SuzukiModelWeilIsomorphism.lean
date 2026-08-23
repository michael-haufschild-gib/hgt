import GaloisForLFunctions.RHTower.SuzukiWeilTauIsomorphism
import GaloisForLFunctions.RHTower.SuzukiSpectralRestriction

noncomputable section

/-!
# The model space is the Weil space

Composing the two spectral pictures — the model space is the weighted sequence space with weights
`π m_γ`, the Weil space with weights `m_γ` — gives the isomorphism of Theorem 1.1 and the constant
that separates the two normalisations: `‖F‖²_{L²(ℝ)} = π ⟨ψ_F, ψ_F⟩_W`.

The isomorphism is the source's `F ↦ ψ_F`: the spectral values of the image are exactly the
spectral values of `F`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

section

variable [hRH : Fact RiemannHypothesis]

/-- Rescaling of the spectral sequence space by `π^{-1/2}`, the constant relating the two
normalisations. -/
def suzukiTauRescale : SuzukiTauSpace ≃ₗ[ℂ] SuzukiTauSpace :=
  LinearEquiv.smulOfNeZero ℂ SuzukiTauSpace ((1 / Real.sqrt Real.pi : ℝ) : ℂ) (by
    have hpi := Real.pi_pos
    simp only [ne_eq, Complex.ofReal_eq_zero, one_div, inv_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hpi))

omit hRH in
@[simp] theorem suzukiTauRescale_apply (f : SuzukiTauSpace) (ρ : XiDivisorSupport) :
    ((suzukiTauRescale f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((1 / Real.sqrt Real.pi : ℝ) : ℂ) * (f : ∀ _ : XiDivisorSupport, ℂ) ρ := rfl

omit hRH in
theorem norm_suzukiTauRescale (f : SuzukiTauSpace) :
    ‖suzukiTauRescale f‖ = (1 / Real.sqrt Real.pi) * ‖f‖ := by
  have hpi := Real.pi_pos
  have hs : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  show ‖((1 / Real.sqrt Real.pi : ℝ) : ℂ) • f‖ = (1 / Real.sqrt Real.pi) * ‖f‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Theorem 1.1.**  The model space and the Weil space are isomorphic. -/
def suzukiModelWeilEquiv :
    ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) ≃ₗ[ℂ] SuzukiHW :=
  ((suzukiFGammaHilbertBasis hRH.out).repr.toLinearEquiv.trans suzukiTauRescale).trans
    (suzukiWeilTauEquiv.symm.toLinearEquiv)

theorem norm_sq_suzukiModelWeilEquiv
    (F : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))) :
    ‖(F : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
      = Real.pi * ‖suzukiModelWeilEquiv F‖ ^ 2 := by
  have hpi := Real.pi_pos
  have hs : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hval : ‖suzukiModelWeilEquiv F‖
      = (1 / Real.sqrt Real.pi) * ‖(F : Lp ℂ 2 (volume : Measure ℝ))‖ := by
    show ‖suzukiWeilTauEquiv.symm (suzukiTauRescale ((suzukiFGammaHilbertBasis hRH.out).repr F))‖
      = (1 / Real.sqrt Real.pi) * ‖(F : Lp ℂ 2 (volume : Measure ℝ))‖
    rw [suzukiWeilTauEquiv.symm.norm_map, norm_suzukiTauRescale,
      (suzukiFGammaHilbertBasis hRH.out).repr.norm_map]
    rfl
  rw [hval, mul_pow]
  have hsq : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt hpi)
  field_simp
  rw [hsq]

/-- **The isomorphism of Theorem 1.1 matches spectral values.**  The Weil-space image of `F` has
exactly the spectral values of `F`, so the map is the source's `F ↦ ψ_F`. -/
theorem suzukiWeilTauEquiv_suzukiModelWeilEquiv
    (F : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))))
    (ρ : XiDivisorSupport) :
    ((suzukiWeilTauEquiv (suzukiModelWeilEquiv F) : SuzukiTauSpace) :
        ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((Real.sqrt (xiSupportMult ρ : ℝ) : ℝ) : ℂ)
        * suzukiRestriction hRH.out (F : Lp ℂ 2 (volume : Measure ℝ)) ρ := by
  have hpi := Real.pi_pos
  have hs : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hrepr : ((suzukiFGammaHilbertBasis hRH.out).repr F : ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((Real.sqrt (suzukiClarkWeight ρ) : ℝ) : ℂ)
        * suzukiRestriction hRH.out (F : Lp ℂ 2 (volume : Measure ℝ)) ρ := by
    have h1 := (suzukiFGammaHilbertBasis hRH.out).repr_apply_apply F ρ
    rw [coe_suzukiFGammaHilbertBasis] at h1
    rw [h1]
    exact inner_eq_sqrt_mul_suzukiRestriction hRH.out _ ρ
  have hsplit : Real.sqrt (suzukiClarkWeight ρ)
      = Real.sqrt Real.pi * Real.sqrt (xiSupportMult ρ : ℝ) := by
    rw [suzukiClarkWeight, Real.sqrt_mul (le_of_lt hpi)]
  have hval : ((suzukiWeilTauEquiv (suzukiModelWeilEquiv F) : SuzukiTauSpace) :
      ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((1 / Real.sqrt Real.pi : ℝ) : ℂ)
        * ((suzukiFGammaHilbertBasis hRH.out).repr F : ∀ _ : XiDivisorSupport, ℂ) ρ := by
    show ((suzukiWeilTauEquiv (suzukiWeilTauEquiv.symm
        (suzukiTauRescale ((suzukiFGammaHilbertBasis hRH.out).repr F))) : SuzukiTauSpace) :
          ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((1 / Real.sqrt Real.pi : ℝ) : ℂ)
        * ((suzukiFGammaHilbertBasis hRH.out).repr F : ∀ _ : XiDivisorSupport, ℂ) ρ
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact suzukiTauRescale_apply _ ρ
  rw [hval, hrepr, hsplit]
  push_cast
  field_simp


end

end RHTower
