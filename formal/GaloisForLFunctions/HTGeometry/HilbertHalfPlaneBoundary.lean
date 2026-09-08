import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift
import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.HilbertL2FourierNaturality

/-! One Hilbert-valued inverse Fourier boundary for a holomorphic Cauchy-bounded map. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Filter Topology FourierTransform
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quantitative data to be derived from the original forcing and inverse, before causal inversion. -/
structure CauchyBoundedHilbertMap where
  value : ℂ → H
  shift : ℝ
  shift_pos : 0 < shift
  bound : ℝ
  holo : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ value w
  norm_le : ∀ w : ℂ, 0 < w.re → ‖value w‖ ≤ bound*‖(w+(shift : ℂ))⁻¹‖

variable {H}
namespace CauchyBoundedHilbertMap
variable (F : CauchyBoundedHilbertMap H)

omit [CompleteSpace H] in
private theorem shifted_ne_zero (w : ℂ) (hw : 0 < w.re) : w+(F.shift : ℂ) ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hr
  linarith [F.shift_pos]

omit [CompleteSpace H] in
/-- Every continuous observation has Hardy bounds derived from the common vector estimate. -/
theorem probe_hardy (ℓ : H →L[ℂ] ℂ) :
    IsHalfPlaneHardy (fun w => ℓ (F.value w)) ((‖ℓ‖*F.bound)^2*(1/(2*F.shift))) := by
  have hi := isHalfPlaneHardy_inv_shift (c := (F.shift : ℂ)) (by simpa using F.shift_pos)
  have hd : DifferentiableOn ℂ (fun w : ℂ => (w+F.shift)*ℓ (F.value w))
      {w : ℂ | 0 < w.re} := by
    intro w hw
    exact ((differentiableAt_id.add_const _).mul
      (ℓ.differentiableAt.comp w (F.holo w hw))).differentiableWithinAt
  have hb : ∀ w : ℂ, 0 < w.re → ‖(w+F.shift)*ℓ (F.value w)‖ ≤ ‖ℓ‖*F.bound := by
    intro w hw
    have hn : ‖w+(F.shift : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (F.shifted_ne_zero w hw)
    calc
      _ = ‖w+(F.shift : ℂ)‖*‖ℓ (F.value w)‖ := norm_mul _ _
      _ ≤ ‖w+(F.shift : ℂ)‖*(‖ℓ‖*(F.bound*‖(w+(F.shift : ℂ))⁻¹‖)) :=
        mul_le_mul_of_nonneg_left ((ℓ.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (F.norm_le w hw) (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by rw [norm_inv]; field_simp
  apply (isHalfPlaneHardy_mul_of_bounded hi hd hb).congr
  intro w hw
  rw [← mul_assoc,inv_mul_cancel₀ (F.shifted_ne_zero w hw),one_mul]

omit [CompleteSpace H] in
theorem line_memLp (σ : ℝ) (hσ : 0 < σ) :
    MemLp (fun ξ : ℝ => F.value (rayLine σ ξ)) 2 volume := by
  have hi := isHalfPlaneHardy_inv_shift (c := (F.shift : ℂ)) (by simpa using F.shift_pos)
  have hd : DifferentiableOn ℂ F.value {w : ℂ | 0 < w.re} :=
    fun w hw => (F.holo w hw).differentiableWithinAt
  have hc : Continuous (fun ξ : ℝ => F.value (rayLine σ ξ)) :=
    hd.continuousOn.comp_continuous (by unfold rayLine; fun_prop) (fun ξ => by simpa using hσ)
  apply MemLp.mono' ((hi.memLp σ hσ).norm.const_mul F.bound) hc.aestronglyMeasurable
  exact Eventually.of_forall (fun ξ => F.norm_le _ (by simpa using hσ))

def lineVector (σ : ℝ) (hσ : 0 < σ) : Lp H 2 (volume : Measure ℝ) :=
  (F.line_memLp σ hσ).toLp _

def linePreimage : Lp H 2 (volume : Measure ℝ) := 𝓕⁻ (F.lineVector 1 one_pos)

/-- Every scalar inverse is the observation of the same actual Hilbert-valued inverse. -/
theorem linePreimage_probe (ℓ : H →L[ℂ] ℂ) :
    ℓ.compLp F.linePreimage = hardyPreimage (fun w => ℓ (F.value w)) 1
      ((F.probe_hardy ℓ).memLp 1 one_pos) := by
  unfold linePreimage hardyPreimage
  rw [compLp_fourierInv]
  congr 1

theorem linePreimage_probe_ae (ℓ : H →L[ℂ] ℂ) :
    (fun t => ℓ (F.linePreimage t)) =ᵐ[volume]
      (hardyPreimage (fun w => ℓ (F.value w)) 1 ((F.probe_hardy ℓ).memLp 1 one_pos) : ℝ → ℂ) := by
  have he := ℓ.coeFn_compLp F.linePreimage
  rw [F.linePreimage_probe ℓ] at he
  exact Filter.EventuallyEq.symm he

end CauchyBoundedHilbertMap
end
end GaloisForLFunctions.HTGeometry
