import GaloisForLFunctions.HTGeometry.L2SpatialReflectionMultipliers
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldRegularity

/-! The sine propagator with the original unit-speed Fourier normalization restored. -/
open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

/-- Restored inverse-frequency sine kernel for the physical operator `(2*pi)^(2 : ℕ) - d_x^(2 : ℕ)`. -/
def unitWaveSine (τ : ℝ) : FourierRealL2 →L[ℂ] FourierRealL2 :=
  (((2*Real.pi)⁻¹:ℝ):ℂ) • kgSinFreqOp (2*Real.pi*τ)

theorem unitWaveSine_apply (τ : ℝ) (f : FourierRealL2) :
    unitWaveSine τ f = (((2*Real.pi)⁻¹:ℝ):ℂ) • kgSinFreqOp (2*Real.pi*τ) f := rfl

theorem unitWaveSine_zero : unitWaveSine 0 = 0 := by simp [unitWaveSine,kgSinFreqOp_zero]

theorem unitWaveSine_norm_le (τ : ℝ) : ‖unitWaveSine τ‖ ≤ (2*Real.pi)⁻¹ := by
  rw [unitWaveSine,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_kgSinFreqOp_le (E := ℝ) (2*Real.pi*τ))
    (by positivity)).trans_eq (mul_one _)

theorem unitWaveSine_apply_norm_le (τ : ℝ) (f : FourierRealL2) :
    ‖unitWaveSine τ f‖ ≤ (2*Real.pi)⁻¹*‖f‖ :=
  (unitWaveSine τ).le_of_opNorm_le (unitWaveSine_norm_le τ) f

/-- Strong continuity holds jointly in the time and the actual spatial source vector. -/
theorem unitWaveSine_continuous_comp {A : Type*} [TopologicalSpace A]
    (r : A → ℝ) (f : A → FourierRealL2) (hr : Continuous r) (hf : Continuous f) :
    Continuous (fun x => unitWaveSine (r x) (f x)) := by
  change Continuous (fun x => (((2*Real.pi)⁻¹:ℝ):ℂ) • kgSinFreqOp (2*Real.pi*r x) (f x))
  exact (continuous_const : Continuous (fun _ : A => (((2*Real.pi)⁻¹:ℝ):ℂ))).smul
    (continuous_kgSinFreqOp_comp (continuous_const.mul hr) hf)

/-- Restoring `2*pi` restores the cosine as the actual static-time derivative. -/
theorem unitWaveSine_hasDerivAt (τ : ℝ) (f : FourierRealL2) :
    HasDerivAt (fun t : ℝ => unitWaveSine t f) (kgCosOp (2*Real.pi*τ) f) τ := by
  have h := (hasDerivAt_kgSinFreqOp (2*Real.pi*τ) f).scomp τ
    ((hasDerivAt_id τ).const_mul (2*Real.pi))
  have hs := h.const_smul (((2*Real.pi)⁻¹:ℝ):ℂ)
  apply hs.congr_deriv
  simp only [mul_one]
  change ((2*Real.pi)⁻¹:ℝ) • ((2*Real.pi:ℝ) • kgCosOp (2*Real.pi*τ) f) = _
  rw [smul_smul,inv_mul_cancel₀ (by positivity : 2*Real.pi ≠ 0),one_smul]

/-- The physical normalization retains the original spatial odd subspace. -/
theorem unitWaveSine_reflection (τ : ℝ) (f : FourierRealL2) :
    unitWaveSine τ (l2Reflection f) = l2Reflection (unitWaveSine τ f) := by
  rw [unitWaveSine_apply,kgSinFreqOp_reflection,unitWaveSine_apply,map_smul]

end
end GaloisForLFunctions.HTGeometry
