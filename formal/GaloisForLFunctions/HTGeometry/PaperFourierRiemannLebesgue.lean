import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Fourier.Dirichlet
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! # Riemann–Lebesgue in the paper's literal phase normalization

These limits retain the exact half-integer frequencies in the Dirichlet sine
identity. Applications separately pay integrability before splitting integrals.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Period

theorem phase_eq_fourierChar (u x : ℝ) : phase u x = (Real.fourierChar (x*u) : ℂ) := by
  rw [phase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem tendsto_phase_integral_cocompact (f : ℝ → ℂ) :
    Tendsto (fun w : ℝ => ∫ x, f x * phase (-w) x) (cocompact ℝ) (𝓝 0) := by
  convert Real.tendsto_integral_exp_smul_cocompact f using 1
  funext w
  apply integral_congr_ae
  filter_upwards [] with x
  rw [phase_eq_fourierChar, mul_neg, Circle.smul_def, smul_eq_mul]
  exact mul_comm _ _

private theorem tendsto_half_frequency :
    Tendsto (fun N : ℕ => (N : ℝ) + 1/2) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem tendsto_integral_phase_half_pos (f : ℝ → ℂ) :
    Tendsto (fun N : ℕ => ∫ x, f x * phase ((N : ℝ) + 1/2) x) atTop (𝓝 0) := by
  have h := ((tendsto_phase_integral_cocompact f).mono_left atBot_le_cocompact).comp
    (tendsto_neg_atTop_atBot.comp tendsto_half_frequency)
  simpa only [Function.comp_def, neg_neg] using h

theorem tendsto_integral_phase_half_neg (f : ℝ → ℂ) :
    Tendsto (fun N : ℕ => ∫ x, f x * phase (-((N : ℝ) + 1/2)) x) atTop (𝓝 0) :=
  ((tendsto_phase_integral_cocompact f).mono_left atTop_le_cocompact).comp tendsto_half_frequency

/-- The exact sine occurring in the original symmetric Dirichlet kernel. -/
theorem dirichlet_sine_eq_phase_pair (N : ℕ) (x : ℝ) :
    (Real.sin (ang N x + Real.pi*x) : ℂ) =
      (phase ((N : ℝ) + 1/2) x - phase (-((N : ℝ) + 1/2)) x) / (2*Complex.I) := by
  have hp : ang ((N : ℝ) + 1/2) x = ang N x + Real.pi*x := by unfold ang; ring
  have hn : ang (-((N : ℝ) + 1/2)) x = -(ang N x + Real.pi*x) := by unfold ang; ring
  rw [phase_trig, phase_trig, hp, hn, Real.sin_neg, Real.cos_neg]
  push_cast
  field_simp
  ring

end GaloisForLFunctions.HTGeometry.FourierLLogL.Period
