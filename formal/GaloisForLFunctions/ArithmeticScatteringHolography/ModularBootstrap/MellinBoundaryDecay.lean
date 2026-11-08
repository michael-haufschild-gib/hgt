import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Boundary decay of inverse Mellin transforms

Logarithmic change of variables turns the normalized inverse Mellin transform into a
Fourier transform. Riemann–Lebesgue gives its vanishing at the positive origin.
-/

open Complex Real Set Filter MeasureTheory Topology
open scoped FourierTransform
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Normalized inverse Mellin transforms vanish at the logarithmic boundary. -/
theorem tendsto_normalized_mellinInv_zero (σ : ℝ) (F : ℂ → ℂ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ (σ : ℂ) * mellinInv σ F y)
      (𝓝[>] 0) (𝓝 0) := by
  let g : ℝ → ℂ := fun t => F (σ + 2 * Real.pi * t * I)
  have hf := Real.zero_at_infty_fourier g
  have hl : Tendsto Real.log (𝓝[>] 0) (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact Real.tendsto_log_nhdsGT_zero.mono_right le_sup_left
  apply (hf.comp hl).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 < y := hy
  rw [mellinInv_eq_fourierInv σ F hy0, smul_eq_mul,
    Real.fourierInv_eq_fourier_neg, neg_neg, ← mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy0.ne')]
  simp [g]

#print axioms tendsto_normalized_mellinInv_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
