import GaloisForLFunctions.HTGeometry.GaussianPolynomialPhaseDefect
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Modulation escapes compact operators on continuous L²

Riemann–Lebesgue makes every fixed L² pairing vanish under high-frequency modulation.
Modulation preserves norm, so every compact operator sends these orbits to zero in norm.
The pairing argument also supplies the native aperture-restricted pole-profile theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology

/-- Every fixed L² pairing vanishes under high-frequency modulation. -/
theorem modulationMul_inner_tendsto (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun t : ℝ => inner ℂ g (modulationMul t f)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => -t) atTop (cocompact ℝ) :=
    tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact
  have h := (Real.tendsto_integral_exp_smul_cocompact
    (fun x : ℝ => inner ℂ (g x) (f x))).comp ht
  apply h.congr'
  filter_upwards with t
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_modulationMul t f] with x hx
  rw [hx]
  simp only [Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul, modulationSymbol, RCLike.inner_apply]
  have he : ((2 * Real.pi * (-(x * -t)) : ℝ) : ℂ) * I =
      ((2 * Real.pi * (t*x) : ℝ) : ℂ) * I := by congr 2; ring
  rw [he]
  ring

/-- Integer-frequency modulation is weakly null for every input vector. -/
theorem modulationMul_nat_inner_tendsto (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => inner ℂ g (modulationMul (n : ℝ) f)) atTop (𝓝 0) :=
  (modulationMul_inner_tendsto f g).comp tendsto_natCast_atTop_atTop

/-- Compact operators kill every fixed modulation orbit in norm. -/
theorem modulationMul_compact_tendsto
    (K : compactOperatorStarAlgebra (Lp ℂ 2 (volume : Measure ℝ)))
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => K.1 (modulationMul (n : ℝ) v)) atTop (𝓝 0) := by
  let C : ℝ := ‖v‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let u := ((C⁻¹ : ℝ) : ℂ) • v
  have hu : ‖u‖ ≤ 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
    rw [inv_mul_le_iff₀ hC, mul_one]
    dsimp [C]
    linarith
  have huv : (C : ℂ) • u = v := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hC.ne',
      Complex.ofReal_one, one_smul]
  have ht := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n : ℕ => modulationMul (n : ℝ) u)
    (fun n => (norm_modulationMul_eq (n : ℝ) u).le.trans hu)
    (fun z => modulationMul_nat_inner_tendsto u z)
  have hs := (tendsto_const_nhds (x := (C : ℂ))).smul ht
  simpa only [← map_smul, huv, smul_zero] using hs

end
end GaloisForLFunctions.HTGeometry
