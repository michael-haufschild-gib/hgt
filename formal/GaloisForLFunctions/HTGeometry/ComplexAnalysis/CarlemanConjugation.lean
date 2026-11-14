import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CompensatedSlices

/-!
# Monomial conjugation of planar Carleman weights

On the punctured plane, division by `z^m` commutes with `∂̄` and shifts every radial norm
weight by exactly `m`. No derivative term proportional to `m` appears. These are the exact
conjugation identities used to move a large integral weight into a holomorphic multiplier;
they do not assert a weighted integral inequality.
-/

open MeasureTheory Set

namespace HTGeometry

/-- Division by a holomorphic monomial commutes with `∂̄` away from its zero. -/
theorem dzbar_div_pow {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : z ≠ 0) (m : ℕ) :
    dzbar (fun w => f w / w ^ m) z = dzbar f z / z ^ m := by
  have hh : DifferentiableAt ℂ (fun w : ℂ => (w ^ m)⁻¹) z :=
    (differentiableAt_id.pow m).inv (pow_ne_zero _ hz)
  have he : (fun w => f w / w ^ m) = fun w => (w ^ m)⁻¹ * f w := by
    funext w
    ring
  rw [he, dzbar_holomorphic_mul hh hf]
  ring

/-- The modulus of the holomorphic multiplier produces the precise radial weight shift. -/
theorem weightedNorm_div_pow (m : ℕ) (a : ℝ) (u z : ℂ) (hz : z ≠ 0) :
    ‖z‖ ^ a * ‖u / z ^ m‖ = ‖z‖ ^ (a - m) * ‖u‖ := by
  rw [norm_div, norm_pow, Real.rpow_sub (norm_pos_iff.mpr hz), Real.rpow_natCast]
  ring

/-- The same shift applies to the antiholomorphic derivative, without a degree-dependent term. -/
theorem weightedNorm_dzbar_div_pow {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : z ≠ 0) (m : ℕ) (a : ℝ) :
    ‖z‖ ^ a * ‖dzbar (fun w => f w / w ^ m) z‖ =
      ‖z‖ ^ (a - m) * ‖dzbar f z‖ := by
  rw [dzbar_div_pow hf hz, weightedNorm_div_pow m a (dzbar f z) z hz]

/-- Exact weighted moment identity on the punctured plane, for every real moment exponent. -/
theorem integral_weightedNorm_div_pow (m : ℕ) (a p : ℝ) (f : ℂ → ℂ) :
    (∫ z in ({0}ᶜ : Set ℂ), (‖z‖ ^ a * ‖f z / z ^ m‖) ^ p) =
      ∫ z in ({0}ᶜ : Set ℂ), (‖z‖ ^ (a - m) * ‖f z‖) ^ p := by
  apply setIntegral_congr_fun (measurableSet_singleton (0 : ℂ)).compl
  intro z hz
  dsimp only
  rw [weightedNorm_div_pow m a (f z) z
    (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)]

end HTGeometry
