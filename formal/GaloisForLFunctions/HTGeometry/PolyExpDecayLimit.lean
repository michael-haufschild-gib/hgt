import GaloisForLFunctions.HTGeometry.GammaScaleExponentialBound

/-!
# Polynomial growth against exponential decay

A function eventually dominated by `C·t^N·e^{−δt}` with `δ > 0` tends to zero.  This is what lets an
exponentially small Gamma product beat the algebraic-logarithmic growth of the coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The scaled polynomial–exponential limit. -/
theorem tendsto_pow_mul_exp_neg_scaled (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => t ^ N * Real.exp (-(δ * t))) atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hinner : Tendsto (fun t : ℝ => δ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hcomp := hbase.comp hinner
  have hscale := hcomp.const_mul ((δ ^ N)⁻¹)
  rw [mul_zero] at hscale
  refine hscale.congr fun t => ?_
  rw [Function.comp_apply, mul_pow]
  field_simp

/-- A function eventually dominated by a polynomial times an exponential decay tends to zero. -/
theorem tendsto_zero_of_eventually_norm_le_polyExp {α : Type*} [NormedAddCommGroup α]
    {f : ℝ → α} {C δ : ℝ} {N : ℕ} (hδ : 0 < δ)
    (h : ∀ᶠ t : ℝ in atTop, ‖f t‖ ≤ C * t ^ N * Real.exp (-(δ * t))) :
    Tendsto f atTop (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hmaj : Tendsto (fun t : ℝ => C * (t ^ N * Real.exp (-(δ * t)))) atTop (nhds 0) := by
    have := (tendsto_pow_mul_exp_neg_scaled N hδ).const_mul C
    rwa [mul_zero] at this
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hmaj
  filter_upwards [h] with t ht
  calc ‖f t‖ ≤ C * t ^ N * Real.exp (-(δ * t)) := ht
    _ = C * (t ^ N * Real.exp (-(δ * t))) := by ring

end

end GaloisForLFunctions.HTGeometry
