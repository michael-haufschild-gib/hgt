import GaloisForLFunctions.HTGeometry.WuDoubleNullEnergy

/-!
# Optimal constants in exponential energy integration

The one- and two-direction constants underlying Wu's Lemma 2.3 are optimal
uniformly in the length of the observation region. Constant profiles suffice
to attain the limiting norm. Thus a better constant requires information
beyond a uniform bound on the original field.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open Filter Topology
noncomputable section

/-- Exact long-interval mass of the terminally normalized exponential weight. -/
theorem tendsto_mass (d : ℝ) : Tendsto (mass d) atTop (𝓝 (1 / (2 * Real.exp d))) := by
  have hlin : Tendsto (fun t : ℝ => 2 * Real.exp d * |t|) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_abs_atTop_atTop
  have he : Tendsto (fun t : ℝ => Real.exp (-(2 * Real.exp d * |t|))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  change Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * Real.exp d * |t|))) / (2 * Real.exp d)) atTop _
  simpa only [sub_zero] using (tendsto_const_nhds.sub he).div_const (2 * Real.exp d)

/-- The sharp uniform squared-energy constant, characterized without an assumed estimate. -/
theorem uniform_energy_bound_iff (d C : ℝ) :
    (∀ (f : BoundedContinuousFunction ℝ ℝ) (t : ℝ), energy d t f ≤ C * ‖f‖ ^ 2) ↔
      1 / (2 * Real.exp d) ≤ C := by
  constructor
  · intro h
    apply le_of_tendsto (tendsto_mass d)
    apply Eventually.of_forall
    intro t
    have hc := h (BoundedContinuousFunction.const ℝ (1 : ℝ)) t
    simpa [energy_const] using hc
  · intro h f t
    calc energy d t f ≤ ‖f‖ ^ 2 / (2 * Real.exp d) := energy_le d t f
      _ = (1 / (2 * Real.exp d)) * ‖f‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- Two directions have the square of the one-direction optimal energy constant. -/
theorem uniform_rectangle_energy_bound_iff (d C : ℝ) :
    (∀ (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) (u v : ℝ),
      rectangleEnergy d u v f ≤ C * ‖f‖ ^ 2) ↔
      1 / (2 * Real.exp d) ^ 2 ≤ C := by
  constructor
  · intro h
    have hm : Tendsto (fun t : ℝ => mass d t * mass d t) atTop
        (𝓝 (1 / (2 * Real.exp d) ^ 2)) := by
      convert! (tendsto_mass d).mul (tendsto_mass d) using 1
      congr 1
      ring
    apply le_of_tendsto hm
    apply Eventually.of_forall
    intro t
    have hc := h (BoundedContinuousFunction.const (ℝ × ℝ) (1 : ℝ)) t t
    simpa [rectangleEnergy_const] using hc
  · intro h f u v
    calc rectangleEnergy d u v f ≤ ‖f‖ ^ 2 / (2 * Real.exp d) ^ 2 := rectangleEnergy_le d u v f
      _ = (1 / (2 * Real.exp d) ^ 2) * ‖f‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h (sq_nonneg _)

end
end GaloisForLFunctions.HTGeometry.Wu
