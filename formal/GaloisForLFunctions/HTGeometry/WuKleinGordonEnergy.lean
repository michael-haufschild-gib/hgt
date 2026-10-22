import GaloisForLFunctions.HTGeometry.WuDoubleNullEnergy
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonEnergyConservation
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldMild

/-!
# Wu integration for free Klein–Gordon dynamics

The characteristic integration estimate of arXiv:2609.08421, Lemma 2.3,
acts on the existing infinite-dimensional energy propagator, on its cosine
and sine channels, and on the field with arbitrary L² Cauchy data.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Exact weighted observation of the conserved Klein–Gordon energy. -/
theorem kleinGordon_energy (v : KGEnergy E) (d t : ℝ) :
    energy d t (fun s => kgPropagator s v) = mass d t * ‖v‖ ^ (2 : ℕ) := by
  unfold energy
  simp_rw [norm_kgPropagator_apply]
  rw [intervalIntegral.integral_mul_const, integral_weight]

/-- Exact energy stability in the full pair of initial data. -/
theorem kleinGordon_difference_energy (v w : KGEnergy E) (d t : ℝ) :
    energy d t (fun s => kgPropagator s v - kgPropagator s w) = mass d t * ‖v - w‖ ^ (2 : ℕ) := by
  simp_rw [← map_sub]
  exact kleinGordon_energy (v - w) d t

/-- Repeated characteristic integration is sharp for two successive wave evolutions. -/
theorem kleinGordon_rectangle_energy (v : KGEnergy E) (d u t : ℝ) :
    rectangleEnergy d u t (fun p => kgPropagator p.1 (kgPropagator p.2 v)) =
      mass d u * mass d t * ‖v‖ ^ (2 : ℕ) := by
  unfold rectangleEnergy energy
  simp_rw [norm_kgPropagator_apply]
  rw [intervalIntegral.integral_mul_const, integral_weight,
    intervalIntegral.integral_mul_const, integral_weight]
  ring

/-- The cosine and sine channels partition the integrated energy exactly. -/
theorem kleinGordon_channel_energy (v : Lp ℂ 2 (volume : Measure E)) (d t : ℝ) :
    energy d t (fun s => kgCosOp s v) + energy d t (fun s => kgSinOp s v) =
      mass d t * ‖v‖ ^ (2 : ℕ) := by
  unfold energy
  have hc : IntervalIntegrable (fun s => weight d t s * ‖kgCosOp s v‖ ^ (2 : ℕ)) volume 0 |t| :=
    ((continuous_weight d t).mul ((continuous_kgCosOp_apply v).norm.pow 2)).intervalIntegrable 0 |t|
  have hs : IntervalIntegrable (fun s => weight d t s * ‖kgSinOp s v‖ ^ (2 : ℕ)) volume 0 |t| :=
    ((continuous_weight d t).mul ((continuous_kgSinOp_apply v).norm.pow 2)).intervalIntegrable 0 |t|
  rw [← intervalIntegral.integral_add hc hs]
  simp_rw [← mul_add, norm_kgCosOp_sq_add_norm_kgSinOp_sq]
  rw [intervalIntegral.integral_mul_const, integral_weight]

/-- The free field curve, bounded by the original two Cauchy norms. -/
def kleinGordonFieldOrbit (f h : Lp ℂ 2 (volume : Measure E)) :
    BoundedContinuousFunction ℝ (Lp ℂ 2 (volume : Measure E)) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (kgFieldFree f h)
    (continuous_kgFieldFree f h) (‖f‖ + ‖h‖) (norm_kgFieldFree_le f h)

/-- The field itself inherits a uniform weighted L²-in-time bound from arbitrary L² Cauchy data. -/
theorem kleinGordon_field_energy_le (f h : Lp ℂ 2 (volume : Measure E)) (d t : ℝ) :
    energy d t (kgFieldFree f h) ≤ (‖f‖ + ‖h‖) ^ (2 : ℕ) / (2 * Real.exp d) := by
  have hb : ‖kleinGordonFieldOrbit f h‖ ≤ ‖f‖ + ‖h‖ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _
  exact (energy_le d t (kleinGordonFieldOrbit f h)).trans
    (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb) (by positivity))

/-- The source-to-field sine channel is uniformly bounded, even at zero frequency. -/
def kleinGordonSineOrbit (h : Lp ℂ 2 (volume : Measure E)) :
    BoundedContinuousFunction ℝ (Lp ℂ 2 (volume : Measure E)) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => kgSinFreqOp s h)
    (continuous_kgSinFreqOp_apply h) ‖h‖ (fun s => norm_kgSinFreqOp_apply_le s h)

/-- The Duhamel sine propagator has the same inverse-rate integrated gain. -/
theorem kleinGordon_sine_energy_le (h : Lp ℂ 2 (volume : Measure E)) (d t : ℝ) :
    energy d t (fun s => kgSinFreqOp s h) ≤ ‖h‖ ^ (2 : ℕ) / (2 * Real.exp d) := by
  have hb : ‖kleinGordonSineOrbit h‖ ≤ ‖h‖ :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _
  exact (energy_le d t (kleinGordonSineOrbit h)).trans
    (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb) (by positivity))

end
end GaloisForLFunctions.HTGeometry.Wu
