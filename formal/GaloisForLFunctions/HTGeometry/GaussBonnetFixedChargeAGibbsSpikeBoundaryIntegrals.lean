import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeBoundarySource

/-! # Strong testing and exact variation of the dimensional source boundary -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter

private theorem integrable_atom (w : NNReal) (y : HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) : Integrable f (hausdorffAtomSource w y) := by
  unfold hausdorffAtomSource
  change Integrable f ((w : ENNReal) • Measure.dirac y)
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

private theorem integral_atom (w : NNReal) (y : HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ z, f z ∂hausdorffAtomSource w y = (w : ℝ) * f y := by
  simp [hausdorffAtomSource, NNReal.smul_def]

private theorem integral_three_atoms (a b c : NNReal) (x y z : HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ t, f t ∂(hausdorffAtomSource a x + hausdorffAtomSource b y + hausdorffAtomSource c z) =
      (a : ℝ) * f x + (b : ℝ) * f y + (c : ℝ) * f z := by
  rw [integral_add_measure (integrable_add_measure.mpr ⟨integrable_atom a x f, integrable_atom b y f⟩)
    (integrable_atom c z f), integral_add_measure (integrable_atom a x f) (integrable_atom b y f)]
  rw [integral_atom, integral_atom, integral_atom]

/-- Every real test function is integrated by the same three exact atomic coefficients. -/
theorem egbFixedChargeAGibbsSpike_source_integral (n : ℕ) (f : HausdorffSourceSpace → ℝ) :
    ∫ y, f y ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) *
        f egbFixedChargeAGibbsCollisionZeroNode +
      egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) *
        f egbFixedChargeAGibbsCollisionSlowNode +
      egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) *
        f egbFixedChargeAGibbsCollisionFastNode := by
  exact integral_three_atoms _ _ _ _ _ _ f

/-- The literal boundary measure evaluates any real test at the zero-rate endpoint. -/
theorem egbFixedChargeAGibbsSpike_boundary_integral (f : HausdorffSourceSpace → ℝ) :
    ∫ y, f y ∂egbFixedChargeAGibbsSpikeBoundarySource =
      (1 / 4 : ℝ) * f egbFixedChargeAGibbsCollisionZeroNode := by
  exact integral_atom _ _ f

/-- The testing error is exactly an inverse-grid multiple of three fixed evaluations. -/
theorem egbFixedChargeAGibbsSpike_integral_error (n : ℕ) (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsSpikeEnergy n)) -
      (∫ y, f y ∂egbFixedChargeAGibbsSpikeBoundarySource) =
      (-5 * f egbFixedChargeAGibbsCollisionZeroNode + 2 * f egbFixedChargeAGibbsCollisionSlowNode +
        2 * f egbFixedChargeAGibbsCollisionFastNode) / (4 * (2 : ℝ) ^ (n + 3)) := by
  rw [egbFixedChargeAGibbsSpike_source_integral, egbFixedChargeAGibbsSpike_boundary_integral,
    egbFixedChargeAGibbsSpike_discarded_energy, egbFixedChargeAGibbsSpike_slow_energy,
    egbFixedChargeAGibbsSpike_fast_energy]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn]
  <;> ring

/-- Every fixed real test converges, without a continuity or boundedness premise. -/
theorem egbFixedChargeAGibbsSpike_integrals_tendsto_boundary (f : HausdorffSourceSpace → ℝ) :
    Tendsto (fun n : ℕ => ∫ y, f y ∂egbFixedChargeAGibbsFullCollisionHausdorffSource n 1
      (egbFixedChargeAGibbsSpikeEnergy n)) atTop
      (nhds (∫ y, f y ∂egbFixedChargeAGibbsSpikeBoundarySource)) := by
  have h := ((egbFixedChargeAGibbsSpike_discarded_tendsto_quarter.mul_const
    (f egbFixedChargeAGibbsCollisionZeroNode)).add
    (egbFixedChargeAGibbsSpike_slow_tendsto_zero.mul_const (f egbFixedChargeAGibbsCollisionSlowNode))).add
    (egbFixedChargeAGibbsSpike_fast_tendsto_zero.mul_const (f egbFixedChargeAGibbsCollisionFastNode))
  simpa only [egbFixedChargeAGibbsSpike_source_integral, egbFixedChargeAGibbsSpike_boundary_integral,
    zero_mul, add_zero] using h

/-- Integration against the actual variation measure has positive coefficients at all three atoms. -/
theorem egbFixedChargeAGibbsSpike_variation_integral (n : ℕ) (f : HausdorffSourceSpace → ℝ) :
    ∫ y, f y ∂(egbFixedChargeAGibbsSpikeBoundaryError n).totalVariation =
      (f egbFixedChargeAGibbsCollisionSlowNode + f egbFixedChargeAGibbsCollisionFastNode) /
        (2 * (2 : ℝ) ^ (n + 3)) +
      5 / (4 * (2 : ℝ) ^ (n + 3)) * f egbFixedChargeAGibbsCollisionZeroNode := by
  rw [egbFixedChargeAGibbsSpikeBoundaryError_totalVariation]
  unfold egbFixedChargeAGibbsSpikeBoundaryPositivePart egbFixedChargeAGibbsSpikeBoundaryNegativePart
  rw [integral_three_atoms]
  change egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) *
    f egbFixedChargeAGibbsCollisionSlowNode +
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) *
    f egbFixedChargeAGibbsCollisionFastNode +
    5 / (4 * (2 : ℝ) ^ (n + 3)) * f egbFixedChargeAGibbsCollisionZeroNode = _
  rw [egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy]
  ring

/-- The total mass of the literal total variation is exactly nine divided by four grid sizes. -/
theorem egbFixedChargeAGibbsSpike_variation_mass (n : ℕ) :
    (egbFixedChargeAGibbsSpikeBoundaryError n).totalVariation.real Set.univ =
      9 / (4 * (2 : ℝ) ^ (n + 3)) := by
  have h := egbFixedChargeAGibbsSpike_variation_integral n (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h]
  ring

/-- The actual signed source error vanishes in total variation mass. -/
theorem egbFixedChargeAGibbsSpike_variation_mass_tendsto_zero :
    Tendsto (fun n : ℕ => (egbFixedChargeAGibbsSpikeBoundaryError n).totalVariation.real Set.univ)
      atTop (nhds 0) := by
  have he (n : ℕ) : (egbFixedChargeAGibbsSpikeBoundaryError n).totalVariation.real Set.univ =
      (9 / 4 : ℝ) * ((2 : ℝ) ^ (n + 3))⁻¹ := by
    rw [egbFixedChargeAGibbsSpike_variation_mass]
    ring
  simpa only [he, mul_zero] using egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero.const_mul (9 / 4 : ℝ)

end
end GaloisForLFunctions.HTGeometry
