import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Recovering a prescribed-date limit from quenched dilation averages -/
open Set MeasureTheory ProbabilityTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

/-- If the time section of a Gaussian event has a limiting occupation on
each dilation interval, then its probability at the prescribed date has
the same limit. The proof uses only measurability at individual dates. -/
theorem snapshot_of_ray_limit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : ℝ)
    (h : ∀ b > (1:ℝ), ∀ᵐ ω ∂P, Tendsto (fun t => rayMass b (E t) (X ω)) atTop (𝓝 ((b-1)*p))) :
    Tendsto (fun t => (Measure.pi fun _ : ι => gaussianReal 0 1).real (E t)) atTop (𝓝 p) := by
  let μ := Measure.pi fun _ : ι => gaussianReal 0 1
  let m := Fintype.card ι
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hpow⟩ := Metric.continuousAt_iff.mp
    (continuousAt_id.pow m : ContinuousAt (fun a : ℝ => a^m) 1) (ε/2) (half_pos hε)
  let b := 1+δ/2
  have hb : 1<b := lt_add_of_pos_right _ (half_pos hδ)
  have hbd : dist b 1 < δ := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hb)]
    dsimp only [b]; linarith only [hδ]
  have herr := hpow hbd
  simp only [Real.dist_eq,one_pow] at herr
  have he₁ : b^m-1 < ε/2 := (le_abs_self _).trans_lt herr
  let R (t : ℝ) := rayMass b (E t)
  have hR (t : ℝ) : Measurable (R t) := measurable_rayMass b (hE t)
  have hbound (t : ℝ) (ω : Ω) : ‖R t (X ω)‖ ≤ b-1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤R t (X ω) from measureReal_nonneg)]
    apply (measureReal_mono (subset_univ _)).trans_eq
    exact (measureReal_restrict_apply_univ _).trans (Real.volume_real_Icc_of_le hb.le)
  have hmean := tendsto_integral_filter_of_dominated_convergence
    (μ:=P) (F:=fun t ω => R t (X ω)) (f:=fun _ => (b-1)*p) (fun _ => b-1)
    (Eventually.of_forall fun t => ((hR t).comp hX.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ (hbound t)) (integrable_const _) (h b hb)
  have he (t : ℝ) : (∫ ω, R t (X ω) ∂P)=∫ x, R t x ∂μ := by
    change _=∫ x, R t x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
    rw [←hX.map_eq,integral_map hX.measurable.aemeasurable (hR t).aestronglyMeasurable]
  simp only [he,integral_const,probReal_univ,one_smul] at hmean
  have hav := hmean.div_const (b-1)
  rw [mul_div_cancel_left₀ p (sub_pos.mpr hb).ne'] at hav
  filter_upwards [Metric.tendsto_nhds.mp hav (ε/2) (half_pos hε)] with t ht
  have hbnd := mean_rayMass_error (E t) (hE t) hb
  change |(∫ x, R t x ∂μ)/(b-1)-μ.real (E t)| ≤ b^m-1 at hbnd
  change dist (μ.real (E t)) p < ε
  calc
    _ ≤ dist (μ.real (E t)) ((∫ x, R t x ∂μ)/(b-1)) + dist ((∫ x, R t x ∂μ)/(b-1)) p := dist_triangle .. 
    _ < ε/2+ε/2 := add_lt_add (by rw [dist_comm,Real.dist_eq]; exact hbnd.trans_lt he₁) ht
    _ = ε := add_halves ε

#print axioms snapshot_of_ray_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
