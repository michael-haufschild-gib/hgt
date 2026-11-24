import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.RayBounds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.SnapshotLimit

/-! # Disorder limits after selecting samples by their first passages -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

/-- A radial occupation limit that is constant across draws remains
valid after selecting any expansion-closed measurable sample event. -/
theorem selected_snapshot_limit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (B : Set (ι → ℝ)) (hB : MeasurableSet B) (hclosed : expansionClosed B)
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : ℝ)
    (h : ∀ b > (1:ℝ), ∀ᵐ ω ∂P, Tendsto (fun t => rayMass b (E t) (X ω)) atTop (𝓝 ((b-1)*p))) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    Tendsto (fun t => μ.real (B ∩ E t)) atTop (𝓝 (μ.real B*p)) := by
  intro μ
  let m := Fintype.card ι
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hpow⟩ := Metric.continuousAt_iff.mp
    (continuousAt_id.pow m : ContinuousAt (fun a : ℝ => a^m) 1) (ε/4) (by linarith only [hε])
  let b := 1+δ/2
  have hb : 1<b := lt_add_of_pos_right _ (half_pos hδ)
  have hbd : dist b 1 < δ := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hb)]
    dsimp only [b]; linarith only [hδ]
  have herr := hpow hbd
  change dist (b^m) ((1:ℝ)^m) < ε/4 at herr
  rw [Real.dist_eq,one_pow] at herr
  have he₁ : 2*(b^m-1) < ε/2 := by linarith only [(le_abs_self _).trans_lt herr]
  let L := b-1
  have hL : 0<L := sub_pos.mpr hb
  let W (t : ℝ) := B.indicator (rayMass b (E t))
  have hW (t : ℝ) : Measurable (W t) := (measurable_rayMass b (hE t)).indicator hB
  have hbound (t : ℝ) (ω : Ω) : ‖W t (X ω)‖≤L := by
    by_cases hω : X ω∈B
    · rw [show W t (X ω)=rayMass b (E t) (X ω) from indicator_of_mem hω _,Real.norm_eq_abs,
        abs_of_nonneg (show 0≤rayMass b (E t) (X ω) from measureReal_nonneg)]
      exact (measureReal_mono (subset_univ _)).trans_eq
        ((measureReal_restrict_apply_univ _).trans (Real.volume_real_Icc_of_le hb.le))
    · rw [show W t (X ω)=0 from indicator_of_notMem hω _,norm_zero]; exact hL.le
  let f := (X ⁻¹' B).indicator (fun _ => L*p)
  have hpoint : ∀ᵐ ω ∂P, Tendsto (fun t => W t (X ω)) atTop (𝓝 (f ω)) := by
    filter_upwards [h b hb] with ω hω
    by_cases hx : X ω∈B
    · simpa only [W,f,indicator_of_mem hx,indicator_of_mem (show ω∈X ⁻¹' B from hx)] using hω
    · simpa only [W,f,indicator_of_notMem hx,indicator_of_notMem (show ω∉X ⁻¹' B from hx)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ:=P) (F:=fun t ω => W t (X ω)) (f:=f) (fun _ => L)
    (Eventually.of_forall fun t => ((hW t).comp hX.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ (hbound t)) (integrable_const _) hpoint
  have he (t : ℝ) : (∫ ω, W t (X ω) ∂P)=∫ x, W t x ∂μ := by
    change _=∫ x, W t x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
    rw [←hX.map_eq,integral_map hX.measurable.aemeasurable (hW t).aestronglyMeasurable]
  have hf : (∫ ω, f ω ∂P)=L*(μ.real B*p) := by
    rw [show (∫ ω, f ω ∂P)=P.real (X ⁻¹' B)*(L*p) by
      dsimp only [f]
      rw [integral_indicator (hB.preimage hX.measurable),setIntegral_const,smul_eq_mul],
      hX.measureReal_preimage hB.nullMeasurableSet]
    ring
  simp only [he,hf] at hh
  have hav := hh.div_const L
  rw [mul_div_cancel_left₀ _ hL.ne'] at hav
  filter_upwards [Metric.tendsto_nhds.mp hav (ε/2) (half_pos hε)] with t ht
  have hh' := selected_mean_error B (E t) hB (hE t) hclosed hb
  change |(∫ x, W t x ∂μ)/L-μ.real (B ∩ E t)| ≤ 2*(b^m-1) at hh'
  calc
    _ ≤ dist (μ.real (B ∩ E t)) ((∫ x, W t x ∂μ)/L) + dist ((∫ x, W t x ∂μ)/L) (μ.real B*p) :=
      dist_triangle ..
    _ < ε/2+ε/2 := add_lt_add (by rw [dist_comm,Real.dist_eq]; exact hh'.trans_lt he₁) ht
    _ = ε := add_halves ε

#print axioms selected_snapshot_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
