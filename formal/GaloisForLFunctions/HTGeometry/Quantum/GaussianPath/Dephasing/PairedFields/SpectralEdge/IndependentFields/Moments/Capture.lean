import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.GaussianActions

/-! # Gaussian capture by a finite family of spectral twists -/

open MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
private abbrev law (J : Type*) [Fintype J] := Measure.pi fun _ : J => gaussianReal 0 1

omit [DecidableEq I] in

/-- Probability of a high overlap with any of the prescribed targets, in
terms of their individual Gaussian moments. The twists may have zero
entries, as occurs for a circuit far from the energy-diagonal subgroup. -/
theorem field_capture_twists {ι : Type*} [Fintype ι] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i=1) (v : J → I → ℝ) (z : ι → I → ℂ)
    (hz : ∀ j i, ‖z j i‖ ≤ 1) (q : ℕ) (L : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ^(2*q)*(law J).real (⋃ j, {g | τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) L‖}) ≤
      ∑ j, ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (z j) L ^ q ∂law J‖ := by
  let A (j : ι) := {g | τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) L‖}
  have hcap (j : ι) : τ^(2*q)*(law J).real (A j) ≤
        ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (z j) L ^ q ∂law J‖ := by
    let f (g : J → ℝ) := ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) L‖^(2*q)
    have hnn (g) : 0 ≤ f g := pow_nonneg (norm_nonneg _) _
    have hb (g : J → ℝ) : ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) L‖ ≤ 1 := by
      unfold twistedFiniteSpectralAmplitude
      apply (norm_sum_le ..).trans
      rw [←hsum]
      apply sum_le_sum
      intro i _
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw i),Complex.norm_exp]
      simpa using mul_le_of_le_one_right (hw i) (hz j i)
    have hi : Integrable f (law J) := by
      apply (integrable_const (1:ℝ)).mono'
      · have hc : Continuous f := by
          dsimp only [f,twistedFiniteSpectralAmplitude,fieldEnergy]
          fun_prop
        exact hc.aestronglyMeasurable
      · exact ae_of_all _ fun g => (Real.norm_of_nonneg (hnn g)).le.trans
          (pow_le_one₀ (norm_nonneg _) (hb g))
    have he : A j ⊆ {g | τ^(2*q) ≤ f g} := fun _ hg => pow_le_pow_left₀ hτ hg _
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hnn) hi (τ^(2*q))
    have hc : (∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (z j) L ^ q ∂law J) =
        (∫ g, (f g:ℂ) ∂law J) := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        simp only [twistedFiniteSpectralFidelity,Complex.normSq_eq_norm_sq,f,pow_mul,Complex.ofReal_pow]
    rw [hc,integral_complex_ofReal,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg hnn)]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono he) (pow_nonneg hτ _)).trans hm
  apply (mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le A) (pow_nonneg hτ _)).trans
  rw [mul_sum]
  exact sum_le_sum fun j _ => hcap j

/-- Taking absolute values after the Gaussian integral retains the full
local-slope kernel as a uniform upper bound for every target. -/
theorem field_capture_moment {ι : Type*} [Fintype ι] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i=1) (v : J → I → ℝ) (z : ι → I → ℂ)
    (hz : ∀ j i, ‖z j i‖ ≤ 1) (q : ℕ) (L : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ^(2*q)*(law J).real (⋃ j, {g | τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (z j) L‖}) ≤
      Fintype.card ι*slopeMoment w v q L := by
  apply (field_capture_twists w hw hsum v z hz q L hτ).trans
  simpa only [sum_const,card_univ,nsmul_eq_mul] using
    sum_le_sum (s:=univ) (fun j _ => field_fidelity_moment_le hw v (hz j) q L)

#print axioms field_capture_twists
#print axioms field_capture_moment
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
