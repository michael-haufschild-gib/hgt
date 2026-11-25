import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PlateauDelay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PhysicalWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.HilbertWindows

/-! # Minimum spectral winding for exponentially confident plateau exclusion -/

open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes AntipodalHorizons CircuitWindings
noncomputable section

private def antipodeHit (n m P : ℕ) := {x : PrefixIndex n→ℝ |
  pathGateDistance n P x (extremalAntipode n m x)≤9/80}

private theorem measurable_antipodeHit (k m P : ℕ) : MeasurableSet (antipodeHit (k+1) m P) := by
  let t := extremalAntipode (k+1) m
  have ht : Measurable t := by
    unfold t extremalAntipode
    exact (measurable_const (a:=((m:ℝ)+1/2)*(2*π))).div (continuous_prefix_width k).measurable
  let f := fun p : (PrefixIndex (k+1)→ℝ) × ℝ => pathGateDistance (k+1) P p.1 p.2
  let v := fun x : PrefixIndex (k+1)→ℝ => (x,t x)
  have hv : Measurable v := (measurable_id' (α:=PrefixIndex (k+1)→ℝ)).prodMk ht
  have hf : Measurable f := (continuous_distance (k+1) P).measurable
  change MeasurableSet {x | (f ∘ v) x ≤ (9/80:ℝ)}
  exact measurableSet_le (hf.comp hv) (measurable_const (a:=(9/80:ℝ)))

private theorem endpoint_in_window (k m P : ℕ) {L ε : ℝ} (hL : 0≤L) (hε : 9/80≤ε)
    (ω : PathPauliDisorder) :
    let u := pathPauliDisorderShell ω (k+1)
    let x := fun i => u (pathCoeffEquiv (k+1) i)
    x∈antipodeHit (k+1) m P → ω∈gateWindow k m P 0 L ε := by
  intro u x hx
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  have he : date E (topLevel k) 0 m 0=extremalAntipode (k+1) m x := by
    rw [extremalAntipode,intrinsic_sorted_width k x]
    simp only [date,add_zero,mul_div_assoc,E]
  refine ⟨0,⟨le_rfl,by simpa only [zero_add] using hL⟩,?_⟩
  apply (hasProjectiveCircuitApproximation_iff_infDist _ P ε).mpr
  change Metric.infDist (unitaryEvolution (pathHamiltonian u) (date E (topLevel k) 0 m 0)) _ ≤ ε
  rw [he,←numberedGenerator_shell u]
  exact (show pathGateDistance (k+1) P x (extremalAntipode (k+1) m x)≤9/80 from hx).trans hε

private theorem endpoint_mass_le (k m P : ℕ) {L ε : ℝ} (hL : 0≤L) (hε : 9/80≤ε) :
    (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1).real (antipodeHit (k+1) m P) ≤
      pathPauliDisorderLaw.real (gateWindow k m P 0 L ε) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
    (measurable_antipodeHit k m P).nullMeasurableSet
  exact he.symm.le.trans (measureReal_mono
    (fun {ω} hω => endpoint_in_window k m P hL hε ω hω) (measure_ne_top _ _))

private theorem rescale_floor (m : ℕ) {r c p q : ℝ} (hr : 1≤r) (hp : 0≤p) (hpq : p≤q)
    (hc : c≤(1+π*((m:ℝ)+1/2)/r)^18*p) : c/5^18≤((m:ℝ)+1)^18*q := by
  have hw : 1+π*((m:ℝ)+1/2)/r≤5*((m:ℝ)+1) := by
    have hl := div_le_self (show 0≤π*((m:ℝ)+1/2) by positivity) hr
    have hm := mul_le_mul_of_nonneg_right pi_lt_four.le (show 0≤(m:ℝ)+1/2 by positivity)
    linarith only [hl,hm,Nat.cast_nonneg (α:=ℝ) m]
  have hr₀ : 0≤r := zero_le_one.trans hr
  have hh := hc.trans (mul_le_mul (pow_le_pow_left₀ (by positivity) hw 18) hpq hp (by positivity))
  rw [mul_pow,mul_assoc,mul_comm (5^18:ℝ)] at hh
  exact (div_le_iff₀ (by positivity)).mpr hh

/-- The probability of a near-Hilbert visit over a window starting at
the mth extremal antipode is at least c/(m+1)^18, even if only its
left endpoint is examined. The constant is uniform in register size. -/
theorem gaussian_gate_window_floor :
    ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop, ∀ m : ℕ, ∀ L≥(0:ℝ), ∀ ε≥(9/80:ℝ),
      let P := nearHilbertContinuousCircuitBudget (k+3)
      c≤((m:ℝ)+1)^18*pathPauliDisorderLaw.real (gateWindow k m P 0 L ε) := by
  obtain ⟨c,hc,h⟩ := gaussian_preplateau_antipode_mass
  refine ⟨c/5^18,div_pos hc (by positivity),?_⟩
  filter_upwards [h] with k hk
  intro m L hL ε hε P
  let n := k+1
  let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hdim : 1≤Fintype.card (PrefixIndex n) := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hr : 1≤r := one_le_sqrt.mpr (by exact_mod_cast hdim)
  apply rescale_floor m hr (measureReal_nonneg (μ:=μ) (s:=antipodeHit n m P)) (endpoint_mass_le k m P hL hε)
  apply (hk m).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro x hx
  have ht : 0≤extremalAntipode n m x :=
    div_nonneg (by positivity) (circuitHamiltonianSpectralWidth_nonneg _)
  exact (hx _ ⟨ht,le_rfl⟩).le

/-- The first winding at which near-Hilbert exclusion over the whole
(8/7)^D-period window attains exponential confidence is finite. Its
eighteenth power must already grow exponentially in Hilbert dimension. -/
theorem gaussian_first_confident_plateau_winding :
    ∃ ρ∈Ioo (0:ℝ) 1, ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let W := {m : ℕ | pathPauliDisorderLaw.real
        (gateWindow k m P 0 ((1/(7/8:ℝ))^D) (1/8))≤ρ^(D-3)}
      sInf W∈W ∧ c*(1/ρ)^(D-3) ≤ (((sInf W:ℕ):ℝ)+1)^18 := by
  have he : (1/8:ℝ)∈Ioo (0:ℝ) (sqrt 2) :=
    ⟨by norm_num,(by norm_num : (1/8:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))⟩
  obtain ⟨ρ,hρ,hlate⟩ := gaussian_near_hilbert_antipodal_window he
  obtain ⟨c,hc,hfloor⟩ := gaussian_gate_window_floor
  refine ⟨ρ,hρ,c,hc,?_⟩
  filter_upwards [hlate,hfloor] with k hk hf
  intro D P W
  have hne : W.Nonempty := ((hk 0).mono (fun _ hm => hm.le)).exists
  have hm := Nat.sInf_mem hne
  refine ⟨hm,?_⟩
  have h := (hf (sInf W) ((1/(7/8:ℝ))^D) (by positivity) (1/8) (by norm_num)).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))
  rw [one_div,inv_pow,←div_eq_mul_inv,div_le_iff₀ (pow_pos hρ.1 _)]
  exact h

#print axioms gaussian_gate_window_floor
#print axioms gaussian_first_confident_plateau_winding
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
