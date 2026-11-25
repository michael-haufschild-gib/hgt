import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PlateauDelay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.PhysicalWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.HilbertWindows

/-! # Minimum spectral winding for exponentially confident plateau exclusion -/

open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes AntipodalHorizons CircuitWindings
noncomputable section

/-- The probability of a near-Hilbert visit over a window starting at
the mth extremal antipode is at least c/(m+1)^18, even if only its
left endpoint is examined. The constant is uniform in register size. -/
theorem gaussian_gate_window_floor :
    ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop, ∀ m : ℕ, ∀ L≥(0:ℝ), ∀ ε≥(9/80:ℝ),
      let P := nearHilbertContinuousCircuitBudget (k+3)
      c≤((m:ℝ)+1)^18*pathPauliDisorderLaw.real (gateWindow k m P 0 L ε) := by
  obtain ⟨c,hc,h⟩ := gaussian_preplateau_antipode_mass
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  refine ⟨c/5^18,div_pos hc (by positivity),?_⟩
  filter_upwards [h] with k hk
  intro m L hL ε hε P
  let n := k+1
  let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  letI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let A := {x : PrefixIndex n→ℝ | pathGateDistance n P x (extremalAntipode n m x)≤9/80}
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hd : Measurable (extremalAntipode n m) := measurable_const.div (continuous_prefix_width k).measurable
  have hA : MeasurableSet A := measurableSet_le
    ((continuous_distance n P).measurable.comp (measurable_id'.prodMk hd)) measurable_const
  have hmass : c≤(1+π*((m:ℝ)+1/2)/r)^18*μ.real A := by
    apply (hk m).trans
    apply mul_le_mul_of_nonneg_left _ (by dsimp only [r]; positivity)
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    have ht : 0≤extremalAntipode n m x := div_nonneg (by positivity) (circuitHamiltonianSpectralWidth_nonneg _)
    exact (hx _ ⟨ht,le_rfl⟩).le
  have hit : X ⁻¹' A ⊆ gateWindow k m P 0 L ε := by
    intro ω hω
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (X ω)
    have he : date E (topLevel k) 0 m 0=extremalAntipode n m (X ω) := by
      rw [extremalAntipode,intrinsic_sorted_width k (X ω)]
      dsimp only [date,E]; ring
    refine ⟨0,⟨le_rfl,by simpa only [zero_add] using hL⟩,?_⟩
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    change Metric.infDist (unitaryEvolution (pathHamiltonian _) (date E (topLevel k) 0 m 0)) _ ≤ ε
    rw [he,←numberedGenerator_shell (pathPauliDisorderShell ω n)]
    exact (show pathGateDistance n P (X ω) (extremalAntipode n m (X ω))≤9/80 from hω).trans hε
  have hprob : μ.real A≤pathPauliDisorderLaw.real (gateWindow k m P 0 L ε) := by
    rw [←hX.measureReal_preimage hA.nullMeasurableSet]
    exact measureReal_mono hit
  have hdim : 1≤Fintype.card (PrefixIndex n) := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hr : 1≤r := one_le_sqrt.mpr (by exact_mod_cast hdim)
  have hw : 1+π*((m:ℝ)+1/2)/r≤5*((m:ℝ)+1) := by
    have hl := div_le_self (show 0≤π*((m:ℝ)+1/2) by positivity) hr
    have hm := mul_le_mul_of_nonneg_right pi_lt_four.le (show 0≤(m:ℝ)+1/2 by positivity)
    linarith only [hl,hm,Nat.cast_nonneg (α:=ℝ) m]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<5^18)).mpr
  have hh := hmass.trans (mul_le_mul (pow_le_pow_left₀ (by dsimp only [r]; positivity) hw _) hprob
    measureReal_nonneg (by positivity))
  convert hh using 1 <;> ring

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
