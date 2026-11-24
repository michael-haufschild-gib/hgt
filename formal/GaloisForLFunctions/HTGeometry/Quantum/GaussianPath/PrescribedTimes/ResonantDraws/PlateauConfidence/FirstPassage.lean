import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PlateauConfidence.ClockBounds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DisorderTails

/-! # Extreme upper quantiles of the onset and actual first waits -/
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
open PassageMoments
noncomputable section

/-- With exceptional mass at most 3·2⁻ᴰ, the first near-Hilbert crossing
and every elapsed first wait end by a common doubly exponential deadline.
At every deadline T ≥ 1, both the onset and *all*
half-budget waits simultaneously exceed T with probability at least c/T¹⁸. -/
theorem gaussian_first_passage_confidence :
    ∃ b : ℕ, ∃ c > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let N := k+3
      let D : ℕ := 2^N
      let P := nearHilbertContinuousCircuitBudget N
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      let Δ := crossingWait n P
      let G := (2:ℝ)^(D^b)
      μ.real {x | G<σ x ∨ ∃ s, G<Δ s x} ≤ 3*(1/2:ℝ)^D ∧
        ∀ T ≥ (1:ℝ), c ≤ T^18*μ.real {x | T<σ x ∧ ∀ s ≤ P/2, T<Δ s x} := by
  obtain ⟨b,hb⟩ := SpectralJets.gaussian_exponential_confidence_clock
  obtain ⟨c,hc,hc'⟩ := WeakBonds.gaussian_uniform_first_excursion_tail
  refine ⟨b,c,hc,?_⟩
  filter_upwards [hc',(tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier] with k htail hent
  intro n N D P μ σ Δ G
  refine ⟨?_,htail⟩
  let F := {x | G<passageMax k 0 x}
  have hm : MeasurableSet F := measurableSet_lt measurable_const (measurable_passageMax k 0)
  have hsub : {x | G<σ x ∨ ∃ s, G<Δ s x} ⊆ F := by
    intro x hx
    rcases hx with h | ⟨s,h⟩
    · exact h.trans_le (le_max_left ..)
    · exact h.trans_le ((crossingWait_antitone (n:=n) (j:=P) (Nat.zero_le s) x).trans (le_max_right ..))
  let X := fun ω i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  obtain ⟨B,hB,hh⟩ := hb k
  have ha : X ⁻¹' F ≤ᵐ[pathPauliDisorderLaw] B := by
    filter_upwards [hh] with ω hω hx
    change G<passageMax k 0 (X ω) at hx
    exact Classical.byContradiction fun hn => hx.not_ge (clock_bounds_first_passage k ω G hent (hω hn))
  apply (measureReal_mono (μ:=μ) hsub).trans
  rw [←hX.measureReal_preimage hm.nullMeasurableSet]
  change (pathPauliDisorderLaw (X ⁻¹' F)).toReal ≤ _
  have hi : pathPauliDisorderLaw (X ⁻¹' F) ≤ ENNReal.ofReal (3*(1/2:ℝ)^D) :=
    (measure_mono_ae ha).trans hB
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hi).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

#print axioms gaussian_first_passage_confidence

/-- To make even the simultaneous survival probability at most βᴰ, the
logarithm of the deadline must grow at least linearly in dimension. -/
theorem gaussian_joint_survival_deadline :
    ∃ a : ℝ, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let D : ℕ := 2^(k+3)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      ∀ T ≥ (1:ℝ), ∀ β > (0:ℝ),
        μ.real {x | T<crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T<crossingWait n P s x} ≤ β^D →
          (a-(D:ℝ)*log β)/18 ≤ log T := by
  obtain ⟨c,hc,h⟩ := WeakBonds.gaussian_uniform_first_excursion_tail
  refine ⟨log c,?_⟩
  filter_upwards [h] with k hk
  intro n D P μ T hT β hβ hmass
  have ht : 0<T := zero_lt_one.trans_le hT
  have hl := log_le_log hc ((hk T hT).trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg ht.le 18)))
  rw [log_mul (pow_pos ht _).ne' (pow_pos hβ _).ne',log_pow,log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

#print axioms gaussian_joint_survival_deadline
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
