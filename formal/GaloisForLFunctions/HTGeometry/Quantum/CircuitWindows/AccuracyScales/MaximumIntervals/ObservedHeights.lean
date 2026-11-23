import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.OrbitProfiles

/-! # Finite observation of all gate-budget thresholds -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
noncomputable section

/-- In every observation window a worst date for each budget recovers the
global critical tolerance to within one bit of error per Hilbert dimension.
The date may depend on the budget. -/
theorem gaussian_observed_critical_heights :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H := chainGenerator ω k
      let G := (2:ℝ)^(D^C)
      ∀ (a : ℝ) (s : ℕ), ∃ z ∈ Icc a (a+G),
        (∀ t ∈ Icc a (a+G), orbitCircuitDistance H s t ≤ orbitCircuitDistance H s z) ∧
        orbitCircuitDistance H s z ≤ criticalHeight H s ∧
        criticalHeight H s ≤ orbitCircuitDistance H s z+1/(2:ℝ)^D := by
  obtain ⟨C,hC⟩ := SpectralJets.HighPrecision.gaussian_uniform_profile_recurrence
  refine ⟨C,?_⟩
  filter_upwards [hC] with ω hω
  filter_upwards [hω] with k hk
  intro N D H G a s
  have hG : 0 ≤ G := by dsimp [G]; positivity
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (le_add_of_nonneg_right hG)) (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
  have htop : orbitCircuitDistance H s z+1/(2:ℝ)^D ∈ upperBounds (range (orbitCircuitDistance H s)) := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨u,hu,hp⟩ := hk a v
    have h := (abs_le.mp (hp 0 s)).1
    simp only [add_zero] at h
    have hm := isMaxOn_iff.mp hmax u hu
    change orbitCircuitDistance H s u ≤ orbitCircuitDistance H s z at hm
    change -(1/(2:ℝ)^D) ≤ orbitCircuitDistance H s u-orbitCircuitDistance H s v at h
    linarith only [hm,h]
  exact ⟨z,hz,isMaxOn_iff.mp hmax,le_csSup ⟨_,htop⟩ (mem_range_self z),csSup_le (range_nonempty _) htop⟩

/-- At any fixed tolerance, a budget which covers a whole observation
window but misses some point of the orbit must have its global critical
height in an explicit interval of length 2⁻ᴰ above that tolerance. -/
theorem gaussian_missed_budgets :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H := chainGenerator ω k
      ∀ (a e : ℝ) (s : ℕ),
        (∀ t ∈ Icc a (a+(2:ℝ)^(D^C)), HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val t)) →
        (∃ t : ℝ, ¬ HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val t)) →
          criticalHeight H s ∈ Ioc e (e+1/(2:ℝ)^D) := by
  obtain ⟨C,hC⟩ := gaussian_observed_critical_heights
  refine ⟨C,?_⟩
  filter_upwards [hC] with ω hω
  filter_upwards [hω] with k hk
  intro N D H a e s hwindow
  rintro ⟨v,hv⟩
  obtain ⟨z,hz,_,_,hupper⟩ := hk a s
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hwindow z hz)
  have hmiss : e < orbitCircuitDistance H s v := lt_of_not_ge fun h =>
    hv ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h)
  have heglobal : orbitCircuitDistance H s v ≤ criticalHeight H s := by
    obtain ⟨w,hw,hm,hle,_⟩ := hk v s
    exact (hm v ⟨le_rfl,le_add_of_nonneg_right (by positivity)⟩).trans hle
  exact ⟨hmiss.trans_le heglobal,hupper.trans (add_le_add_left hfit _)⟩

#print axioms gaussian_observed_critical_heights
#print axioms gaussian_missed_budgets
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
