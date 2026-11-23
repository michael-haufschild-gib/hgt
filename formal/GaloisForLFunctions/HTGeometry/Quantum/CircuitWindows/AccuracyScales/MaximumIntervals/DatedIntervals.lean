import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.GaussianIntervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.OrbitProfiles

/-! # Absolute deadlines for long intervals at the same-error orbit maximum -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
noncomputable section

/-- Every doubly exponential window contains an actual maximizer at the
regular tolerance. At all offsets of exponentially long duration the cost
still differs from that maximum by at most the stated gate slack. -/
theorem gaussian_dated_same_error_maximum_intervals :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ e ∈ Ioc (0:ℝ) (11/25), e ∉ chainExceptional ω →
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∀ a : ℝ, ∃ z ∈ Icc a (a+(2:ℝ)^((2^N:ℕ)^C)),
            (∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val z) → m ≤ j) ∧
            ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z+t)) →
                m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  obtain ⟨C,hC⟩ := SpectralJets.HighPrecision.gaussian_uniform_profile_recurrence
  refine ⟨C,?_⟩
  filter_upwards [hC,gaussian_frozen_maximum_clearance,LocalPatches.gaussian_exponential_precision_compiler]
    with ω hrep hclear hsim
  intro e he hreg γ α hγ hγα hα
  obtain ⟨c,hc⟩ := hclear e he hreg
  filter_upwards [hrep,hc,hsim (c+1) γ α hγ hγα hα.le,eventually_ge_atTop c,
    eventually_ge_atTop 64] with k hr hk hs hkc h64
  intro N H
  let B := (c+1)*N
  let δ := 1/(2:ℝ)^(c*N)
  let η := 1/(2:ℝ)^B
  let r := 1/(2:ℝ)^(2^N:ℕ)
  have hp : 0 < (2:ℝ)^B := by positivity
  have hbudget : c*N+1 ≤ B := by dsimp [B,N]; rw [Nat.add_mul,one_mul]; omega
  have hsmall : 2*η ≤ δ := by
    change 2*(1/(2:ℝ)^B) ≤ 1/(2:ℝ)^(c*N)
    rw [show 2*(1/(2:ℝ)^B)=2/(2:ℝ)^B by ring,div_le_div_iff₀ hp (by positivity),
      one_mul,←pow_succ' (2:ℝ) (c*N)]
    exact pow_le_pow_right₀ (by norm_num) hbudget
  have hB : B ≤ 2^N := by
    have hh := ReturnExcursions.dimension_dominates_speed (show 64 ≤ N by dsimp [N]; omega)
    have hsq : B ≤ (N+1)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by dsimp [N]; omega) (Nat.le_succ N)
    exact hsq.trans (le_trans (by omega) hh)
  have hrη : r ≤ η := one_div_le_one_div_of_le hp (pow_le_pow_right₀ (by norm_num) hB)
  obtain ⟨m,hmP,hm,hh⟩ := hk
  obtain ⟨v,hv⟩ := required_at_some_date hh
  refine ⟨m,hmP,hm,?_⟩
  intro a
  obtain ⟨z,hz,hz'⟩ := hr a v
  have atCenter (j : ℕ) (hfit : HasProjectiveCircuitApproximation N (e+η) j (unitaryEvolution H.val z)) : m ≤ j := by
    have hd : orbitCircuitDistance H j z ≤ e+η := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit
    have hgap := (abs_le.mp (hz' 0 j)).1
    simp only [add_zero] at hgap
    apply hv j
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    change orbitCircuitDistance H j v ≤ e+δ
    change -r ≤ orbitCircuitDistance H j z-orbitCircuitDistance H j v at hgap
    linarith only [hd,hgap,hsmall,hrη]
  refine ⟨z,hz,?_,?_⟩
  · rintro j ⟨u,hu,J,hJ,herr⟩
    exact atCenter j ⟨u,hu,J,hJ,herr.trans (le_add_of_nonneg_right (one_div_nonneg.mpr hp.le))⟩
  · intro t ht j hfit
    have hh := affordable_add_time H hfit (hs (-t) (by rwa [abs_neg]))
    rw [show z+t+ -t=z by ring] at hh
    exact atCenter _ hh

#print axioms gaussian_dated_same_error_maximum_intervals
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
