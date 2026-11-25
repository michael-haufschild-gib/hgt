import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.FineReturns.PhysicalIndex
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.ContactSpectrum

/-! # The full discrete precision exponent at almost every period of a frozen chain -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
open PrescribedTimes PrecisionReturns ResonantReturns AccuracyScales.MaximumIntervals ShiftedWaits
noncomputable section

/-- A volume-null exceptional set of coupling vectors cuts almost
every ray in a one-dimensional null set of scales. -/
theorem ae_dilations {m : ℕ} {P : (Fin m → ℝ) → Prop} (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂volume, ∀ᵐ τ : ℝ ∂volume, P (τ • x) := by
  obtain ⟨B,hsub,hB,hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hm : MeasurableSet {p : (Fin m → ℝ) × ℝ | p.2 • p.1 ∉ B} :=
    hB.compl.preimage (measurable_snd.smul measurable_fst)
  have hcol : ∀ᵐ τ : ℝ ∂volume, ∀ᵐ x ∂volume, τ • x ∉ B := by
    filter_upwards [Measure.ae_ne volume (0:ℝ)] with τ hτ
    exact (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin m → ℝ)) hτ).ae
      (measure_eq_zero_iff_ae_notMem.mp hnull)
  filter_upwards [(Measure.ae_ae_comm (μ:=volume) (ν:=volume) hm).mpr hcol] with x hx
  filter_upwards [hx] with τ ht
  by_contra h
  exact ht (hsub h)

/-- For each typical frozen chain, almost every positive period has
the full first affordable index exponent on every prefix and at all
budgets below the connected-circuit threshold. -/
theorem gaussian_clock_periods :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ᵐ τ : ℝ ∂volume, 0 < τ →
      ∀ j : ℕ, j+1 < k+3 → Tendsto
        (fun ε => log (firstIndex (chainGenerator ω k) τ j ε)/log (1/ε))
        (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
  have hr (k : ℕ) := ae_dilations (discrete_gap_rate k)
  have H (k : ℕ) :
      ∀ᵐ ω ∂pathPauliDisorderLaw, let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        ∀ᵐ τ : ℝ ∂volume, 0 < τ → Tendsto
          (fun r => log (firstHit (fun i => τ*qubitPathDiscreteFrequency k x i) r)/log (1/r))
          (𝓝[>] (0:ℝ)) (𝓝 ((2^(k+3)-1:ℕ):ℝ)) := by
    have hg : centredProductGaussian (PrefixIndex (k+1)) 1 ≪ volume :=
      productGaussian_absolutelyContinuous _ one_ne_zero _
    filter_upwards [(gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
      (hg.ae_le (hr k))] with ω hω
    intro x
    filter_upwards [hω] with τ ht hτ
    rw [←discrete_frequency_smul k x hτ]
    exact ht
  filter_upwards [ae_all_iff.mpr H,gaussian_sorted_index_comparison] with ω hω hc k
  filter_upwards [hω k] with τ ht hτ
  exact hc k τ _ (ht hτ)

#print axioms gaussian_clock_periods
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
