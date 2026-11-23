import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.GaussianWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.LogarithmicMesh

/-! # Trace dephasing from inverse-root onset through logarithmic time -/
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- An inverse-root onset and a logarithmic horizon hold simultaneously
for every physical date on the same frozen prefix. -/
theorem gaussian_logarithmic_startup_trace {κ : ℝ} (hκ : 0 < κ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) (Nat.log b n : ℝ), A ≤ (n+2:ℕ)*t^2 → ‖amplitude ω n t‖ < κ := by
  obtain ⟨A,hA,hshort⟩ := Bulk.gaussian_startup_trace hκ
  obtain ⟨b,hb,hfar⟩ := SpanningDensity.FixedHorizon.logarithmic_cut_window
    (a:=1) zero_lt_one (by norm_num : (0:ℝ)<1/2) hκ
  refine ⟨b,hb,A,hA,?_⟩
  filter_upwards [hshort,hfar] with ω hω hw
  filter_upwards [hω,hw] with n hn hf
  intro t ht h
  by_cases hs : t ≤ 1
  · exact hn t h (by rwa [abs_of_nonneg ht.1])
  · exact trace_lt_of_no_cut_event (hf t ⟨le_of_not_ge hs,ht.2⟩)

/-- Shrinking a logarithmic time window by a fixed harmonic order only
changes the logarithm's base. -/
theorem harmonic_log_bound (b k n : ℕ) : k*Nat.log (b^k) n ≤ Nat.log b n := by
  rw [Nat.log_pow_left,mul_comm]
  exact Nat.div_mul_le_self ..

/-- Any prescribed finite set of harmonics fits within the same trace
estimate after changing the base of the logarithmic horizon. -/
theorem gaussian_harmonic_trace_window (k : ℕ) (hk : 0 < k) {κ : ℝ} (hκ : 0 < κ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc (0:ℝ) ((k:ℝ)*Nat.log b n), A ≤ (n+2:ℕ)*t^2 → ‖amplitude ω n t‖ < κ := by
  obtain ⟨b,hb,A,hA,h⟩ := gaussian_logarithmic_startup_trace hκ
  refine ⟨b^k,hb.trans (le_self_pow₀ (by omega) hk.ne'),A,hA,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t ht hm
  exact hn t ⟨ht.1,ht.2.trans (by exact_mod_cast harmonic_log_bound b k n)⟩ hm

#print axioms gaussian_logarithmic_startup_trace
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
