import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Reflections.VariablePrecision
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # All-precision return deadlines from arbitrary physical dates -/
open Filter MeasureTheory Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
open PrecisionReturns (Register)
noncomputable section

/-- From any starting date, the empty circuit succeeds within the all-height
phase horizon, including when the error was chosen from the same draw. -/
theorem gaussian_all_precision_scalar_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε ∈ Ioc (0:ℝ) π, ∀ a : ℝ, ∃ t ∈ Icc a (a+phaseHorizon k ε),
        HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t) := by
  filter_upwards [gaussian_all_precision_phase_clock] with ω hw
  filter_upwards [hw] with k hk
  intro N u H ε hε a
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  exact phase_interval_zero_gate_at_error hε.1.le e H a _ (hk ε hε a)

/-- The first affordable date obeys both an origin-independent deadline and
the Dirichlet bound based on the absolute origin. This includes the first
low-budget return after the original robust crossing. -/
theorem gaussian_any_origin_first_visit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε ∈ Ioc (0:ℝ) π, ∀ a : ℝ, ∀ s : ℕ, let Q := ⌈2*π/ε⌉₊
        PrecisionReturns.firstVisit H a s ε-a ∈
          Icc 0 (min (phaseHorizon k ε) ((|a|+1)*((Q:ℝ)+1)^(2^N-1:ℕ)-a)) := by
  filter_upwards [gaussian_all_precision_scalar_windows] with ω hw
  filter_upwards [hw] with k hk
  intro N u H ε hε a s Q
  have hfirst := PrecisionReturns.firstVisit_isLeast H a s hε.1
  refine ⟨sub_nonneg.mpr hfirst.1.1,le_min ?_ ?_⟩
  · obtain ⟨z,hz,c,hc,C,hC,he⟩ := hk ε hε a
    have hcand := hfirst.2 (show z∈PrecisionReturns.visitSet H a s ε from
      ⟨hz.1,c,hc,C,hC.trans (Nat.zero_le _),he⟩)
    linarith only [hcand,hz.2]
  · let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
    obtain ⟨z,hz,c,hc,C,hC,he⟩ := projective_operator_zero_gate_return_after e H a Q
    have hq := (div_le_iff₀ hε.1).mp (Nat.le_ceil (2*π/ε))
    have herr : 2*π/((Q:ℝ)+1) ≤ ε := by
      apply (div_le_iff₀ (by positivity)).mpr
      change 2*π ≤ (Q:ℝ)*ε at hq
      linarith only [hq,hε.1]
    have hcand := hfirst.2 (show z∈PrecisionReturns.visitSet H a s ε from
      ⟨by linarith only [le_abs_self a,hz.1],c,hc,C,hC.trans (Nat.zero_le _),he.trans herr⟩)
    exact sub_le_sub_right (hcand.trans hz.2) a

#print axioms gaussian_any_origin_first_visit
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
