import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # A uniform affordable fraction bound up to physical error one eighth -/

open Filter Set MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
open SharpOccupation
noncomputable section

/-- At every error at most one eighth and budget at most P, on every
nonconstant affine lattice, sufficiently long prefixes have affordable
fraction below 16^(-2^N). -/
theorem gaussian_lattice_eighth_upper :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a τ : ℝ, τ≠0 → ∀ᶠ M : ℕ in atTop, ∀ s≤nearHilbertContinuousCircuitBudget N,
        ∀ ε≤(1/8:ℝ), (timeLaw a τ M).real (visitSet H s ε)<1/((16^(2^N):ℕ):ℝ) := by
  let x : ℝ := 1/24
  have htol : 1/8 ≤ zeroGateArcTolerance x := (by norm_num [x] : 1/8≤3*x).trans
    (three_mul_le_arcTolerance (by norm_num [x]) (by norm_num [x]))
  have hlog : log x+32*log 2/(64:ℕ)<log (1/16) := by
    have hh := log_lt_log (by norm_num [x] : 0<x^2*2) (by norm_num [x] : x^2*2<(1/16:ℝ)^2)
    rw [log_mul (by norm_num [x]) (by norm_num),log_pow,log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  filter_upwards [gaussian_hilbert_budget] with ω hu
  filter_upwards [hu 64 (by decide) x (by constructor <;> norm_num [x]) (1/16) (by norm_num) hlog] with k hk
  intro N H a τ hτ
  filter_upwards [hk a τ hτ] with M hm s hs ε hε
  have hsub : visitSet H s ε ⊆ visitSet H s (zeroGateArcTolerance x) := by
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨z,hz,C,hC,he.trans (hε.trans htol)⟩
  apply (measureReal_mono (μ:=timeLaw a τ M) hsub).trans_lt
  simpa only [one_div,inv_pow,Nat.cast_pow,Nat.cast_ofNat] using hm s hs

#print axioms gaussian_lattice_eighth_upper
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
