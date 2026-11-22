import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.IsolatedWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.StrongFieldSites

/-! # Gaussian order statistics delay the first short-circuit exit -/
open MeasureTheory Real Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- On a single draw, s gates cancel at least s√log(N/s)/18 of the
initial inverse-time scale, simultaneously for all budgets in a fixed
positive fraction of the prefix and all initial angular tolerances. -/
theorem gaussian_field_delay :
    ∃ M : ℕ, 0<M ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian _⟩
      let W := circuitHamiltonianSpectralWidth H
      ∀ s : ℕ, 0<s → M*s ≤ N → ∀ θ t : ℝ, θ ≤ π/4 → 0 ≤ t →
        t*(W-(s:ℝ)*sqrt (log ((N:ℝ)/s))/18) ≤ 4*θ →
          HasProjectiveCircuitApproximation N (2*sin θ) s (unitaryEvolution H.val t) := by
  obtain ⟨M,hM,hω⟩ := gaussian_strong_field_sites
  refine ⟨M,hM,?_⟩
  filter_upwards [hω] with ω hω
  filter_upwards [hω] with n hn
  intro N H W s hs hsize θ t hθ ht htime
  obtain ⟨q,hq,hm,S,hS,hgood⟩ := hn s hs hsize
  have hq0 : 0 ≤ q := by linarith only [hq]
  have h := isolated_window (pathPauliDisorderShell ω n) S q 1 (by norm_num)
    (by simpa only [mul_one,abs_of_nonneg hq0] using hq) hgood θ hθ t ht
  rw [hS,abs_of_nonneg hq0] at h
  apply h
  apply (mul_le_mul_of_nonneg_left (sub_le_sub_left _ W) ht).trans htime
  have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg s : (0:ℝ) ≤ s)
  change (s:ℝ)*sqrt (log ((N:ℝ)/s)) ≤ (s:ℝ)*(18*q) at hh
  linarith only [hh]

#print axioms gaussian_field_delay
end
end GaloisForLFunctions.HTGeometry.FirstAscent
