import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.IsolatedWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity

/-! # Sublinear gate budgets delay the initial exit on a fixed Gaussian chain -/
open Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- For every prescribed width reduction k per gate there is a positive
density of sites realizing it. One draw and every sufficiently long prefix
work at once for all smaller budgets, times and initial angular tolerances. -/
theorem gaussian_isolated_windows :
    ∃ ρ : ℕ→ℝ, (∀ k, 0<ρ k) ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian _⟩
      let W := circuitHamiltonianSpectralWidth H
      ∀ s : ℕ, (s:ℝ) ≤ ρ k*N → ∀ θ t : ℝ, θ≤π/4 → 0≤t → t*(W-(k:ℝ)*s)≤4*θ →
        HasProjectiveCircuitApproximation N (2*sin θ) s (unitaryEvolution H.val t) := by
  classical
  let q (k : ℕ) : ℝ := k+126
  choose ρ hp hh using fun k => gaussian_path_eventual_isolated_sites (q k) 1 (by norm_num)
  refine ⟨ρ,hp,?_⟩
  filter_upwards [ae_all_iff.mpr hh] with ω hs k
  filter_upwards [hs k] with n hn
  intro N H W s hsize θ t hθ ht htime
  obtain ⟨S,hcard,hgood⟩ := hn
  have hc : s ≤ S.card := by exact_mod_cast hsize.trans hcard
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq hc
  have hq : 0≤q k := by dsimp [q]; positivity
  have hk : (k:ℝ) ≤ q k := by dsimp [q]; linarith
  have h := isolated_window (pathPauliDisorderShell ω n) T (q k) 1 (by norm_num)
    (by rw [abs_of_nonneg hq]; dsimp [q]; linarith only [Nat.cast_nonneg (α := ℝ) k])
    (fun i hi => hgood i (hTS hi)) θ hθ t ht
  rw [hT,abs_of_nonneg hq] at h
  apply h
  change t*(W-(s:ℝ)*q k) ≤ 4*θ
  apply (mul_le_mul_of_nonneg_left (sub_le_sub_left _ W) ht).trans htime
  simpa only [mul_comm (k:ℝ) (s:ℝ)] using mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg s)

#print axioms gaussian_isolated_windows
end
end GaloisForLFunctions.HTGeometry.FirstAscent
