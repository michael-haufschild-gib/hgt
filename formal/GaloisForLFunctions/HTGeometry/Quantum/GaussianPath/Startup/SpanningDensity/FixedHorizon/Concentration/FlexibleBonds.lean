import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap

/-! # Neighboring physical sites in a fitting circuit's interaction graph -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Almost all physical neighbors must be inseparable by any circuit
cut. The exceptional bonds are counted jointly over all cut orientations
and the circuit is allowed an arbitrary gate budget. -/
theorem gaussian_uniform_flexible_bonds {a T η κ : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, ∀ C : TwoQubitCircuit (n+2),
      κ≤‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
        (choiVector C.eval.val)‖ → ((flexible C).card:ℝ)<η*(n+1:ℕ) := by
  filter_upwards [gaussian_uniform_cut_overlap (T:=T) ha (half_pos hη) hκ] with ω hω
  filter_upwards [hω] with n hn
  intro t ht C hfit
  obtain ⟨c,hc⟩ := exists_cut_half_flexible C
  have hh : ((flexible C).card:ℝ)≤2*((crossed c).card:ℝ) := by exact_mod_cast hc
  by_contra! h
  exact hn t ht ⟨C,c,by linarith only [h,hh],hfit⟩

#print axioms gaussian_uniform_flexible_bonds
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
