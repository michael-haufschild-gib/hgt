import GaloisForLFunctions.HTGeometry.WuSchwartzEnergy
import GaloisForLFunctions.HTGeometry.GaussianSchwartz

/-!
# Wu integration for the corpus's Gaussian and oscillator probes

The all-order Schwartz energy estimate applies to every native polynomial
Gaussian and every native Hermite oscillator state. Thus the same damping
constant controls arbitrary probe degree, derivative order, and spatial moment;
all dependence on the probe remains in its existing Schwartz seminorm.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
noncomputable section

/-- Arbitrary polynomial-Gaussian probes, at every derivative and moment order. -/
theorem polynomial_gaussian_jet_energy_le (p : Polynomial ℝ) (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) • iteratedDeriv n (polyGaussSchwartz p : ℝ → ℂ) s) ≤
      (SchwartzMap.seminorm ℝ k n (polyGaussSchwartz p)) ^ (2 : ℕ) / (2 * Real.exp d) :=
  schwartz_jet_energy_le (polyGaussSchwartz p) k n d t

/-- Every oscillator level inherits the same damping gain with its native normalization. -/
theorem hermite_jet_energy_le (j k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) • iteratedDeriv n (hermiteSchwartz j : ℝ → ℂ) s) ≤
      (SchwartzMap.seminorm ℝ k n (hermiteSchwartz j)) ^ (2 : ℕ) / (2 * Real.exp d) :=
  schwartz_jet_energy_le (hermiteSchwartz j) k n d t

end
end GaloisForLFunctions.HTGeometry.Wu
