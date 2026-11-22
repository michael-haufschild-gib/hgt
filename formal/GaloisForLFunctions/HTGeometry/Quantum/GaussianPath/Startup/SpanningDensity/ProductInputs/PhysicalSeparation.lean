import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LimitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.StateError

/-! # Product input tests and the physical operator gate count on the same Gaussian draw -/
open Set Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
noncomputable section

/-- Throughout the intermediate startup window the true gate count per qubit tends
to one. On those same prefixes the empty circuit reproduces every individual
product input with vanishing Euclidean error up to an input-dependent phase. -/
theorem gaussian_product_input_separation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ t : ℕ → ℝ,
      Tendsto (fun n => |t n| * (n+1:ℕ)) atTop atTop →
      Tendsto (fun n => (t n)^2*(n+2:ℕ)) atTop (𝓝 0) →
      Tendsto (fun n => ((sInf {j : ℕ | HasProjectiveCircuitApproximation (n+2) (1/10) j
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n))}:ℕ):ℝ)/(n+2:ℕ))
        atTop (𝓝 1) ∧
      ∀ η : ℝ, 0<η → ∀ᶠ n : ℕ in atTop,
        ∀ (B : Fin (n+2) → Matrix.unitaryGroup Bool ℂ) (x : Bits (n+2)),
          let V := (basisUnitary B).val
          let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n)
          ∃ z : ℂ, ‖z‖=1 ∧ (∑ y, ‖(U*V) y x-z*V y x‖^2) ≤ η^2 := by
  obtain ⟨b,hb,hgate⟩ := gaussian_gate_density_limit
  obtain ⟨_,M,_,hM,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hgate,hbulk] with ω hω hm
  intro t hlate ht
  constructor
  · apply hω t (fun _ => 1/10) hlate
    filter_upwards [ht.eventually_lt_const hb] with n hn
    exact ⟨hn.le,by constructor <;> norm_num⟩
  · intro η hη
    have hp : 0<21*M := by positivity
    filter_upwards [ht.eventually_lt_const (div_pos (sq_pos_of_pos hη) hp),hm] with n hn hn'
    intro B x V U
    obtain ⟨z,hz,he⟩ := product_input_empty_error (pathPauliDisorderShell ω n) (t n) B x
    refine ⟨z,hz,he.trans ?_⟩
    have h := mul_le_mul_of_nonneg_left hn'.2 (show 0≤21*(t n)^2 by positivity)
    have hscale := (lt_div_iff₀ hp).mp hn
    linarith only [h,hscale]

#print axioms gaussian_product_input_separation
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
