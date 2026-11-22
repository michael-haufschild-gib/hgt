import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.PhysicalComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass

/-! # Fixed-draw short-circuit error throughout the initial semicircle -/
open Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- At any signed time the improvement over the empty circuit is limited
by the Gaussian mass of the most favorable support. -/
theorem gaussian_circuit_advantage :
    ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let p := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      ∀ s : ℕ, 0<s → 42*s ≤ Fintype.card (PathLabel n) →
        let r : ℝ := 42*s
        ∀ t : ℝ, orbitCircuitDistance H 0 t ≤ orbitCircuitDistance H s t + 4* |t| * r*sqrt (log (B*N/r)) := by
  obtain ⟨B,hB,hω⟩ := gaussian_subset_mass
  refine ⟨B,hB,?_⟩
  filter_upwards [hω] with ω hh
  filter_upwards [hh] with n hn
  intro N p H s hs hcap r t
  obtain ⟨L,hL,he⟩ := circuit_advantage p s t
  obtain ⟨M,hLM,hm⟩ := Finset.exists_superset_card_eq hL hcap
  have hpos : 0<M.card := by rw [hm]; omega
  have hcard : (M.card:ℝ)=r := by dsimp only [r]; exact_mod_cast hm
  have hh := hn M (Finset.card_pos.mp hpos)
  change (∑ l ∈ M, |p l|)^2 ≤ 4*(M.card:ℝ)^2*log (B*N/M.card) at hh
  rw [hcard] at hh
  have hr : 0≤r := by dsimp [r]; positivity
  have hlog (x : ℝ) : x ≤ (sqrt x)^2 := by
    rcases le_total 0 x with hx | hx
    · rw [sq_sqrt hx]
    · exact hx.trans (sq_nonneg _)
  have hbound : (∑ l ∈ M, |p l|) ≤ 2*r*sqrt (log (B*N/r)) := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun l _ => abs_nonneg _) (by positivity)).mp
    calc
      _ ≤ 4*r^2*log (B*N/r) := hh
      _ ≤ 4*r^2*(sqrt (log (B*N/r)))^2 :=
        mul_le_mul_of_nonneg_left (hlog _) (by positivity)
      _ = _ := by ring
  have hLsum := (Finset.sum_le_sum_of_subset_of_nonneg hLM (fun l _ _ => abs_nonneg (p l))).trans hbound
  change orbitCircuitDistance H 0 t ≤ orbitCircuitDistance H s t+2* |t| * (∑ l ∈ L, |p l|) at he
  apply he.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 2* |t| * (2*r*sqrt (log (B*N/r))) := mul_le_mul_of_nonneg_left hLsum (by positivity)
    _ = _ := by ring

/-- The initial spectral chord bounds every budget from below up to the
Gaussian cost of its most favorable support. -/
theorem gaussian_initial_floor :
    ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let p := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      let W := circuitHamiltonianSpectralWidth H
      ∀ s : ℕ, 0<s → 42*s ≤ Fintype.card (PathLabel n) →
        let r : ℝ := 42*s
        ∀ t : ℝ, 0≤t → t*W ≤ π →
          2*sin (t*W/4) ≤ orbitCircuitDistance H s t + 4*t*r*sqrt (log (B*N/r)) := by
  obtain ⟨B,hB,hω⟩ := gaussian_circuit_advantage
  refine ⟨B,hB,?_⟩
  filter_upwards [hω] with ω hω
  filter_upwards [hω] with n hn
  intro N p H W s hs hcap r t ht hw
  have h := hn s hs hcap t
  rwa [empty_distance H ht hw,abs_of_nonneg ht] at h

#print axioms gaussian_circuit_advantage
#print axioms gaussian_initial_floor
end
end GaloisForLFunctions.HTGeometry.FirstAscent
