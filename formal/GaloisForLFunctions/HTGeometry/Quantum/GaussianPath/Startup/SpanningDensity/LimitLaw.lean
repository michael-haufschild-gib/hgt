import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity

/-! # Limit of the actual minimum circuit cost per qubit -/
open Filter Set Matrix Real MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

/-- On one draw, even dates and tolerances selected from that draw obey
the same limit. The lower endpoint requires the number of qubits times
the absolute date to diverge. The upper endpoint includes a fixed small
multiple of the inverse square root of the number of qubits. -/
theorem gaussian_gate_density_limit :
    ∃ b : ℝ, 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ t ε : ℕ→ℝ,
      Tendsto (fun n => |t n| * (n+1:ℕ)) atTop atTop →
      (∀ᶠ n : ℕ in atTop, (t n)^2*(n+2:ℕ)≤b ∧ ε n∈Icc (1/20:ℝ) (1/4)) →
      Tendsto (fun n => ((sInf {j : ℕ | HasProjectiveCircuitApproximation (n+2) (ε n) j
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n))}:ℕ):ℝ)/(n+2:ℕ))
        atTop (𝓝 1) := by
  obtain ⟨b,hb,h⟩ := gaussian_spanning_gate_density
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hω
  intro t ε ht hsmall
  let cost (n : ℕ) := sInf {j : ℕ | HasProjectiveCircuitApproximation (n+2) (ε n) j
    (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n))}
  have hw (k : ℕ) : let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop, (1-8*q)*(n+1:ℕ) ≤ (cost n:ℝ) ∧ cost n≤n+1 := by
    intro q
    have hq : 0<q := by dsimp [q]; positivity
    filter_upwards [hω k,ht.eventually_ge_atTop (π/q^2),hsmall] with n hn hlate hε
    have hL := (div_le_iff₀ (sq_pos_of_pos hq)).mp hlate
    obtain ⟨s,hs,hl,hu⟩ := hn (t n) (by linarith only [hL]) hε.1 (ε n) hε.2
    have he : cost n=s := hs.csInf_eq
    rw [he]
    exact ⟨hl,hu⟩
  change Tendsto (fun n => (cost n:ℝ)/(n+2:ℕ)) atTop (𝓝 1)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k,hk⟩ := exists_nat_gt (9/(1-a))
    let q : ℝ := 1/(k+1:ℕ)
    have hkp : 0<((k+1:ℕ):ℝ) := by positivity
    have hq : a<1-9*q := by
      have he := (div_lt_iff₀ (sub_pos.mpr ha)).mp hk
      have h' : 9/((k+1:ℕ):ℝ)<1-a := (div_lt_iff₀ hkp).mpr (by
        push_cast; nlinarith only [he,ha])
      dsimp only [q]; rw [mul_one_div]; linarith only [h']
    filter_upwards [hw k,eventually_ge_atTop k] with n hn hnk
    have hqn : 1≤q*(n+1:ℕ) := by
      dsimp only [q]; rw [one_div_mul_eq_div,le_div_iff₀ hkp,one_mul]
      exact_mod_cast Nat.add_le_add_right hnk 1
    apply (lt_div_iff₀ (show 0<((n+2:ℕ):ℝ) by positivity)).mpr
    have hh := mul_lt_mul_of_pos_right hq (show 0<((n+2:ℕ):ℝ) by positivity)
    have hlow : (1-8*q)*((n+1:ℕ):ℝ)≤(cost n:ℝ) := hn.1
    have hq0 : 0≤q := by dsimp [q]; positivity
    push_cast at hlow hh hqn ⊢
    linarith only [hlow,hh,hqn,hq0]
  · intro a ha
    filter_upwards [hw 0] with n hn
    apply lt_of_le_of_lt _ ha
    apply (div_le_iff₀ (show 0<((n+2:ℕ):ℝ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast hn.2.trans (by omega : n+1 ≤ n+2)

#print axioms gaussian_gate_density_limit
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
