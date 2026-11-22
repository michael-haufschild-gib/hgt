import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Gate density in the neighborhood of actual low-complexity visits -/
open Filter Set Matrix Real MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Both signed sides of every visit obey the bond-density bounds after
subtracting or adding its gate budget. The estimates hold simultaneously
for all visits, lag times and allowed error margins. -/
theorem gaussian_spanning_gate_density_around_visits :
    ∃ b : ℝ, 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop,
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∀ t : ℝ, π ≤ |t| * q^2*(n+1:ℕ) → t^2*(n+2:ℕ) ≤ b →
        ∀ (v α ε : ℝ) (s : ℕ), α+1/20≤ε → α+ε≤1/4 →
          HasProjectiveCircuitApproximation (n+2) α s (unitaryEvolution H v) →
          ∃ r : ℕ, IsLeast {j | HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H (v+t))} r ∧
            (1-8*q)*(n+1:ℕ) ≤ (s:ℝ)+r ∧ r ≤ s+(n+1) := by
  classical
  obtain ⟨b,hb,h⟩ := gaussian_spanning_gate_density
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hω k
  intro q
  filter_upwards [hω k] with n hn
  let H : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  intro _ t hlate hsmall v α ε s hε hsum hv
  obtain ⟨a,ha,_,hac⟩ := hn t hlate hsmall (1/20) (by constructor <;> norm_num)
  obtain ⟨d,hd,hdc,_⟩ := hn t hlate hsmall (1/4) (by constructor <;> norm_num)
  let afford (j : ℕ) := HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H.val (v+t))
  have hfit : afford (s+a) := by
    obtain ⟨z,hz,C,hC,he⟩ := affordable_add_time H hv ha.1
    exact ⟨z,hz,C,hC,he.trans hε⟩
  have hex : ∃ j, afford j := ⟨_,hfit⟩
  let r := Nat.find hex
  have hr : afford r := Nat.find_spec hex
  have hinc := affordable_add_time H (hv.neg_time H) hr
  rw [neg_add_cancel_left] at hinc
  obtain ⟨z,hz,C,hC,he⟩ := hinc
  have hc := hd.2 (show s+r∈{j | HasProjectiveCircuitApproximation (n+2) (1/4) j
    (unitaryEvolution H.val t)} from ⟨z,hz,C,hC,he.trans hsum⟩)
  exact ⟨r,⟨hr,fun _ hj => Nat.find_min' hex hj⟩,hdc.trans (by exact_mod_cast hc),
    (Nat.find_min' hex hfit).trans (Nat.add_le_add_left hac _)⟩

/-- At the prescribed error 1/10 on both endpoints, two affordable
circuits must together pay the whole limiting bond density of their lag.
The first endpoint may be the first low-complexity return after a crossing. -/
theorem gaussian_spanning_two_visits :
    ∃ b : ℝ, 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop,
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∀ t : ℝ, π ≤ |t| * q^2*(n+1:ℕ) → t^2*(n+2:ℕ) ≤ b →
        ∀ (v : ℝ) (s r : ℕ),
          HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H (v+t)) →
          (1-8*q)*(n+1:ℕ) ≤ (s:ℝ)+r := by
  obtain ⟨b,hb,h⟩ := gaussian_spanning_gate_density
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hω k
  intro q
  filter_upwards [hω k] with n hn
  let H : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  intro _ t hlate hsmall v s r hs hr
  obtain ⟨a,ha,hfloor,_⟩ := hn t hlate hsmall (1/10+1/10) (by constructor <;> norm_num)
  have hinc := affordable_add_time H (hs.neg_time H) hr
  rw [neg_add_cancel_left] at hinc
  exact hfloor.trans (by exact_mod_cast ha.2 hinc)

/-- In particular, both sides of the first scalar visit at error 1/20
from any origin have unit limiting gate density at the fixed error 1/10. -/
theorem gaussian_spanning_gate_density_first_scalar :
    ∃ b : ℝ, 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ᶠ n : ℕ in atTop,
        let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        ∀ t : ℝ, π ≤ |t| * q^2*(n+1:ℕ) → t^2*(n+2:ℕ) ≤ b →
        ∀ origin : ℝ, let v := PrecisionReturns.firstVisit H origin 0 (1/20)
          ∃ r : ℕ, IsLeast {j | HasProjectiveCircuitApproximation (n+2) (1/10) j
              (unitaryEvolution H.val (v+t))} r ∧ (1-8*q)*(n+1:ℕ) ≤ r ∧ r≤n+1 := by
  obtain ⟨b,hb,h⟩ := gaussian_spanning_gate_density_around_visits
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hω k
  intro q
  filter_upwards [hω k] with n hn
  intro H t hlate hsmall origin v
  simpa only [Nat.cast_zero,zero_add] using hn t hlate hsmall v (1/20) (1/10) 0
    (by norm_num) (by norm_num) (PrecisionReturns.firstVisit_isLeast H origin 0 (by norm_num : 0<(1/20:ℝ))).1.2

#print axioms gaussian_spanning_gate_density_first_scalar
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
