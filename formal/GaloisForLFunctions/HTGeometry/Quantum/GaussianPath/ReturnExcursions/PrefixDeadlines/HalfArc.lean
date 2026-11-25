import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.DifferenceWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates

/-! # Spectral half-arcs bound the first return from its observed scalar occupation -/

open Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
open SharpOccupation
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- Subtracting two visits doubles their angular error and adds their budgets. -/
theorem half_arc_differences {N : ℕ} (H : selfAdjoint (Register N)) (j : ℕ)
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) (t : ℝ) (ht : t∈visitSet H j (zeroGateArcTolerance (x/2)))
    (u : ℝ) (hu : u∈visitSet H j (zeroGateArcTolerance (x/2))) :
    t-u∈visitSet H (j+j) (zeroGateArcTolerance x) := by
  let θ := Real.pi*(x/2)/2
  have hθ : 0≤θ := div_nonneg (mul_nonneg Real.pi_pos.le (div_nonneg hx.1 zero_le_two)) zero_le_two
  have he : 2*θ=Real.pi*x/2 := by dsimp only [θ]; ring
  have hl : 2*θ≤Real.pi/2 := by
    rw [he]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right Real.pi_pos.le hx.2) zero_le_two
  have h := AngularError.affordable_add_angle H (θ:=θ) hθ hl ht (HasProjectiveCircuitApproximation.neg_time H hu)
  rw [he] at h
  change HasProjectiveCircuitApproximation N (2*Real.sin (Real.pi*x/2)) (j+j) (unitaryEvolution H.val (t-u))
  rw [sub_eq_add_neg]
  exact h

/-- Every prefix on the Gaussian chain has a scalar occupation floor at every
observation length. At a first return the intervening affordable time is zero,
so the same floor bounds its date from the scalar time before the origin. -/
theorem gaussian_scalar_residence_deadline :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ ε ∈ Ioo (0:ℝ) 2, let x := physicalArc ε
        let p := zeroGateArcDensity D (x/2)
        (∀ T≥(0:ℝ), p*T≤volume.real (visitSet H 0 ε∩Icc 0 T)) ∧
          ∀ (s : ℕ) (a : ℝ), 0≤a →
            p*firstVisit H a s ε≤volume.real (visitSet H 0 ε∩Icc 0 a) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k N D H ε he x p
  obtain ⟨hx,htol⟩ := FiniteRecords.physicalArc_full he
  have hx' : x∈Icc (0:ℝ) 1 := ⟨hx.1.le,hx.2.le⟩
  let y : Icc (0:ℝ) (1/2) := ⟨x/2,div_nonneg hx.1.le zero_le_two,by linarith only [hx'.2]⟩
  let d := zeroGateArcTolerance y
  have hd : ∀ t∈visitSet H 0 d, ∀ u∈visitSet H 0 d, t-u∈visitSet H 0 ε := by
    intro t ht u hu
    rw [←htol]
    exact half_arc_differences H 0 hx' t ht u hu
  have hl := zero_visitFraction_tendsto H (hω k) y 0
  simp only [visitFraction,sub_zero] at hl
  have bound := density_le_prefix _ _ (closed_visits H 0 d) (closed_visits H 0 ε).measurableSet hd hl
  refine ⟨bound,?_⟩
  intro s a ha
  have hzero := firstVisit_isLeast H a 0 he.1
  have hle : firstVisit H a s ε≤firstVisit H a 0 ε := by
    obtain ⟨c,hc,C,hC,hfit⟩ := hzero.1.2
    exact (firstVisit_isLeast H a s he.1).2 ⟨hzero.1.1,c,hc,C,hC.trans (Nat.zero_le s),hfit⟩
  have hp : 0≤p := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg y.2.1 _)
  have h := bound _ (ha.trans hzero.1.1)
  rw [first_visit_mass H 0 he.1] at h
  exact (mul_le_mul_of_nonneg_left hle hp).trans h

#print axioms gaussian_scalar_residence_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
