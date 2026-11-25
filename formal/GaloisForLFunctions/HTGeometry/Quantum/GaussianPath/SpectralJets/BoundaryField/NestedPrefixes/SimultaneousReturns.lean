import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.PhaseProduct
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.PhaseRectangles

/-! # Exact joint occupation of scalar returns by nested frozen registers -/

open MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
noncomputable section

/-- At the same laboratory time, the scalar-return fractions of all
the nested prefixes multiply exactly, at different errors per prefix
and from every fixed observation origin. -/
theorem gaussian_simultaneous_empty_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (x : Fin n → Icc (0:ℝ) 1) (a : ℝ),
      let H (j : Fin n) : selfAdjoint (Matrix (Config j.val) (Config j.val) ℂ) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (j.val+1)),isSelfAdjoint_pathHamiltonian _⟩
      let B := ⋂ j, zeroGateReturnSet (H j) (x j)
      Tendsto (fun T => volume.real (B ∩ Icc a T)/(T-a)) atTop
        (𝓝 (∏ j, zeroGateArcOccupationPolynomial (2^(j.val+3)) (x j))) := by
  classical
  filter_upwards [gaussian_nested_phase_product] with ω hω
  intro n x a H B
  let r (j : Fin n) : Config j.val := fun _ => false
  let I (j : Fin n) := {i : Config j.val // i≠r j}
  let A (j : Fin n) := relativeEnclosingUnitArc (r j) (x j)
  let E (j : Fin n) := (H j).2.isHermitian.eigenvalues
  let f (z : Sigma I) := projectiveFrequency (fun i => -E z.1 i) (r z.1) z.2
  have ht := (hω n r).2
  let V := rectangle A
  have hA (j : Fin n) := isClosed_relativeEnclosingUnitArc (r j) (x j)
  have hm : MeasurableSet V := (rectangle_closed A hA).measurableSet
  have hf : (finiteTorusHaarProbabilityMeasure (Sigma I) : Measure _) (frontier V)=0 := by
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact rectangle_null_frontier A hA (fun j => volume_frontier_relativeEnclosingUnitArc (r j) (x j))
  have hb : B=finiteClockPhasePoint f ⁻¹' V := by
    ext t
    constructor
    · intro h j
      have hh := mem_iInter.mp h j
      rw [zeroGateReturnSet_eq_preimage_full (H j) (r j) (x j)] at hh
      exact hh
    · intro h
      apply mem_iInter.mpr
      intro j
      rw [zeroGateReturnSet_eq_preimage_full (H j) (r j) (x j)]
      exact h j
  have hmass : volume.real V=∏ j, zeroGateArcOccupationPolynomial (2^(j.val+3)) (x j) := by
    rw [rectangle_mass]
    exact Finset.prod_congr rfl fun j _ => zeroGateFullArcMass_eq_exactPolynomial (j.val+3) (x j)
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht hf
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at he
  have hav := (ENNReal.tendsto_toReal (measure_ne_top volume V)).comp he
  change Tendsto (fun T => (clockPhaseWindowLaw f T : Measure _).real V) atTop (𝓝 (volume.real V)) at hav
  rw [hmass] at hav
  apply tendsto_occupation_from_start B (by rw [hb]; exact hm.preimage (finiteClockPhasePoint_continuous f).measurable)
  apply hav.congr
  intro T
  rw [clockPhaseWindowLaw,Measure.real,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (finiteClockPhasePoint_continuous f).measurable hm,←hb]
  rfl

#print axioms gaussian_simultaneous_empty_returns
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
