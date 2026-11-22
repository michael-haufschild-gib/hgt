import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NullFrequencies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CrossingDates

/-! # Null sets of first empty-return dates with a single varying coefficient -/
open Set MeasureTheory Real Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
open PrecisionReturns
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- Every null set of absolute dates misses the first empty visit for
almost every terminal increment. The observation origin may depend on
that increment in an arbitrary way. -/
theorem gaussian_boundary_null_return_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ ε : ℝ, 0<ε → ε<sqrt 2 → ∀ S : Set ℝ, volume S=0 →
      ∀ᵐ z : ℝ, let H : selfAdjoint (Reg (k+3)) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
                ∀ A : ℝ, 0<A → ε<orbitCircuitDistance H 0 A → firstVisit H A 0 ε∉S := by
  filter_upwards [gaussian_boundary_null_frequencies] with ω hω
  intro k ε hε hs S hS
  let U := S ∩ Ioi 0
  let g (n : ℤ) (t : ℝ) := (2*π)*((n:ℝ)+SharpOccupation.physicalArc ε)/t
  have hU : volume U=0 := measure_mono_null inter_subset_left hS
  have hg (n : ℤ) : volume (g n '' U)=0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume _ hU
    intro t ht
    apply DifferentiableAt.differentiableWithinAt
    dsimp only [g]
    fun_prop (disch := exact ht.2.ne')
  filter_upwards [hω k (⋃ n : ℤ, g n '' U) (measure_iUnion_null hg)] with z hz
  intro H A hA hfar hbad
  obtain ⟨hv,m,n,hm,hbal,he⟩ := first_entry_action H hA hε hs hfar
  exact hz m hm hbal (mem_iUnion.mpr ⟨n,firstVisit H A 0 ε,⟨hbad,hv⟩,he.symm⟩)

#print axioms gaussian_boundary_null_return_dates

/-- With all other coefficients held fixed, a null set of dates misses
the first scalar return after the perturbed chain’s own near-Hilbert
crossing for almost every terminal increment. -/
theorem gaussian_boundary_null_crossing_return_dates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∀ S : Set ℝ, volume S=0 →
      ∀ᵐ z : ℝ, let N := k+3
                let H : selfAdjoint (Reg N) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
                let P := nearHilbertContinuousCircuitBudget N
                ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
                  (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧ firstVisit H σ 0 (1/10)∉S := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_boundary_null_return_dates,gaussian_boundary_crossing_return_dates] with ω hd hc
  filter_upwards [hc] with k hk
  intro S hS
  obtain ⟨B,hB,hσ⟩ := hk ∅ countable_empty
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hB.measure_zero volume),
    hd k (1/10) (by norm_num) hs S hS] with z hz hv
  intro N H P
  obtain ⟨σ,hpos,he,hprior,_⟩ := hσ z hz
  refine ⟨σ,hpos,he,hprior,hv σ hpos ?_⟩
  by_contra! h
  obtain ⟨c,hc,Q,hQ,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
  have hp : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
    ⟨c,hc,Q,hQ.trans (Nat.zero_le _),herr⟩
  rw [he] at hp
  norm_num at hp

#print axioms gaussian_boundary_null_crossing_return_dates
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
