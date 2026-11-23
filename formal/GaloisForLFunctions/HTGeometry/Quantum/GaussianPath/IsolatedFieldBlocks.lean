import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.BoxFrequency
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows

/-! # Density of prescribed two-site coefficient boxes along the Gaussian path -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
abbrev PathPauliBlockLabel := Fin 2 × PathPauliDirections

/-- The two consecutive site rows in block k include both bonds incident on site 2k+1. -/
def pathPauliBlock (ω : PathPauliDisorder) (k : ℕ) (i : PathPauliBlockLabel) : ℝ :=
  ω (2*k+i.1.val,i.2)

/-- Any nondegenerate coefficient box in a two-row block occurs with positive
limiting frequency along almost every single infinite Gaussian sample. -/
theorem gaussian_pauli_block_positive_density (lo hi : PathPauliBlockLabel → ℝ)
    (hbox : ∀ i, lo i < hi i) :
    ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      p*m ≤ ((Finset.range m).filter (fun j => ∀ i, pathPauliBlock ω j i ∈ Icc (lo i) (hi i))).card := by
  apply gaussian_disjoint_box_frequency (fun p => (2*p.1+p.2.1.val,p.2.2)) _ lo hi hbox
  rintro ⟨k,i,d⟩ ⟨j,l,e⟩ h
  obtain ⟨he,hd⟩ := Prod.mk.inj h
  change 2*k+i.val=2*j+l.val at he
  have hk : k=j := by have := i.isLt; have := l.isLt; omega
  exact Prod.ext hk (Prod.ext (Fin.ext (by omega)) hd)

#print axioms gaussian_pauli_block_positive_density
end
end GaloisForLFunctions.HTGeometry
