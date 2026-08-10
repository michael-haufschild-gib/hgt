import GaloisForLFunctions.HTGeometry.OneKnobSpectralActivationLaw
import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathGenericityLaw

/-!
# One-knob activation on the local qudit chain

The uniform qudit path carries a physical trace-zero local Hamiltonian whose spectrum is maximally
projective, and that single witness is exactly what the one-knob law consumes.  Along almost every
affine line `A + g V` inside the trace-zero local space, therefore, all but countably many coupling
strengths give maximal projective rational rank — the countable-exception form of generic spectral
activation for the actual nearest-neighbour chain.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- **One-knob activation in a real-affine Hermitian family.** -/
theorem countable_exceptional_coupling_realAffineHermitianMaximalSet
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian) (hgenerator : ∀ t, (generator t).IsHermitian)
    (hne : (realAffineHermitianMaximalSet base generator hbase hgenerator).Nonempty) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          (fun i => av.1 i + g * av.2 i) ∈
            realAffineHermitianMaximalSet base generator hbase hgenerator := by
  obtain ⟨p₀, hp₀⟩ := hne
  exact countable_exceptional_coupling_of_maximallyProjective_witness
    (realAffineMatrixPolynomial base generator) _ p₀ hp₀

/-- **One-knob activation in a Hermitian matrix submodule.** -/
theorem countable_exceptional_coupling_realHermitianSubmoduleMaximalSet
    (L : Submodule ℝ (Matrix I I ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix I I ℂ))
    (hne : (realHermitianSubmoduleMaximalSet L hL).Nonempty) :
    ∀ᵐ av : (Fin (Module.finrank ℝ L) → ℝ) × (Fin (Module.finrank ℝ L) → ℝ)
        ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          (fun i => av.1 i + g * av.2 i) ∈ realHermitianSubmoduleMaximalSet L hL :=
  countable_exceptional_coupling_realAffineHermitianMaximalSet _ _ _ _ hne

/-- **One-knob activation on the uniform qudit path.**  For every chain length `n ≥ 2` and every
local dimension `q ≥ 2` there is a physically realized path system of Hilbert-space dimension
`q ^ n` such that, along almost every affine coupling line inside its trace-zero local
Hamiltonian space, all but countably many coupling strengths have maximal projective rational
rank. -/
theorem exists_uniformQuditPath_countable_exceptional_coupling
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph =
          SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
      (letI : Fintype Z.PhysicalState := Z.physicalFintype
       letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
       let L := Z.tracelessLocalHamiltonianSubmodule
       let hL := Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
       ∀ᵐ av : (Fin (Module.finrank ℝ L) → ℝ) × (Fin (Module.finrank ℝ L) → ℝ)
           ∂(volume.prod volume),
         ∃ C : Set ℝ, C.Countable ∧
           ∀ g ∉ C,
             (fun i => av.1 i + g * av.2 i) ∈
               realHermitianSubmoduleMaximalSet L hL) := by
  obtain ⟨Z, e, hgraph, hstate, hdense, _hresidual, _hnull⟩ :=
    exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure
      n q hn hq
  refine ⟨Z, e, hgraph, hstate, ?_⟩
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact countable_exceptional_coupling_realHermitianSubmoduleMaximalSet _ _
    (hdense.nonempty)

end

end GaloisForLFunctions.HTGeometry
