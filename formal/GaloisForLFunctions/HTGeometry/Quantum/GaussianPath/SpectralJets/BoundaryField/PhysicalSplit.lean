import GaloisForLFunctions.HTGeometry.QubitChainEndpointCompleteness
import GaloisForLFunctions.HTGeometry.PauliChainSpanWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.LastSpinBlocks

/-! # A two-parameter physical path with only one varying onsite field -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
open SpinExtension
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- Append one spin, with longitudinal splitting z and transverse bond uP⊗X. -/
def splitPath {n : ℕ} (H P : Reg n) (z u : ℝ) : Reg (n+1) :=
  reindex (snocConfig n) (snocConfig n)
    (physicalLeafHamiltonian H P (boolShift (z:ℂ)) ((u:ℂ) • layerExchange))

theorem splitPath_mem {n : ℕ} {H P : Reg (n+1)} (hH : H∈pauliChainSpan (n+1))
    (hP : P∈pauliSiteSpan (n+1) (Fin.last n)) (z u : ℝ) :
    splitPath H P z u∈pauliChainSpan (n+2) :=
  physicalLeaf_mem_pauliChainSpan hH hP z (isHermitian_layerExchange.smul (Complex.conj_ofReal u))

/-- Altering z changes only the new boundary Z coefficient. -/
theorem splitPath_shift {n : ℕ} (H P : Reg n) (z u : ℝ) :
    splitPath H P z u=splitPath H P 0 u+((z/2 : ℝ):ℂ) • lastPauli n 2 := by
  have hf (v : ℝ) :
      reindex (snocConfig n) (snocConfig n)
        (layerMatrixCoupling (1 : Reg n) (diagonal (boolShift (v:ℂ))))=((v/2:ℝ):ℂ) • lastPauli n 2 := by
    change coupleSnoc n (diagonal (boolShift (v:ℂ))) 1=_
    rw [diagonal_boolShift_eq,coupleSnoc_smul_right]
    push_cast
    rfl
  have h₀ := hf 0
  simp only [Complex.ofReal_zero,zero_div,zero_smul] at h₀
  simp only [splitPath,physicalLeafHamiltonian,reindex_snocConfig_add',Complex.ofReal_zero,hf,h₀,add_zero]
  abel

/-- The spectral-basis layer pencil and the physical path have the same
characteristic polynomial at every splitting and every real bond strength. -/
theorem splitPath_charpoly {n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (Fin n→Bool) A ℂ) (hl : Uᴴ*U=1) (hr : U*Uᴴ=1)
    (E : A→ℂ) (P : Reg n) (z u : ℝ) :
    (splitPath (U*diagonal E*Uᴴ) P z u).charpoly =
      (diagonal (layerSplitEnergy E (z:ℂ))+(u:ℂ) • layerCrossPerturbation (Uᴴ*P*U)).charpoly := by
  rw [splitPath,Matrix.charpoly_reindex,charpoly_physicalLeafHamiltonian U hl hr]
  rw [layerExchange,localExtensionMatrix_selectedLayer,layeredEnergy_boolShift,selectedLayerCoupling_bool]

#print axioms splitPath_shift
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
