import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PhysicalField
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Coordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.LastSpinBlocks

/-! # Tilted product fields and a single directed Pauli coupling on each edge -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Restore the ordinary computational-basis index after a spin extension. -/
def onRegister (n : ℕ) (A : Matrix (Config n⊕Config n) (Config n⊕Config n) ℂ) : Register (n+1) :=
  Matrix.reindex (blockConfig n) (blockConfig n) A

theorem onRegister_add (n : ℕ) (A B : Matrix (Config n⊕Config n) (Config n⊕Config n) ℂ) :
    onRegister n (A+B)=onRegister n A+onRegister n B := rfl

theorem onRegister_smul (n : ℕ) (c : ℂ) (A : Matrix (Config n⊕Config n) (Config n⊕Config n) ℂ) :
    onRegister n (c • A)=c • onRegister n A := rfl

theorem blocks_onRegister (n : ℕ) (A : Matrix (Config n⊕Config n) (Config n⊕Config n) ℂ) :
    blocks n (onRegister n A)=A := by
  ext i j
  simp [blocks,onRegister,Matrix.reindex_apply,Matrix.submatrix_apply]

theorem onRegister_tip (n : ℕ) : onRegister n (tip (Config n))=lastPauli n 0 := by
  apply (Matrix.reindex (blockConfig n).symm (blockConfig n).symm).injective
  change blocks n (onRegister n _)=blocks n (lastPauli n 0)
  rw [blocks_onRegister,lastPauli,blocks_tensor]
  simp [tip,finiteQubitPauli]

/-- In Pauli coordinates the field increments are X on the new site and
Z on the new site coupled to V on the previous register. -/
theorem onRegister_physical (n : ℕ) (H V : Register n) (a d : ℂ) :
    onRegister n (physical H V a d) =
      coupleSnoc n (boolPauliOption none) H + coupleSnoc n (finiteQubitPauli 2) V +
      a • lastPauli n 2+d • lastPauli n 0 := by
  apply (Matrix.reindex (blockConfig n).symm (blockConfig n).symm).injective
  change blocks n (onRegister n _)=blocks n _
  have hsm (c : ℂ) (X : Register (n+1)) : blocks n (c • X)=c • blocks n X := rfl
  rw [blocks_onRegister]
  simp only [blocks_add,hsm,lastPauli,blocks_tensor,boolPauliOption]
  have hz₀ : (2 : Fin 3) ≠ 0 := by decide
  have hz₁ : (2 : Fin 3) ≠ 1 := by decide
  simp [physical,finiteQubitPauli,hz₀,hz₁,fromBlocks_add,fromBlocks_smul,sub_eq_add_neg]

/-- On n+1 sites, all n entries of p are bond strengths. The last transverse
field is left out here and is supplied by the final control in chain. -/
def background : (n : ℕ) → (Fin (n+1) → ℕ) → Controls n → Register (n+1)
  | 0,B,_ => onRegister 0 (physical 0 0 ((3/5)*height (B 0)) ((4/5)*height (B 0)))
  | n+1,B,p => onRegister (n+1) (baseNext (background n (fun i => B i.castSucc))
      (lastPauli n 0) (B (Fin.last (n+1))) (splitControls n p))

/-- The N true controls are one XZ term per bond and one terminal X field. -/
def chain {n : ℕ} (B : Fin (n+1)→ℕ) (p : Controls (n+1)) : Register (n+1) :=
  background n B (splitControls n p).1+(splitControls n p).2 • lastPauli n 0

open scoped Matrix.Norms.Elementwise in
theorem background_analytic (n : ℕ) (B : Fin (n+1)→ℕ) : AnalyticAt ℂ (background n B) 0 := by
  induction n with
  | zero => exact analyticAt_const
  | succ n ih =>
    let H := background n (fun i => B i.castSucc)
    let A := lastPauli n 0
    let h := B (Fin.last (n+1))
    have hg := baseNext_analytic (ih (fun i => B i.castSucc)) A h
    have hs : AnalyticAt ℂ (fun p : Controls (n+1) => baseNext H A h (splitControls n p)) 0 := by
      have hbase : AnalyticAt ℂ (baseNext H A h) (splitControls n 0) := by
        simpa only [map_zero] using hg
      exact hbase.comp (f:=splitControls n) (x:=0) ((splitControls n).analyticAt _)
    apply analyticAt_matrix_of_entries
    intro i j
    exact analyticAt_matrix_entry hs ((blockConfig (n+1)).symm i) ((blockConfig (n+1)).symm j)

theorem relation_onRegister (n : ℕ) (A : Matrix (Config n⊕Config n) (Config n⊕Config n) ℂ) (z : ℂ) :
    matrixCharpolyRelation (onRegister n A,z)=matrixCharpolyRelation (A,z) := by
  simp only [matrixCharpolyRelation,←Matrix.eval_charpoly,onRegister,Matrix.charpoly_reindex]

#print axioms onRegister_physical
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
