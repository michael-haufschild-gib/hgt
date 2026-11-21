import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.LongitudinalRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.TraceAtBackground
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.PauliDetector

/-! # A nonzero longitudinal trace polynomial on the physical Gaussian coupling space -/
open Matrix Filter Topology MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

def physicalWords (n : ℕ) (a : Fin (2^(n+1))) :=
  maskWord ((qubitConfigFin (n+1)).symm a)

def spinCoefficient (N : ℕ) (j : Fin (2^N)) (i : Fin N) : GaussianInt :=
  if (qubitConfigFin N).symm j i then -1 else 1

theorem spinCoefficient_cast (N : ℕ) (j : Fin (2^N)) :
    GaussianInt.toComplex ∘ spinCoefficient N j = spinVector ((qubitConfigFin N).symm j) := by
  funext i
  cases h : (qubitConfigFin N).symm j i <;> simp [spinCoefficient,spinVector,Walsh.boolSign,h]

/-- Numbered Gaussian-integer trace polynomial for one choice of monomial columns. -/
def physicalTrace (n : ℕ) (k : Fin (2^(n+1)) → Fin (2^(n+2))) :=
  fieldTraceMinor (pencil (integralGenerators (n+2))) (spinCoefficient (n+2)) (physicalWords n)
    (n+1+(n+1)%2) k

def numberedBackground (n : ℕ) (θ : Coordinates (n+2) → ℝ) :=
  (eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ))).mapMatrix (pencil (integralGenerators (n+2)))

theorem numberedBackground_eq (n : ℕ) (θ : Coordinates (n+2) → ℝ) :
    numberedBackground n θ = spectralEnsembleMatrix (chainPauliFin (n+2)) θ := by
  rw [numberedBackground,eval_pencil]
  simp only [generators_map,spectralEnsembleMatrix]

private theorem char_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (H : Matrix I I ℂ) (z : ℂ) :
    matrixCharpolyRelation (Matrix.reindex e e H,z) = matrixCharpolyRelation (H,z) := by
  simp only [matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex]

theorem physicalTrace_witness (n : ℕ) :
    ∃ k, ∃ θ : Coordinates (n+2) → ℝ,
      eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (physicalTrace n k) ≠ 0 := by
  classical
  obtain ⟨v,hs,f,hf,hi,hm⟩ := (longitudinal_rank_right n).exists
  let e := qubitConfigFin (n+2)
  let a := qubitConfigFin (n+1)
  let θ (i) := splitShell n v (pathCoeffEquiv n i)
  let H := numberedBackground n θ
  have he : H=Matrix.reindex e e (pathHamiltonian (splitShell n v)) :=
    (numberedBackground_eq n θ).trans (reindex_pathHamiltonian _).symm
  have hH : H.IsHermitian := by
    rw [he]
    exact (isSelfAdjoint_pathHamiltonian _).isHermitian.reindex e
  have hs' : H.charpoly.Separable := by rw [he,Matrix.charpoly_reindex]; exact hs
  let u (j : Fin (2^(n+2))) := GaussianInt.toComplex ∘ spinCoefficient (n+2) j
  have hmat (h : Fin (n+2) → ℂ) : H+diagonal (fun j => fieldEnergy (u j) h) =
      Matrix.reindex e e (fieldHamiltonian n v h) := by
    rw [he]
    apply Matrix.ext
    intro i j
    change pathHamiltonian (splitShell n v) (e.symm i) (e.symm j) + diagonal _ i j =
      pathHamiltonian (splitShell n v) (e.symm i) (e.symm j) + diagonal _ (e.symm i) (e.symm j)
    apply congrArg (pathHamiltonian (splitShell n v) (e.symm i) (e.symm j)+·)
    by_cases hij : i=j
    · subst j; simp only [Matrix.diagonal_apply_eq,u,spinCoefficient_cast]; rfl
    · rw [Matrix.diagonal_apply_ne _ hij,Matrix.diagonal_apply_ne _ (e.symm.injective.ne hij)]
  have hr : hasFieldMinor H u (physicalWords n) := by
    refine ⟨fun j => f (a.symm j),fun j => ⟨(hf _).1,?_⟩,hi.comp a.symm.injective,?_⟩
    · filter_upwards [(hf (a.symm j)).2] with h hh
      rwa [hmat,char_reindex]
    · rw [←Matrix.det_reindex_self a (Matrix.of fun i j => mixed (maskWord i) (f j) 0)] at hm
      exact hm
  obtain ⟨k,hk⟩ := (fieldTrace_iff (pencil (integralGenerators (n+2))) (spinCoefficient (n+2))
    (physicalWords n) _ (fun j => maskWord_length _) GaussianInt.toComplex (fun i => (θ i:ℂ)) hH hs').mpr hr
  exact ⟨k,θ,hk⟩

theorem physicalTrace_nonzero (n : ℕ) :
    ∃ k, MvPolynomial.map GaussianInt.toComplex (physicalTrace n k) ≠ 0 := by
  obtain ⟨k,θ,hk⟩ := physicalTrace_witness n
  refine ⟨k,fun hz => hk ?_⟩
  change eval₂ GaussianInt.toComplex (fun i => (θ i:ℂ)) (physicalTrace n k)=0
  rw [←eval_map,hz,map_zero]

#print axioms physicalTrace_nonzero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
