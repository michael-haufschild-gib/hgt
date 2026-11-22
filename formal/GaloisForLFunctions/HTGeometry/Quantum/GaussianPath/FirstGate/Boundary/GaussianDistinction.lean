import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.PhysicalDetector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.EnergySlopes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # One fixed boundary observable distinguishes all Gaussian energy eigenstates -/
open Matrix MvPolynomial Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry.SpectralJets
open GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem distinguishes_shell {n : ℕ} (a : PathShell n)
    (hw : eval₂Hom GaussianInt.toComplex (fun i => (a (pathCoeffEquiv n i):ℂ)) (firstDetector n)≠0) :
    let hH := (isSelfAdjoint_pathHamiltonian a).isHermitian
    let V : Reg (n+2) := hH.eigenvectorUnitary
    let Z : Reg (n+2) := finitePauliMatrix (pauliZLabel (0:Fin (n+2)))
    Function.Injective hH.eigenvalues ∧ Function.Injective (fun j : Fin (n+2)→Bool => ((star V*Z*V) j j).re) := by
  intro hH V Z
  let e := qubitConfigFin (n+2)
  let θ (i) := a (pathCoeffEquiv n i)
  let M := pencil (integralGenerators (n+2))
  let H := numberedBackground n θ
  have he : H=Matrix.reindex e e (pathHamiltonian a) :=
    (numberedBackground_eq n θ).trans (reindex_pathHamiltonian a).symm
  have hh : H.IsHermitian := by rw [he]; exact hH.reindex e
  let E (j : Fin (2^(n+2))) := (hh.eigenvalues j:ℂ)
  have ht (k : ℕ) : eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (M^k).trace=∑ j, E j^k := by
    rw [←trace_mapMatrix,map_pow]
    exact trace_pow_eq_sum_eigenvalues_pow hh k
  have hi := ratioTrace_simple M _ _ GaussianInt.toComplex _ E ht hw
  have hs : H.charpoly.Separable := by rw [hh.charpoly_eq]; exact Polynomial.separable_prod_X_sub_C_iff.mpr hi
  rw [he,Matrix.charpoly_reindex,hH.charpoly_eq] at hs
  have hinj := Polynomial.separable_prod_X_sub_C_iff.mp hs
  have hre : Function.Injective hH.eigenvalues := fun i j hij => hinj (congrArg Complex.ofReal hij)
  obtain ⟨f,hf⟩ := energy_basis_slopes (pathHamiltonian a) Z hH hre
  let g (j : Fin (2^(n+2))) := f (e.symm j)
  have hg (j) : AnalyticAt ℂ (g j) 0 ∧ ∀ᶠ s in 𝓝 0,
      matrixCharpolyRelation (H+s • diagonal (fun i => GaussianInt.toComplex (firstSign n i)),g j s)=0 := by
    refine ⟨(hf _).1,?_⟩
    filter_upwards [(hf (e.symm j)).2.2.1] with s hroot
    rw [he,←reindex_firstZ]
    change matrixCharpolyRelation (Matrix.reindex e e (pathHamiltonian a+s • Z),f (e.symm j) s)=0
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex] using hroot
  have hg₀ : Function.Injective (fun j => g j 0) := by
    intro i j hij
    apply e.symm.injective
    apply hre
    apply Complex.ofReal_injective
    exact (hf (e.symm i)).2.1.symm.trans (hij.trans (hf (e.symm j)).2.1)
  have hd := (slopeDetector_iff M (firstSign n) GaussianInt.toComplex (fun i => (θ i:ℂ)) g hg hg₀).mp hw
  let B := star V*Z*V
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V (finitePauliMatrix_isHermitian _)
  have him (j) : (B j j).im=0 := by
    have h := congrArg Complex.im (hB.apply j j)
    change -(B j j).im=(B j j).im at h
    linarith only [h]
  refine ⟨hre,?_⟩
  intro i j hij
  apply e.injective
  apply hd
  change deriv (f (e.symm (e i))) 0=deriv (f (e.symm (e j))) 0
  rw [e.symm_apply_apply,e.symm_apply_apply,(hf i).2.2.2,(hf j).2.2.2]
  exact Complex.ext hij ((him i).trans (him j).symm)

/-- On a single Gaussian draw, for every prefix of at least two spins, the
expectations of Z at site zero in all its distinct energy eigenstates are
pairwise different. -/
theorem gaussian_simple_firstZ_distinguishes : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
    let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian
    let V : Reg (n+2) := hH.eigenvectorUnitary
    let Z : Reg (n+2) := finitePauliMatrix (pauliZLabel (0:Fin (n+2)))
    Function.Injective hH.eigenvalues ∧ Function.Injective (fun j : Fin (n+2)→Bool => ((star V*Z*V) j j).re) := by
  apply ae_all_iff.mpr
  intro n
  have h := gaussian_ae_of_real_witness GaussianInt.toComplex (firstDetector n) one_ne_zero
    (firstDetector_witness n)
  exact ((gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae h).mono fun ω hω =>
    distinguishes_shell (pathPauliDisorderShell ω n) hω

theorem gaussian_firstZ_distinguishes : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
    let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian
    let V : Reg (n+2) := hH.eigenvectorUnitary
    let Z : Reg (n+2) := finitePauliMatrix (pauliZLabel (0:Fin (n+2)))
    Function.Injective (fun j : Fin (n+2)→Bool => ((star V*Z*V) j j).re) :=
  gaussian_simple_firstZ_distinguishes.mono fun _ hω n => (hω n).2

#print axioms gaussian_firstZ_distinguishes
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
