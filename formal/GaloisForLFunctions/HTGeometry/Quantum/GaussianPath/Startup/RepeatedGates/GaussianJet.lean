import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.DoubleBracket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # A physical second-order signalling witness transfers to Gaussian disorder -/
open Matrix MeasureTheory MvPolynomial
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section
private abbrev Mat (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- Expand only the two occurrences of the generator. Coefficients of
the resulting quadratic form are fixed triple commutators. -/
private theorem signal₂_sum {n : ℕ} {I : Type*} [Fintype I]
    (A B : Mat n) (X : I→Mat n) (u : I→ℂ) :
    signal₂ A B (∑ i, u i • X i) =
      ∑ i, ∑ j, (u i*u j) • bracket (bracket (bracket A (X i)) (X j)) B := by
  have expandL (L : I→Mat n) (H : Mat n) : bracket (∑ i, L i) H=∑ i, bracket (L i) H := by
    rw [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]; rfl
  have expandR (L : I→Mat n) (H : Mat n) : bracket H (∑ i, L i)=∑ i, bracket H (L i) := by
    rw [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]; rfl
  have scaleL (c : ℂ) (K H : Mat n) : bracket (c • K) H=c • bracket K H := by
    rw [bracket,bracket,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  have scaleR (c : ℂ) (K H : Mat n) : bracket K (c • H)=c • bracket K H := by
    rw [bracket,bracket,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  simp only [signal₂,expandL,expandR,scaleL,scaleR,smul_smul]

/-- A single real generator with a nonzero signal suffices. The test
imposes no condition on the random generator. -/
theorem gaussian_signal₂_of_witness {n : ℕ} (A B : Mat (n+2)) (w : PathShell n)
    (hw : signal₂ A B (pathHamiltonian w) ≠ 0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, signal₂ A B (pathHamiltonian (pathPauliDisorderShell ω n)) ≠ 0 := by
  classical
  obtain ⟨r,s,hrs⟩ : ∃ r s, signal₂ A B (pathHamiltonian w) r s ≠ 0 := by
    by_contra! h; exact hw (Matrix.ext fun r s => h r s)
  let d := Fintype.card (ChainLabel (n+2))
  let e := pathCoeffEquiv n
  let M (i : Fin d) := finitePauliMatrix (pathWord (e i))
  let K (i j : Fin d) := bracket (bracket (bracket A (M i)) (M j)) B r s
  let P : MvPolynomial (Fin d) ℂ := ∑ i, ∑ j, X i*X j*C (K i j)
  have he (u : PathShell n) :
      eval₂Hom (RingHom.id ℂ) (fun i => (u (e i):ℂ)) P=signal₂ A B (pathHamiltonian u) r s := by
    have hH : pathHamiltonian u=∑ i : Fin d, (u (e i):ℂ) • M i := by
      rw [pathHamiltonian_eq_sum]; exact (e.sum_comp _).symm
    rw [hH,signal₂_sum]
    simp only [P,map_sum,map_mul,eval₂Hom_X',eval₂Hom_C,RingHom.id_apply,
      Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,K]
  have h := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae
    (SpectralJets.gaussian_ae_of_real_witness (RingHom.id ℂ) P (v:=1) one_ne_zero
      ⟨fun i => w (e i),by rw [he w]; exact hrs⟩)
  filter_upwards [h] with ω hω
  intro hz
  apply hω
  change eval₂Hom (RingHom.id ℂ) (fun i => ((pathPauliDisorderShell ω n) (e i):ℂ)) P=0
  rw [he,hz]; rfl

end
end GaloisForLFunctions.HTGeometry.RepeatedGates
