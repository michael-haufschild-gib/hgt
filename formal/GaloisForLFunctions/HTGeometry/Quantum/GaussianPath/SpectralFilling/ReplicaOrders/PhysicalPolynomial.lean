import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.SymmetricPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.AbsoluteDetuning

/-! # Degree and arithmetic normalization of the physical replica obstruction -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open private homogeneous_of_doubling from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ModeDegree
noncomputable section

abbrev Level (k : ℕ) := Fin (2^(k+3))
abbrev Coordinate (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))

/-- Substitute the signed characteristic coefficients of the physical
Pauli matrix into the symmetric replica polynomial. -/
def physical (k q : ℕ) : MvPolynomial (Coordinate k) ℂ :=
  aeval (matrixCharacteristicElementaryPolynomial (spectralGenericMatrix (chainPauliFin (k+3))))
    (coefficient (Level k) q)

theorem physical_eval (k q : ℕ) (x : Coordinate k→ℝ) :
    eval (fun i => (x i:ℂ)) (physical k q)=
      (value (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues q:ℂ) := by
  let P := chainPauliFin (k+3)
  let M := spectralGenericMatrix P
  let hH := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x
  let E := fun i => (hH.eigenvalues i:ℂ)
  let θ := fun i => (x i:ℂ)
  have hc (j) : eval θ (matrixCharacteristicElementaryPolynomial M j)=
      aeval E (esymm (Level k) ℤ (j.val+1)) := by
    change eval₂ (RingHom.id ℂ) θ _=_
    rw [eval_matrixCharacteristicElementaryPolynomial]
    dsimp only [M,θ]
    rw [map_spectralGenericMatrix_eq x]
    apply (matrixCharacteristicElementaryCoefficient_eq_hermitianEigenvalues _ hH j).trans
    rw [←map_esymm (Level k) ℤ (j.val+1) (Int.castRingHom ℚ),eval₂_map,aeval_def]
    congr 1
  change eval θ (aeval (matrixCharacteristicElementaryPolynomial M) (coefficient (Level k) q))=_
  rw [map_aeval]
  simp_rw [hc]
  have hhom : (eval θ).comp (algebraMap ℤ (MvPolynomial (Coordinate k) ℂ))=algebraMap ℤ ℂ :=
    Subsingleton.elim _ _
  rw [hhom,←aeval_eq_eval₂Hom,eval_coefficient]
  simp only [value,gap,E,Complex.ofReal_prod,Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_sum]

theorem physical_ne_zero (k q : ℕ) : physical k q≠0 := by
  obtain ⟨x,hx⟩ := exists_chainShell_maximallyProjective_witness k
  intro hz
  have he := physical_eval k q x
  rw [hz,map_zero] at he
  exact value_ne_zero hx q (Complex.ofReal_injective he.symm)

/-- The number of unequal-multiplicity word pairs is the exact degree. -/
theorem physical_degree (k q : ℕ) : (physical k q).totalDegree=Fintype.card (Pair (Level k) q) := by
  let hP := chainPauliFin_isHermitian (k+3)
  have he (x : Coordinate k→ℝ) : eval (fun i => (x i:ℂ)) (physical k q)=
      (value (sortedEnsembleSpectrum hP x) q:ℂ) :=
    (physical_eval k q x).trans (congrArg Complex.ofReal (value_perm (Tuple.sort
      (isHermitian_spectralEnsembleMatrix hP x).eigenvalues) _ q).symm)
  apply IsHomogeneous.totalDegree _ (physical_ne_zero k q)
  apply homogeneous_of_doubling
  intro x
  have hh := he (fun i => 2*x i)
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at hh
  rw [hh,he,sortedEnsembleSpectrum_const_mul hP (by norm_num : (0:ℝ)<2),value_scale]
  push_cast
  rfl

/-- Integer Pauli entries prevent an arbitrarily small nonzero leading coefficient. -/
theorem physical_head (k q : ℕ) : 1 ≤ ‖lexHeadCoefficient (physical k q)‖ := by
  let N := k+3
  let K := Coordinate k
  let φ := MvPolynomial.map (σ:=K) GaussianInt.toComplex
  obtain ⟨M,hM⟩ := exists_integral_path_pauli_matrix N
  let c (j : Fin (Fintype.card (Level k))) : MvPolynomial K GaussianInt :=
    (-1)^(j.val+1)*M.charpoly.coeff (Fintype.card (Level k)-(j.val+1))
  have hc (j) : φ (c j)=matrixCharacteristicElementaryPolynomial (spectralGenericMatrix (chainPauliFin N)) j := by
    change φ ((-1)^(j.val+1)*M.charpoly.coeff _)=(-1)^(j.val+1)*_
    rw [map_mul,map_pow,map_neg,map_one,←hM,Matrix.charpoly_map,Polynomial.coeff_map]
  let g := aeval c (coefficient (Level k) q)
  have h : φ g=physical k q := by
    dsimp only [g,physical]
    rw [map_aeval,aeval_def]
    simp_rw [hc]
    change eval₂ _ _ _=eval₂ _ _ _
    congr 1
    exact Subsingleton.elim _ _
  obtain ⟨a,ha⟩ := lexHeadCoefficient_is_coeff (physical k q)
  have he : GaussianInt.toComplex (g.coeff a)=lexHeadCoefficient (physical k q) := by rw [←ha,←h,coeff_map]
  have hn := lexHeadCoefficient_ne_zero _ (physical_ne_zero k q)
  rw [←he] at hn ⊢
  exact one_le_gaussianInt_norm _ hn

#print axioms physical_degree
#print axioms physical_head
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
