import GaloisForLFunctions.HTGeometry.LinearSpectralRelationOrbitPolynomial
import GaloisForLFunctions.HTGeometry.SpectralRelationOrbitPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Discriminant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ModeDegree

/-! # Absolute detuning bounds for finite packets of path spectral modes

Integer symmetric elimination and Gaussian-integer Pauli entries give unit
lower normalization for every mode polynomial. Homogeneity fixes its degree.
-/
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Symmetric elimination commutes with the inclusion of integers into rationals.
The universal spectral mode polynomial has integer coefficients. -/
theorem integral_spectral_relation_coefficient {I : Type*} [Fintype I] (m : I → ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (linearRelationCoefficient m) = spectralRelationCoefficientPolynomial m := by
  classical
  let φ := Int.castRingHom ℚ
  have hcomm (q : MvPolynomial (Fin (Fintype.card I)) ℤ) :
      (MvPolynomial.esymmAlgHom I ℚ _ (MvPolynomial.map φ q)).val =
        MvPolynomial.map φ (MvPolynomial.esymmAlgHom I ℤ _ q).val := by
    simp only [MvPolynomial.esymmAlgHom_apply,MvPolynomial.aeval_def,MvPolynomial.algebraMap_eq]
    rw [MvPolynomial.eval₂_map,MvPolynomial.hom_eval₂]
    simp only [MvPolynomial.map_esymm]
    congr 1
    ext x
    simp
  apply (MvPolynomial.esymmAlgEquiv I ℚ rfl).injective
  apply Subtype.ext
  change (MvPolynomial.esymmAlgHom I ℚ _ _).val = (MvPolynomial.esymmAlgHom I ℚ _ _).val
  rw [hcomm,esymmAlgHom_linearRelationCoefficient,esymmAlgHom_spectralRelationCoefficientPolynomial]
  unfold linearRelationOrbit spectralRelationOrbitPolynomial
  rw [map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [MvPolynomial.map_rename]
  apply congrArg (MvPolynomial.rename σ)
  simp only [linearRelationPoly,spectralRelationLinearPolynomial,map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,φ,Int.coe_castRingHom]

/-- The physical balanced-mode obstruction has Gaussian-integer coefficients. -/
theorem pauliSpectralModePolynomial_integral (k : ℕ) (m : Fin (2^(k+3)) → ℤ) :
    pauliSpectralModePolynomial k m ∈ (MvPolynomial.map GaussianInt.toComplex).range := by
  let N := k+3
  let D := 2^N
  let K := Fin (Fintype.card (ChainLabel N))
  let φ := MvPolynomial.map (σ := K) GaussianInt.toComplex
  obtain ⟨M,hM⟩ := exists_integral_path_pauli_matrix N
  let c (j : Fin (Fintype.card (Fin D))) : MvPolynomial K GaussianInt :=
    (-1)^(j.val+1)*M.charpoly.coeff (Fintype.card (Fin D)-(j.val+1))
  have hc (j) : φ (c j) =
      matrixCharacteristicElementaryPolynomial (spectralGenericMatrix (chainPauliFin N)) j := by
    change φ ((-1)^(j.val+1)*M.charpoly.coeff _) = (-1)^(j.val+1)*_
    rw [map_mul,map_pow,map_neg,map_one,← hM,Matrix.charpoly_map,Polynomial.coeff_map]
  let q := linearRelationCoefficient m
  refine ⟨MvPolynomial.aeval c q,?_⟩
  change φ (MvPolynomial.aeval c q) = _
  rw [MvPolynomial.map_aeval]
  simp_rw [hc]
  change _ = MvPolynomial.aeval _ (MvPolynomial.map (Rat.castHom ℂ) (spectralRelationCoefficientPolynomial m))
  rw [← integral_spectral_relation_coefficient,MvPolynomial.aeval_def,MvPolynomial.eval₂_map,MvPolynomial.eval₂_map]
  change MvPolynomial.eval₂ _ _ q = MvPolynomial.eval₂ _ _ q
  congr 1
  exact Subsingleton.elim _ _

/-- Calibrated in physical units, every nonzero balanced mode polynomial
has leading coefficient of modulus at least one. -/
theorem one_le_pauliSpectralModePolynomial_lexHead (k : ℕ) (m : Fin (2^(k+3)) → ℤ)
    (hbal : SpectralCharacterBalanced m) (hm : m ≠ 0) : 1 ≤ ‖lexHeadCoefficient (pauliSpectralModePolynomial k m)‖ := by
  obtain ⟨g,hg⟩ := pauliSpectralModePolynomial_integral k m
  obtain ⟨a,ha⟩ := lexHeadCoefficient_is_coeff (pauliSpectralModePolynomial k m)
  have he : GaussianInt.toComplex (g.coeff a) = lexHeadCoefficient (pauliSpectralModePolynomial k m) := by
    rw [← ha,← hg,MvPolynomial.coeff_map]
  have hn := lexHeadCoefficient_ne_zero _ (pauliSpectralModePolynomial_ne_zero k m hbal hm)
  rw [← he] at hn ⊢
  exact one_le_gaussianInt_norm _ hn

/-- Uniform detuning bound in physical energy units for a finite packet on an
N-site Gaussian Pauli path. Each mode includes all D! eigenvalue orderings. -/
theorem gaussian_pauli_finite_mode_absolute_detuning (k : ℕ) (S : Finset (Fin (2^(k+3)) → ℤ))
    (hS : ∀ m ∈ S, SpectralCharacterBalanced m ∧ m ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (R : ℝ) :
    let D := 2^(k+3)
    (Measure.pi fun _ : Fin (Fintype.card (ChainLabel (k+3))) => gaussianReal 0 1)
      {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
           (∀ i, |E i| ≤ R) ∧ ∃ m ∈ S, ∃ σ : Equiv.Perm (Fin D),
             |∑ i, (m i:ℝ)*E (σ i)|*((∑ i, |(m i:ℝ)|)*R)^(D.factorial-1) < r^D.factorial} ≤
      S.card * ENNReal.ofReal (2*((D.factorial:ℕ):ℝ)*r) := by
  let D := 2^(k+3)
  intro _
  refine (measure_mono (t := ⋃ m ∈ S, pauliModeNearResonance k m R r) ?_).trans
    ((gaussian_pauli_finite_mode_detuning_sublevel k S hS hr hr' R).trans_eq ?_)
  · rintro x ⟨hE,m,hm,σ,hs⟩
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,hE,σ,hs.trans_le ?_⟩⟩
    rw [pauliSpectralModePolynomial_totalDegree k m (hS m hm).1 (hS m hm).2]
    exact le_mul_of_one_le_left (pow_nonneg hr.le _) (one_le_pauliSpectralModePolynomial_lexHead k m (hS m hm).1 (hS m hm).2)
  · rw [Finset.sum_congr rfl (fun m hm => congrArg (fun d : ℕ => ENNReal.ofReal (2*(d:ℝ)*r))
        (pauliSpectralModePolynomial_totalDegree k m (hS m hm).1 (hS m hm).2))]
    simp
#print axioms gaussian_pauli_finite_mode_absolute_detuning

end
end GaloisForLFunctions.HTGeometry
