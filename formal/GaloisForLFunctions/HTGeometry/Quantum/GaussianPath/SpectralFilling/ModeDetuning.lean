import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PolynomialSublevel
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity

/-! # Detuning probability for integer spectral modes of a Gaussian Pauli chain

The product of a balanced energy sum over all permutations is a polynomial in
the Gaussian path coefficients. A spectral width cutoff bounds every factor
except the smallest and gives a tail bound simultaneously over all labelings.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev ChainEnergyIndex (k : ℕ) := Fin (2^(k+3))
private abbrev ChainCoordinate (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))

/-- The unordered product of the mode evaluated on the eigenvalues, expressed
as a polynomial in the physical nearest-neighbour Pauli coefficients. -/
def pauliSpectralModePolynomial (k : ℕ) (m : ChainEnergyIndex k → ℤ) :
    MvPolynomial (ChainCoordinate k) ℂ :=
  complexSpectralCoefficientObstructionPullback
    (matrixCharacteristicElementaryPolynomial (spectralGenericMatrix (chainPauliFin (k+3)))) m

/-- Evaluating the physical polynomial gives the product over every spectral labeling. -/
theorem pauliSpectralModePolynomial_eval (k : ℕ) (m : ChainEnergyIndex k → ℤ)
    (x : ChainCoordinate k → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (pauliSpectralModePolynomial k m) =
      (spectralRelationOrbitValue m (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k+3)) x).eigenvalues : ℂ) := by
  let P := chainPauliFin (k+3)
  let hH := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x
  let M := spectralGenericMatrix P
  have hcoeff (j) :
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (x i : ℂ)) (matrixCharacteristicElementaryPolynomial M j) =
        MvPolynomial.eval₂ (Rat.castHom ℂ) (fun i => (hH.eigenvalues i : ℂ))
          (MvPolynomial.esymm (ChainEnergyIndex k) ℚ (j.val+1)) := by
    rw [eval_matrixCharacteristicElementaryPolynomial]
    dsimp only [M]
    rw [map_spectralGenericMatrix_eq x]
    exact matrixCharacteristicElementaryCoefficient_eq_hermitianEigenvalues _ hH j
  change MvPolynomial.eval₂ (RingHom.id ℂ) _
    (complexSpectralCoefficientObstructionPullback (matrixCharacteristicElementaryPolynomial M) m) = _
  rw [eval_complexSpectralCoefficientObstructionPullback]
  simp_rw [hcoeff]
  rw [eval₂_spectralRelationCoefficientPolynomial_complex_esymm,eval₂_spectralRelationOrbitPolynomial]
  simp only [spectralRelationOrbitValueComplex,spectralRelationOrbitValue,Complex.ofReal_prod,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast]

/-- Maximal projectivity of one Pauli spectrum makes every nonzero balanced
mode polynomial nonzero. -/
theorem pauliSpectralModePolynomial_ne_zero (k : ℕ) (m : ChainEnergyIndex k → ℤ)
    (hbal : SpectralCharacterBalanced m) (hm : m ≠ 0) : pauliSpectralModePolynomial k m ≠ 0 := by
  obtain ⟨x,hx⟩ := exists_chainShell_maximallyProjective_witness k
  intro hz
  have he := pauliSpectralModePolynomial_eval k m x
  rw [hz,map_zero] at he
  exact spectralRelationOrbitValue_ne_zero_of_maximallyProjective _ hx m hbal hm (Complex.ofReal_injective he.symm)

private theorem abs_orbit_le_one_mode {I : Type*} [Fintype I]
    (m : I → ℤ) (E : I → ℝ) (σ : Equiv.Perm I) (R : ℝ) (hE : ∀ i, |E i| ≤ R) :
    |spectralRelationOrbitValue m E| ≤ |∑ i, (m i:ℝ)*E (σ i)| *
      ((∑ i, |(m i:ℝ)|)*R)^(Fintype.card (Equiv.Perm I)-1) := by
  classical
  let F (s : Equiv.Perm I) := |∑ i, (m i:ℝ)*E (s i)|
  let B := (∑ i, |(m i:ℝ)|)*R
  have hF (s) : F s ≤ B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE _) (abs_nonneg _)
  have hrest : ∏ s ∈ Finset.univ.erase σ, F s ≤ B^(Fintype.card (Equiv.Perm I)-1) := by
    refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun s _ => hF s)).trans_eq ?_
    simp
  calc
    |spectralRelationOrbitValue m E| = ∏ s, F s := by simp only [spectralRelationOrbitValue,Finset.abs_prod,F]
    _ = (∏ s ∈ Finset.univ.erase σ, F s)*F σ := (Finset.prod_erase_mul _ _ (Finset.mem_univ σ)).symm
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hrest (abs_nonneg _)

/-- The event that some labeling has a small energy sum at spectral cutoff R.
The factor with exponent D!−1 bounds the other factors of the orbit product. -/
def pauliModeNearResonance (k : ℕ) (m : ChainEnergyIndex k → ℤ) (R r : ℝ) :
    Set (ChainCoordinate k → ℝ) :=
  {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
       let p := pauliSpectralModePolynomial k m
       (∀ i, |E i| ≤ R) ∧ ∃ σ : Equiv.Perm (ChainEnergyIndex k),
         |∑ i, (m i:ℝ)*E (σ i)| * ((∑ i, |(m i:ℝ)|)*R)^(Fintype.card (Equiv.Perm (ChainEnergyIndex k))-1)
           < ‖lexHeadCoefficient p‖*r^p.totalDegree}

/-- For a nonzero balanced mode on the path, the near-resonance probability
is at most 2dr, with d the degree of the physical obstruction polynomial. -/
theorem gaussian_pauli_mode_detuning_sublevel (k : ℕ) (m : ChainEnergyIndex k → ℤ)
    (hbal : SpectralCharacterBalanced m) (hm : m ≠ 0) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (R : ℝ) :
    (Measure.pi fun _ : ChainCoordinate k => gaussianReal 0 1) (pauliModeNearResonance k m R r) ≤
      ENNReal.ofReal (2*(pauliSpectralModePolynomial k m).totalDegree*r) := by
  let p := pauliSpectralModePolynomial k m
  refine (measure_mono ?_).trans (gaussian_mvPolynomial_sublevel p (pauliSpectralModePolynomial_ne_zero k m hbal hm) hr hr')
  rintro x ⟨he,σ,hs⟩
  change ‖MvPolynomial.eval (fun i => (x i : ℂ)) p‖ < _
  rw [show p = pauliSpectralModePolynomial k m from rfl,pauliSpectralModePolynomial_eval,Complex.norm_real,Real.norm_eq_abs]
  exact (abs_orbit_le_one_mode m _ σ R he).trans_lt hs

/-- On the same draw, a finite collection of balanced modes obeys the sum
of their individual near-resonance bounds. -/
theorem gaussian_pauli_finite_mode_detuning_sublevel (k : ℕ) (S : Finset (ChainEnergyIndex k → ℤ))
    (hS : ∀ m ∈ S, SpectralCharacterBalanced m ∧ m ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (R : ℝ) :
    (Measure.pi fun _ : ChainCoordinate k => gaussianReal 0 1)
      (⋃ m ∈ S, pauliModeNearResonance k m R r) ≤
      ∑ m ∈ S, ENNReal.ofReal (2*(pauliSpectralModePolynomial k m).totalDegree*r) :=
  (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun m hm =>
    gaussian_pauli_mode_detuning_sublevel k m (hS m hm).1 (hS m hm).2 hr hr' R)

#print axioms gaussian_pauli_finite_mode_detuning_sublevel
#print axioms gaussian_pauli_mode_detuning_sublevel
end
end GaloisForLFunctions.HTGeometry
