import GaloisForLFunctions.HTGeometry.PolynomialHermitianMatrixProjectiveGenericity
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Generic maximal projective spectra in polynomial Hermitian families

This file turns coefficient-obstruction genericity into a statement about
the actual ordered eigenvalues of every real-parameter Hermitian matrix
family.  No eigenvalue branch ordering is assumed: the matrix spectral
theorem supplies a canonical real enumeration at each parameter.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Maximal projective independence forces a simple real packet. -/
theorem MaximallyProjectiveEnergy.injective
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) :
    Function.Injective energy := by
  classical
  intro i j hij
  by_contra hne
  let k : I → ℤ :=
    Pi.single i 1 - Pi.single j 1
  have hbalanced :
      SpectralCharacterBalanced k := by
    unfold SpectralCharacterBalanced
    dsimp only [k]
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib,
      Fintype.sum_pi_single',
      Fintype.sum_pi_single',
      ]
    simp
  have hzero :
      (∑ a, (k a : ℝ) * energy a) = 0 := by
    dsimp only [k]
    simp only [Pi.sub_apply, Int.cast_sub]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp [Pi.single_apply, hij]
  have hk := hmax k hbalanced hzero
  have hi := congrFun hk i
  simp [k, hne] at hi

/-- Signed characteristic coefficients of a Hermitian matrix are the
elementary symmetric functions of its canonical real eigenvalue packet,
with multiplicity. -/
theorem
    matrixCharacteristicElementaryCoefficient_eq_hermitianEigenvalues
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (j : Fin (Fintype.card I)) :
    (-1 : ℂ) ^ (j.1 + 1) *
        H.charpoly.coeff
          (Fintype.card I - (j.1 + 1)) =
      MvPolynomial.eval₂ (Rat.castHom ℂ)
        (fun i => (hH.eigenvalues i : ℂ))
        (MvPolynomial.esymm I ℚ (j.1 + 1)) := by
  have hcoefficientIndex :
      Fintype.card I - (j.1 + 1) ≤
        H.charpoly.natDegree := by
    rw [H.charpoly_natDegree_eq_dim]
    omega
  have hvieta :=
    Polynomial.coeff_eq_esymm_roots_of_splits
      (IsAlgClosed.splits H.charpoly)
      (k := Fintype.card I - (j.1 + 1))
      hcoefficientIndex
  rw [H.charpoly_natDegree_eq_dim] at hvieta
  have hdegreeDifference :
      Fintype.card I -
          (Fintype.card I - (j.1 + 1)) =
        j.1 + 1 := by
    omega
  have hesymm :
      H.charpoly.coeff
          (Fintype.card I - (j.1 + 1)) =
        (-1 : ℂ) ^ (j.1 + 1) *
          (Finset.univ.val.map
            (fun i => (hH.eigenvalues i : ℂ))).esymm
              (j.1 + 1) := by
    rw [hH.roots_charpoly_eq_eigenvalues] at hvieta
    simpa [H.charpoly_monic.leadingCoeff,
      hdegreeDifference, Function.comp_apply] using hvieta
  rw [hesymm]
  have hsign :
      (-1 : ℂ) ^ (j.1 + 1) *
          ((-1 : ℂ) ^ (j.1 + 1) *
            (Finset.univ.val.map
              (fun i => (hH.eigenvalues i : ℂ))).esymm
                (j.1 + 1)) =
        (Finset.univ.val.map
          (fun i => (hH.eigenvalues i : ℂ))).esymm
            (j.1 + 1) := by
    rw [← mul_assoc, ← pow_add]
    simp [show (j.1 + 1) + (j.1 + 1) =
        2 * (j.1 + 1) by omega,
      pow_mul]
  rw [hsign, ←
    MvPolynomial.aeval_esymm_eq_multiset_esymm
      I ℚ (j.1 + 1)
      (fun i => (hH.eigenvalues i : ℂ))]
  simp only [MvPolynomial.aeval_def]
  rfl

/-- Membership in the coefficient-obstruction generic set forces the
actual Hermitian eigenvalue packet to be maximally projectively
independent. -/
theorem maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℝ)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet M)
    (hH :
      (M.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ)))).IsHermitian) :
    MaximallyProjectiveEnergy hH.eigenvalues := by
  intro k hbalanced hzero
  by_cases hk : k = 0
  · exact hk
  exfalso
  have hobstruction :=
    hp k hbalanced hk
  rw [
    eval_complexSpectralCoefficientObstructionPullback]
      at hobstruction
  have hcoefficient :
      ∀ j,
        MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun t => (p t : ℂ))
            (matrixCharacteristicElementaryPolynomial M j) =
          MvPolynomial.eval₂ (Rat.castHom ℂ)
            (fun i => (hH.eigenvalues i : ℂ))
            (MvPolynomial.esymm I ℚ (j.1 + 1)) := by
    intro j
    rw [eval_matrixCharacteristicElementaryPolynomial]
    exact
      matrixCharacteristicElementaryCoefficient_eq_hermitianEigenvalues
        _ hH j
  simp_rw [hcoefficient] at hobstruction
  rw [
    eval₂_spectralRelationCoefficientPolynomial_complex_esymm,
    eval₂_spectralRelationOrbitPolynomial]
      at hobstruction
  apply hobstruction
  letI : DecidableEq I := Classical.decEq I
  unfold spectralRelationOrbitValueComplex
  rw [Finset.prod_eq_zero_iff]
  let σ : Equiv.Perm I := Equiv.refl I
  refine ⟨σ, Finset.mem_univ σ, ?_⟩
  change ∑ i, (k i : ℂ) *
    (hH.eigenvalues i : ℂ) = 0
  exact_mod_cast hzero

/-- Real parameters whose actual Hermitian eigenvalue packet has maximal
projective rational rank. -/
def polynomialHermitianMatrixMaximalSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hhermitian :
      ∀ p : Fin m → ℝ,
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).IsHermitian) :
    Set (Fin m → ℝ) :=
  {p |
    MaximallyProjectiveEnergy
      (hhermitian p).eigenvalues}

/-- A canonical Hermitian eigenvalue is a root of the characteristic
relation. -/
theorem hermitianEigenvalue_matrixCharpolyRelation
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (i : I) :
    matrixCharpolyRelation
      (H, (hH.eigenvalues i : ℂ)) = 0 := by
  change
    (Matrix.scalar I (hH.eigenvalues i : ℂ) - H).det = 0
  rw [← Matrix.eval_charpoly, hH.charpoly_eq,
    Polynomial.eval_prod]
  apply Finset.prod_eq_zero
  · exact Finset.mem_univ i
  · simp

/-- **Generic Hermitian spectrum theorem.** In any real-parameter
polynomial Hermitian matrix family, one maximally projective parameter
forces the actual maximally projective spectrum set to be dense, residual,
and full Lebesgue measure. -/
theorem
    polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hhermitian :
      ∀ p : Fin m → ℝ,
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax :
      MaximallyProjectiveEnergy
        (hhermitian p₀).eigenvalues) :
    Dense
        (polynomialHermitianMatrixMaximalSet
          M hhermitian) ∧
      polynomialHermitianMatrixMaximalSet
          M hhermitian ∈
        residual (Fin m → ℝ) ∧
      volume
        (polynomialHermitianMatrixMaximalSet
          M hhermitian)ᶜ = 0 := by
  let H₀ : Matrix I I ℂ :=
    M.map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p₀ t : ℂ)))
  have hH₀ : H₀.IsHermitian :=
    hhermitian p₀
  obtain ⟨hdense, hresidual, hnull⟩ :=
    polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
      M p₀ hH₀.eigenvalues hmax hmax.injective
      (hermitianEigenvalue_matrixCharpolyRelation
        H₀ hH₀)
  have hsubset :
      polynomialMatrixProjectiveGenericSet M ⊆
        polynomialHermitianMatrixMaximalSet
          M hhermitian := by
    intro p hp
    exact
      maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
        M p hp (hhermitian p)
  constructor
  · exact hdense.mono hsubset
  constructor
  · exact Filter.mem_of_superset hresidual hsubset
  · exact measure_mono_null
      (compl_subset_compl.mpr hsubset) hnull

end

end GaloisForLFunctions.HTGeometry
