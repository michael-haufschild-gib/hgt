import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy
import GaloisForLFunctions.HTGeometry.TorusReplicaMomentBound

/-!
# Removing coefficients through four-corner energy

The coefficient-removal step of Proposition 5.2 of arXiv:2610.03707 bounds
weighted column energy by the squared correlations between rows. Here it is
a rectangular Gram inequality, obtained from Hilbert--Schmidt Cauchy--Schwarz
and the existing source--target Gram duality. Empty matrices and zero
coefficients require no separate assumptions.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HTGeometry

/-- Rectangular Hilbert--Schmidt Cauchy--Schwarz, with arbitrary finite index types. -/
theorem finiteMatrixHilbertSchmidt_pairing_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B : Matrix ι κ ℂ) :
    ‖(Aᴴ * B).trace‖ ^ 2 ≤ finiteMatrixHilbertSchmidtSq A * finiteMatrixHilbertSchmidtSq B := by
  classical
  have hinner : finiteComplexInner (fun p : ι × κ => A p.1 p.2)
      (fun p : ι × κ => B p.1 p.2) = (Aᴴ * B).trace := by
    rw [finiteComplexInner, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simp only [starRingEnd_apply]
  have h := norm_finiteComplexInner_le
    (fun p : ι × κ => A p.1 p.2) (fun p : ι × κ => B p.1 p.2)
  rw [hinner, Fintype.sum_prod_type, Fintype.sum_prod_type,
    ← finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq A,
    ← finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq B] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg ((Aᴴ * B).trace)) h 2
  rwa [mul_pow, Real.sq_sqrt (finiteMatrixHilbertSchmidtSq_nonneg A),
    Real.sq_sqrt (finiteMatrixHilbertSchmidtSq_nonneg B)] at hsq

/-- The cross-Gram energy is bounded by the geometric mean of the two Gram energies. -/
theorem finiteMatrixHilbertSchmidtSq_cross_gram_sq_le
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (A : Matrix ι κ ℂ) (B : Matrix ι ν ℂ) :
    finiteMatrixHilbertSchmidtSq (Aᴴ * B) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) * finiteMatrixHilbertSchmidtSq (Bᴴ * B) := by
  have hreal : finiteMatrixHilbertSchmidtSq (Aᴴ * B) ≤
      ‖((A * Aᴴ) * (B * Bᴴ)).trace‖ := by
    rw [finiteMatrixHilbertSchmidtSq_cross_gram]
    exact Complex.re_le_norm _
  have hs := pow_le_pow_left₀ (finiteMatrixHilbertSchmidtSq_nonneg (Aᴴ * B)) hreal 2
  have hcs := finiteMatrixHilbertSchmidt_pairing_sq_le (A * Aᴴ) (B * Bᴴ)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hcs
  rw [finiteMatrixHilbertSchmidtSq_gram_duality A,
    finiteMatrixHilbertSchmidtSq_gram_duality B]
  exact hs.trans hcs

/-- Sum of squared row correlations, equivalently the four-corner correlation sum. -/
def fourCornerEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ ℂ) : ℝ := finiteMatrixHilbertSchmidtSq (A * Aᴴ)

theorem fourCornerEnergy_eq_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (A : Matrix ι κ ℂ) :
    fourCornerEnergy A = ∑ i, ∑ k, ‖∑ j, A i j * star (A k j)‖ ^ 2 := by
  simp only [fourCornerEnergy, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The same four-corner energy can be read from either side of the matrix. -/
theorem fourCornerEnergy_conjTranspose
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : fourCornerEnergy Aᴴ = fourCornerEnergy A := by
  simp only [fourCornerEnergy, Matrix.conjTranspose_conjTranspose]
  exact finiteMatrixHilbertSchmidtSq_gram_duality A

private def coefficientColumn {κ : Type*} (b : κ → ℂ) : Matrix κ Unit ℂ := fun j _ => b j

private theorem coefficientColumn_gram_energy
    {κ : Type*} [Fintype κ] (b : κ → ℂ) :
    finiteMatrixHilbertSchmidtSq ((coefficientColumn b)ᴴ * coefficientColumn b) =
      (∑ j, ‖b j‖ ^ 2) ^ 2 := by
  have he : (((coefficientColumn b)ᴴ * coefficientColumn b) () ()) =
      ((∑ j, ‖b j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientColumn,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, Fintype.sum_unique,
    he, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Removing the column coefficients costs only their squared ℓ² mass. -/
theorem weightedColumnEnergy_sq_le_fourCornerEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : κ → ℂ) :
    (∑ i, ‖∑ j, A i j * b j‖ ^ 2) ^ 2 ≤
      fourCornerEnergy A * (∑ j, ‖b j‖ ^ 2) ^ 2 := by
  have h := finiteMatrixHilbertSchmidtSq_cross_gram_sq_le Aᴴ (coefficientColumn b)
  rw [Matrix.conjTranspose_conjTranspose, coefficientColumn_gram_energy] at h
  have he : finiteMatrixHilbertSchmidtSq (A * coefficientColumn b) =
      ∑ i, ‖∑ j, A i j * b j‖ ^ 2 := by
    simp only [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, Fintype.sum_unique,
      Matrix.mul_apply, coefficientColumn]
  rw [he] at h
  exact h

/-- Two Cauchy--Schwarz steps remove both coefficient sequences from a bilinear form. -/
theorem norm_bilinear_fourth_le_fourCornerEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    ‖∑ i, a i * ∑ j, A i j * b j‖ ^ 4 ≤
      (∑ i, ‖a i‖ ^ 2) ^ 2 * (∑ j, ‖b j‖ ^ 2) ^ 2 * fourCornerEnergy A := by
  have h := norm_finiteComplexInner_le (fun i => star (a i))
    (fun i => ∑ j, A i j * b j)
  simp only [finiteComplexInner, starRingEnd_apply, star_star, norm_star] at h
  have ha : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : 0 ≤ ∑ i, ‖∑ j, A i j * b j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt he] at hsq
  calc
    ‖∑ i, a i * ∑ j, A i j * b j‖ ^ 4 =
        (‖∑ i, a i * ∑ j, A i j * b j‖ ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i, ‖a i‖ ^ 2) * (∑ i, ‖∑ j, A i j * b j‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hsq 2
    _ = (∑ i, ‖a i‖ ^ 2) ^ 2 * (∑ i, ‖∑ j, A i j * b j‖ ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (∑ i, ‖a i‖ ^ 2) ^ 2 * (fourCornerEnergy A * (∑ j, ‖b j‖ ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (weightedColumnEnergy_sq_le_fourCornerEnergy A b) (sq_nonneg _)
    _ = _ := by ring

#print axioms finiteMatrixHilbertSchmidtSq_cross_gram_sq_le
#print axioms weightedColumnEnergy_sq_le_fourCornerEnergy
#print axioms norm_bilinear_fourth_le_fourCornerEnergy

end GaloisForLFunctions.HTGeometry
