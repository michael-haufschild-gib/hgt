import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodKernel
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import Mathlib.Analysis.Matrix.Order

/-!
# Exact finite Gram determinants of prime likelihoods

The centered likelihood Gram matrix is a multiplicative Cauchy matrix.
The Cayley coordinate `(p+1)/(p-1)` reduces its determinant to the existing
additive Cauchy determinant. It factors into the diagonal variances and
squared pairwise ratios `(p-q)/(pq-1)`. Distinct primes therefore give
strictly positive Gram determinants.
-/

open MeasureTheory Matrix Finset
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Actual semicircle Gram matrix of a finite family of centered prime likelihoods. -/
def kestenLikelihoodGram {n : ℕ} (p : Fin n → Nat.Primes) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, (kestenLikelihood (p i) x - 1) * (kestenLikelihood (p j) x - 1)
    ∂(semicircleSpectralLaw : Measure ℝ)

/-- Every entry is the multiplicative Cauchy kernel. -/
theorem kestenLikelihoodGram_apply {n : ℕ} (p : Fin n → Nat.Primes) (i j : Fin n) :
    kestenLikelihoodGram p i j = ((p i : ℝ) * (p j : ℝ) - 1)⁻¹ :=
  integral_semicircleLikelihood_centered_mul (p i) (p j)

/-- The finite likelihood quadratic form is the actual squared semicircle norm. -/
theorem kestenLikelihoodGram_quadratic_form {n : ℕ} (p : Fin n → Nat.Primes) (c : Fin n → ℝ) :
    (∑ i, ∑ j, c i * c j * kestenLikelihoodGram p i j) =
      ∫ x, (∑ i, c i * (kestenLikelihood (p i) x - 1)) ^ 2
        ∂(semicircleSpectralLaw : Measure ℝ) := by
  have he (x : ℝ) : (∑ i, c i * (kestenLikelihood (p i) x - 1)) ^ 2 =
      ∑ i, ∑ j, c i * c j * ((kestenLikelihood (p i) x - 1) * (kestenLikelihood (p j) x - 1)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin n) : Integrable (fun x => c i * c j *
      ((kestenLikelihood (p i) x - 1) * (kestenLikelihood (p j) x - 1)))
        (semicircleSpectralLaw : Measure ℝ) := integrable_semicircleSpectralLaw_continuous
    ⟨_, continuous_const.mul (((continuous_kestenLikelihood (p i)).sub continuous_const).mul
      ((continuous_kestenLikelihood (p j)).sub continuous_const))⟩
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  rfl

/-- Every finite centered-likelihood Gram matrix is positive semidefinite. -/
theorem kestenLikelihoodGram_posSemidef {n : ℕ} (p : Fin n → Nat.Primes) :
    (kestenLikelihoodGram p).PosSemidef := by
  refine ⟨?_, fun c => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, kestenLikelihoodGram_apply]
    rw [mul_comm]
  · have he : (c.sum fun i ci => c.sum fun j cj => star ci * kestenLikelihoodGram p i j * cj) =
        ∑ i, ∑ j, c i * c j * kestenLikelihoodGram p i j := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [star_trivial]
      ring
    rw [he, kestenLikelihoodGram_quadratic_form]
    exact integral_nonneg fun x => sq_nonneg _

private theorem symmetric_double_product {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∏ i, ∏ j, f i j) = (∏ i, f i i) * ∏ i, ∏ j ∈ Ioi i, f i j ^ 2 := by
  have he : (∏ i, ∏ j ∈ Ioi i, f i j ^ 2) = ∏ i, ∏ j ∈ ({i}ᶜ : Finset (Fin n)), f j i := by
    rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    rw [hf j i, pow_two]
  rw [he, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]
  have h := Finset.prod_compl_mul_prod ({i} : Finset (Fin n)) (fun j => f j i)
  simpa only [Finset.prod_singleton, hf] using h.symm

private theorem cauchy_self_det_product {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    (cauchyMatrix u u).det = (∏ i, (2 * u i)⁻¹) *
      ∏ i, ∏ j ∈ Ioi i, ((u i - u j) / (u i + u j)) ^ 2 := by
  have hD := symmetric_double_product (fun i j => u i + u j) (fun i j => add_comm _ _)
  have hdiag : (∏ i, 2 * u i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (mul_pos (by norm_num) (hu i)).ne'
  have hoff : (∏ i, ∏ j ∈ Ioi i, (u i + u j) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero 2 (add_pos (hu i) (hu j)).ne'
  have hd := det_cauchyMatrix u u (fun i j => (add_pos (hu i) (hu j)).ne')
  simp only [← pow_two] at hd
  rw [hD] at hd
  simp only [← two_mul] at hd
  simp_rw [div_pow, Finset.prod_div_distrib]
  rw [Finset.prod_inv_distrib]
  field_simp [hdiag, hoff]
  linear_combination hd

private def primeCayley (p : Nat.Primes) : ℝ := ((p : ℝ) + 1) / ((p : ℝ) - 1)

private theorem primeCayley_pos (p : Nat.Primes) : 0 < primeCayley p := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  exact div_pos (by linarith only [hp]) (by linarith only [hp])

private theorem primeCayley_sum (p q : Nat.Primes) :
    primeCayley p + primeCayley q =
      2 * ((p : ℝ) * (q : ℝ) - 1) / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  unfold primeCayley
  field_simp [(sub_pos.mpr hp).ne', (sub_pos.mpr hq).ne']
  ring

private theorem primeCayley_sub (p q : Nat.Primes) :
    primeCayley p - primeCayley q =
      2 * ((q : ℝ) - (p : ℝ)) / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  unfold primeCayley
  field_simp [(sub_pos.mpr hp).ne', (sub_pos.mpr hq).ne']
  ring

private theorem primeCayley_kernel (p q : Nat.Primes) :
    ((p : ℝ) * (q : ℝ) - 1)⁻¹ =
      (2 / ((p : ℝ) - 1)) * (((q : ℝ) - 1)⁻¹ * (primeCayley p + primeCayley q)⁻¹) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  have hq1 : (q : ℝ) - 1 ≠ 0 := (sub_pos.mpr hq).ne'
  have hd : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by
    have h := mul_lt_mul_of_pos_left hq (show 0 < (p : ℝ) by linarith only [hp])
    nlinarith only [h, hp]
  rw [primeCayley_sum]
  field_simp [hp1, hq1, hd]
  ring

private theorem primeCayley_diagonal (p : Nat.Primes) :
    (2 / ((p : ℝ) - 1)) * ((p : ℝ) - 1)⁻¹ * (2 * primeCayley p)⁻¹ =
      ((p : ℝ) ^ 2 - 1)⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  have hp2 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hd : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  unfold primeCayley
  field_simp [hp1, hp2, hd]
  ring

private theorem primeCayley_pair (p q : Nat.Primes) :
    ((primeCayley p - primeCayley q) / (primeCayley p + primeCayley q)) ^ 2 =
      (((p : ℝ) - (q : ℝ)) / ((p : ℝ) * (q : ℝ) - 1)) ^ 2 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  have hq1 : (q : ℝ) - 1 ≠ 0 := (sub_pos.mpr hq).ne'
  have hd : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by
    have h := mul_lt_mul_of_pos_left hq (show 0 < (p : ℝ) by linarith only [hp])
    nlinarith only [h, hp]
  rw [primeCayley_sub, primeCayley_sum]
  field_simp [hp1, hq1, hd]
  ring

/-- The Gram determinant factors into diagonal variances and squared pairwise prime ratios. -/
theorem det_kestenLikelihoodGram {n : ℕ} (p : Fin n → Nat.Primes) :
    (kestenLikelihoodGram p).det =
      (∏ i, ((p i : ℝ) ^ 2 - 1)⁻¹) *
        ∏ i, ∏ j ∈ Ioi i, (((p i : ℝ) - (p j : ℝ)) / ((p i : ℝ) * (p j : ℝ) - 1)) ^ 2 := by
  let u : Fin n → ℝ := fun i => primeCayley (p i)
  have hg : kestenLikelihoodGram p = Matrix.of (fun i j =>
      (2 / ((p i : ℝ) - 1)) * (Matrix.of (fun i j =>
        ((p j : ℝ) - 1)⁻¹ * cauchyMatrix u u i j)) i j) := by
    ext i j
    simp only [kestenLikelihoodGram_apply, Matrix.of_apply, cauchyMatrix_apply]
    exact primeCayley_kernel (p i) (p j)
  rw [hg, Matrix.det_mul_column, Matrix.det_mul_row,
    cauchy_self_det_product u (fun i => primeCayley_pos (p i))]
  have hdiag : (∏ i, 2 / ((p i : ℝ) - 1)) * (∏ i, ((p i : ℝ) - 1)⁻¹) *
      (∏ i, (2 * u i)⁻¹) = ∏ i, ((p i : ℝ) ^ 2 - 1)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => primeCayley_diagonal (p i)
  have hpair : (∏ i, ∏ j ∈ Ioi i, ((u i - u j) / (u i + u j)) ^ 2) =
      ∏ i, ∏ j ∈ Ioi i, (((p i : ℝ) - (p j : ℝ)) / ((p i : ℝ) * (p j : ℝ) - 1)) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i _
    exact Finset.prod_congr rfl fun j _ => primeCayley_pair (p i) (p j)
  rw [hpair, ← hdiag]
  ring

/-- Every finite family of distinct prime likelihoods has strictly positive Gram determinant. -/
theorem det_kestenLikelihoodGram_pos {n : ℕ} (p : Fin n ↪ Nat.Primes) :
    0 < (kestenLikelihoodGram p).det := by
  rw [det_kestenLikelihoodGram]
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    have hp : 1 < (p i : ℝ) := by exact_mod_cast (p i).property.one_lt
    apply inv_pos.mpr
    nlinarith only [hp, sq_nonneg ((p i : ℝ) - 1)]
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hp : 1 < (p i : ℝ) := by exact_mod_cast (p i).property.one_lt
    have hq : 1 < (p j : ℝ) := by exact_mod_cast (p j).property.one_lt
    have hd : (p i : ℝ) * (p j : ℝ) - 1 ≠ 0 := by
      have h := mul_lt_mul_of_pos_left hq (show 0 < (p i : ℝ) by linarith only [hp])
      nlinarith only [h, hp]
    have hn : (p i : ℝ) - (p j : ℝ) ≠ 0 := by
      intro he
      have hpq : p i = p j := by
        apply Subtype.ext
        exact_mod_cast sub_eq_zero.mp he
      exact (ne_of_lt (Finset.mem_Ioi.mp hj)) (p.injective hpq)
    exact sq_pos_of_ne_zero (div_ne_zero hn hd)

/-- Distinct primes give a strictly positive centered-likelihood Gram form. -/
theorem kestenLikelihoodGram_posDef {n : ℕ} (p : Fin n ↪ Nat.Primes) :
    (kestenLikelihoodGram p).PosDef :=
  (kestenLikelihoodGram_posSemidef p).posDef_iff_det_ne_zero.mpr
    (det_kestenLikelihoodGram_pos p).ne'

/-- No nonzero finite combination of distinct centered prime likelihoods has zero squared norm. -/
theorem integral_kestenLikelihood_combination_sq_eq_zero_iff {n : ℕ}
    (p : Fin n ↪ Nat.Primes) (c : Fin n → ℝ) :
    (∫ x, (∑ i, c i * (kestenLikelihood (p i) x - 1)) ^ 2
      ∂(semicircleSpectralLaw : Measure ℝ)) = 0 ↔ c = 0 := by
  constructor
  · intro he
    by_contra hc
    have hp := (kestenLikelihoodGram_posDef p).dotProduct_mulVec_pos hc
    have hq : star c ⬝ᵥ (kestenLikelihoodGram p).mulVec c =
        ∑ i, ∑ j, c i * c j * kestenLikelihoodGram p i j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hq, kestenLikelihoodGram_quadratic_form, he] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · rintro rfl
    simp

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenLikelihoodGram_apply
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenLikelihoodGram_quadratic_form
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenLikelihoodGram_posSemidef
#print axioms GaloisForLFunctions.SelbergClass.Primon.det_kestenLikelihoodGram
#print axioms GaloisForLFunctions.SelbergClass.Primon.det_kestenLikelihoodGram_pos
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenLikelihoodGram_posDef
#print axioms GaloisForLFunctions.SelbergClass.Primon.integral_kestenLikelihood_combination_sq_eq_zero_iff
