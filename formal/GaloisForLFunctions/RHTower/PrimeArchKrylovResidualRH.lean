import GaloisForLFunctions.HTGeometry.ThermalKrylovDeterminant
import GaloisForLFunctions.RHTower.PrimeArchCanonicalReflectionPositiveEquivalence
import GaloisForLFunctions.RHTower.PrimeArchReflectionPositiveHankelRH

/-!
# Krylov residual values for the prime--archimedean and Xi determinant towers

The previous complex reflection-positive interface supplied the weak trace-Hankel cone but had no
strict complex determinant producer.  Krylov nontermination closes that gap.  Every leading source
and Xi determinant is identified with a product of squared complex Gram--Schmidt residual norms;
nonzero residuals therefore discharge the full strict determinant hierarchy and imply RH.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- The squared norm of the `k`-th residual in the complex Krylov/Gram--Schmidt chain. -/
def complexKrylovResidualNormSq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F) (k : ℕ) : ℝ :=
  ‖InnerProductSpace.gramSchmidt ℂ v k‖ ^ 2

/-- The complex Krylov/Gram--Schmidt chain does not terminate in any degree. -/
def ComplexKrylovResidualsNonzero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F) : Prop :=
  ∀ k : ℕ, InnerProductSpace.gramSchmidt ℂ v k ≠ 0

/-- Exact value of every leading prime--archimedean source determinant in a complex reflected
Krylov realization. -/
theorem det_primeArchSourceMomentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (n : ℕ)
    (hli : LinearIndependent ℂ (fun i : Fin n => v (i : ℕ))) :
    (primeArchSourceMomentHankelMatrix n).det =
      ∏ k : Fin n, ‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin n => v (i : ℕ)) k‖ ^ 2 := by
  have hmatrix : primeArchSourceMomentHankelMatrix n =
      HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n := by
    ext i j
    rfl
  rw [hmatrix]
  exact HTGeometry.det_momentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    normalizedPrimeArchMoment v hgram n hli

/-- The same Krylov residual product is the exact value of every leading Xi central moment
determinant. -/
theorem det_xiCentralMomentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (n : ℕ)
    (hli : LinearIndependent ℂ (fun i : Fin n => v (i : ℕ))) :
    (xiCentralMomentHankelMatrix n).det =
      ∏ k : Fin n, ‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin n => v (i : ℕ)) k‖ ^ 2 := by
  rw [← primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
  exact det_primeArchSourceMomentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    v hgram n hli

/-- The zeroth Krylov residual norm is the zeroth reflected moment. -/
theorem complexKrylovResidualNormSq_zero_eq_moment_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F) (m : ℕ → ℝ)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ)) :
    complexKrylovResidualNormSq v 0 = m 0 := by
  change ‖InnerProductSpace.gramSchmidt ℂ v (⊥ : ℕ)‖ ^ 2 = m 0
  rw [InnerProductSpace.gramSchmidt_bot]
  apply Complex.ofReal_injective
  have h := hgram 0 0
  rw [inner_self_eq_norm_sq_to_K] at h
  simpa only [Complex.ofReal_pow, zero_add, Nat.bot_eq_zero] using! h

/-- **Correct normalized Lanczos value formula for the source determinant tower.**  Under the
normalized residual recurrence, the `j`-th Lanczos coefficient occurs with exponent
`2 * (N - j)`. -/
theorem det_primeArchSourceMomentHankelMatrix_lanczosScaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (hresidual : ComplexKrylovResidualsNonzero v)
    (b : ℕ → ℝ)
    (hrec : ∀ k, complexKrylovResidualNormSq v (k + 1) =
      complexKrylovResidualNormSq v k * b (k + 1) ^ 2)
    (N : ℕ) :
    (primeArchSourceMomentHankelMatrix N).det =
      normalizedPrimeArchMoment 0 ^ N *
        ∏ j ∈ Finset.Ico 1 N, b j ^ (2 * (N - j)) := by
  have hli : LinearIndependent ℂ (fun i : Fin N => v (i : ℕ)) :=
    (GaloisForLFunctions.HTGeometry.linearIndependent_iff_gramSchmidt_ne_zero _).mpr
      (fun k => by
        rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val]
        exact hresidual (k : ℕ))
  rw [det_primeArchSourceMomentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    v hgram N hli]
  have hprod :
      (∏ k : Fin N, ‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin N => v (i : ℕ)) k‖ ^ 2) =
      ∏ k ∈ Finset.range N, complexKrylovResidualNormSq v k := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _
    rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val]
    rfl
  rw [hprod]
  exact HTGeometry.lanczosDeterminantScaling
    (normalizedPrimeArchMoment 0) b (complexKrylovResidualNormSq v)
    (complexKrylovResidualNormSq_zero_eq_moment_zero v normalizedPrimeArchMoment hgram)
    hrec N

/-- The identical normalized Lanczos scaling law holds for the Xi central determinant tower. -/
theorem det_xiCentralMomentHankelMatrix_lanczosScaling
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (hresidual : ComplexKrylovResidualsNonzero v)
    (b : ℕ → ℝ)
    (hrec : ∀ k, complexKrylovResidualNormSq v (k + 1) =
      complexKrylovResidualNormSq v k * b (k + 1) ^ 2)
    (N : ℕ) :
    (xiCentralMomentHankelMatrix N).det =
      normalizedPrimeArchMoment 0 ^ N *
        ∏ j ∈ Finset.Ico 1 N, b j ^ (2 * (N - j)) := by
  rw [← primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
  exact det_primeArchSourceMomentHankelMatrix_lanczosScaling
    v hgram hresidual b hrec N

/-- Complex reflection-positive source values plus Krylov nontermination discharge the strict
prime--archimedean determinant hierarchy.  This is the strict complex counterpart missing from the
older reflection-positive interface. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_complexKrylovResidualsNonzero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (hresidual : ComplexKrylovResidualsNonzero v) :
    PrimeArchSourceMomentHankelDeterminantsPositive := by
  intro n
  have hli : LinearIndependent ℂ (fun i : Fin n => v (i : ℕ)) :=
    (GaloisForLFunctions.HTGeometry.linearIndependent_iff_gramSchmidt_ne_zero _).mpr
      (fun k => by
        rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val]
        exact hresidual (k : ℕ))
  rw [det_primeArchSourceMomentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    v hgram n hli]
  apply Finset.prod_pos
  intro k _
  rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val]
  exact sq_pos_of_pos (norm_pos_iff.mpr (hresidual (k : ℕ)))

/-- **Complex Krylov nontermination RH capstone.** -/
theorem riemannHypothesis_of_primeArchComplexKrylovResidualsNonzero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ))
    (hresidual : ComplexKrylovResidualsNonzero v) :
    RiemannHypothesis :=
  primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
    (primeArchSourceMomentHankelDeterminantsPositive_of_complexKrylovResidualsNonzero
      v hgram hresidual)

/-- Under RH, the canonical reflection-positive Xi orbit has no terminating Krylov residual.
Strict source Hankel determinants make every finite Gram packet linearly independent. -/
theorem complexKrylovResidualsNonzero_primeArchReflectionVector
    (hRH : RiemannHypothesis) :
    ComplexKrylovResidualsNonzero (primeArchReflectionVector hRH) := by
  intro k
  let n := k + 1
  have hmatrix :
      Matrix.gram ℂ
          (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ)) =
        (algebraMap ℝ ℂ).mapMatrix (primeArchSourceMomentHankelMatrix n) := by
    ext i j
    rw [Matrix.gram_apply, inner_primeArchReflectionVector_eq_normalizedMoment]
    rfl
  have hdetReal : 0 < (primeArchSourceMomentHankelMatrix n).det :=
    (primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH) n
  have hdet :
      (Matrix.gram ℂ
        (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ))).det ≠ 0 := by
    rw [hmatrix, ← RingHom.map_det]
    exact (map_ne_zero (algebraMap ℝ ℂ)).2 (ne_of_gt hdetReal)
  have hli : LinearIndependent ℂ
      (fun i : Fin n => primeArchReflectionVector hRH (i : ℕ)) :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mp hdet
  have hres := InnerProductSpace.gramSchmidt_ne_zero
    (⟨k, Nat.lt_succ_self k⟩ : Fin n) hli
  rw [GaloisForLFunctions.HTGeometry.gramSchmidt_fin_val] at hres
  exact hres

/-- Existence of an exact complex Gram realization with nonterminating Krylov chain is exactly RH.
The converse realization is the canonical reciprocal-square Xi orbit. -/
theorem riemannHypothesis_iff_exists_primeArchComplexKrylovRealization :
    RiemannHypothesis ↔
      ∃ v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
        (∀ i j, inner ℂ (v i) (v j) =
          (normalizedPrimeArchMoment (i + j) : ℂ)) ∧
        ComplexKrylovResidualsNonzero v := by
  constructor
  · intro hRH
    exact ⟨primeArchReflectionVector hRH,
      inner_primeArchReflectionVector_eq_normalizedMoment hRH,
      complexKrylovResidualsNonzero_primeArchReflectionVector hRH⟩
  · rintro ⟨v, hgram, hres⟩
    exact riemannHypothesis_of_primeArchComplexKrylovResidualsNonzero v hgram hres

end

end RHTower
