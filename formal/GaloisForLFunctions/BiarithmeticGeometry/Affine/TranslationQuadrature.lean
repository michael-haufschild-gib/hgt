import GaloisForLFunctions.BiarithmeticGeometry.Affine.SmallTranslationGrids

/-!
# Polynomial reproduction on separated translation grids

Averaging identical finite-difference rules across geometric blocks preserves polynomial
evaluation and reduces the sum of squared weights by the number of blocks.
-/

open Polynomial Complex Finset
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Equal averaging across blocks of the normalized finite-difference rule. -/
def translationQuadratureWeight (n N : ℕ) (j : Fin n × Fin N) : ℂ :=
  originQuadratureWeight n j.1 / (N : ℂ)

theorem conj_translationQuadratureWeight (n N : ℕ) (j : Fin n × Fin N) :
    starRingEnd ℂ (translationQuadratureWeight n N j) = translationQuadratureWeight n N j := by
  simp only [translationQuadratureWeight, map_div₀, conj_originQuadratureWeight, map_natCast]

/-- Every affine polynomial reading below the quadrature order is reproduced exactly. -/
theorem translationQuadrature_eval {n N : ℕ} (hN : 0 < N) (ε : ℚ)
    (P : ℂ[X]) (hP : P.natDegree < n) (α β : ℂ) :
    (∑ j : Fin n × Fin N, translationQuadratureWeight n N j *
      P.eval (α * (quadratureTranslationNode ε j.1 j.2.val : ℂ) + β)) = P.eval β := by
  have hrow (t : Fin N) : (∑ i : Fin n, originQuadratureWeight n i *
      P.eval (α * (quadratureTranslationNode ε i t.val : ℂ) + β)) = P.eval β := by
    have h := originQuadrature_eval_shifted P hP β
      (α * (ε : ℂ) / (n + 1 : ℂ) ^ (t.val + 1))
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    simp only [quadratureTranslationNode, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
    ring
  have hrow' (t : Fin N) : (∑ i : Fin n, translationQuadratureWeight n N (i, t) *
      P.eval (α * (quadratureTranslationNode ε i t.val : ℂ) + β)) = (N : ℂ)⁻¹ * P.eval β := by
    calc
      _ = (N : ℂ)⁻¹ * ∑ i : Fin n, originQuadratureWeight n i *
          P.eval (α * (quadratureTranslationNode ε i t.val : ℂ) + β) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [translationQuadratureWeight, div_eq_mul_inv]
        ring
      _ = _ := by rw [hrow]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hrow', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]

/-- The total weight is one whenever the quadrature order and number of blocks are positive. -/
theorem sum_translationQuadratureWeight {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    ∑ j : Fin n × Fin N, translationQuadratureWeight n N j = 1 := by
  have h := translationQuadrature_eval hN (1 : ℚ) (1 : ℂ[X])
    (by simpa only [natDegree_one] using hn) 0 0
  simpa only [eval_one, mul_one] using h

/-- Repeating the rule over `N` orthogonal blocks divides its squared norm by `N`. -/
theorem sum_normSq_translationQuadratureWeight {n N : ℕ} (hN : 0 < N) :
    (∑ j : Fin n × Fin N, normSq (translationQuadratureWeight n N j)) =
      (∑ i : Fin n, normSq (originQuadratureWeight n i)) / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnorm (i : Fin n) : normSq (originQuadratureWeight n i / (N : ℂ)) =
      normSq (originQuadratureWeight n i) / (N : ℝ) ^ 2 := by
    simp only [normSq_eq_norm_sq, norm_div, Complex.norm_natCast, div_pow]
  rw [Fintype.sum_prod_type]
  simp only [translationQuadratureWeight, hnorm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hN0]

#print axioms translationQuadrature_eval
#print axioms sum_normSq_translationQuadratureWeight
end GaloisForLFunctions.BiarithmeticGeometry
