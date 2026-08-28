import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenUpperAdicPartition

/-!
# Exact adic subdivision of convolution factors

This file lifts the scalar upper-closed partition to coefficient arithmetic functions and to the
constant-one factor in a Dirichlet convolution.  Equalities are exact on the finite source window;
no endpoint term is discarded.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- One coefficient sequence restricted to an upper-closed `(1+δ)`-adic interval. -/
def mtUpperAdicCoefficientAF (α : ℕ → ℂ) (δ : ℝ) (j : ℕ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF α (mtUpperAdicScale δ j)
    ((1 + δ) * mtUpperAdicScale δ j)

@[simp] theorem mtUpperAdicCoefficientAF_apply_of_pos
    (α : ℕ → ℂ) (δ : ℝ) (j : ℕ) {m : ℕ} (hm : 0 < m) :
    mtUpperAdicCoefficientAF α δ j m =
      if mtUpperAdicScale δ j < (m : ℝ) ∧
          (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
      then α m else 0 := by
  simp [mtUpperAdicCoefficientAF, mtRealIntervalAF_apply_of_pos, hm]

theorem mtUpperAdicCoefficientAF_polynomialDivisorBounded
    {α : ℕ → ℂ} (hα : MTPolynomialDivisorBounded α) (δ : ℝ) (j : ℕ) :
    MTPolynomialDivisorBounded (fun m =>
      if mtUpperAdicScale δ j < (m : ℝ) ∧
          (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
      then α m else 0) := by
  exact hα.restrict (fun m =>
    mtUpperAdicScale δ j < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j)

/-- Exact coefficient partition through a finite upper endpoint. -/
theorem sum_mtUpperAdicCoefficientAF_apply
    {δ : ℝ} (hδ : 0 < δ) (α : ℕ → ℂ)
    {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    (∑ j ∈ Finset.range (mtUpperAdicIndex δ M + 1),
        mtUpperAdicCoefficientAF α δ j) m = α m := by
  rw [arithmeticFunction_finset_sum_apply]
  have hindexMem : mtUpperAdicIndex δ m ∈
      Finset.range (mtUpperAdicIndex δ M + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact mtUpperAdicIndex_mono hδ hmM
  calc
    ∑ j ∈ Finset.range (mtUpperAdicIndex δ M + 1),
        mtUpperAdicCoefficientAF α δ j m =
        mtUpperAdicCoefficientAF α δ (mtUpperAdicIndex δ m) m := by
      apply Finset.sum_eq_single (mtUpperAdicIndex δ m)
      · intro j hj hne
        rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hm]
        by_cases hblock : mtUpperAdicScale δ j < (m : ℝ) ∧
            (m : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
        · exact (hne ((mtUpperAdicIndex_eq_iff hδ hm j).2 hblock).symm).elim
        · simp [hblock]
      · intro hnot
        exact (hnot hindexMem).elim
    _ = α m := by
      rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hm]
      simp [(mtUpperAdicIndex_eq_iff hδ hm (mtUpperAdicIndex δ m)).1 rfl]

/-- A sequence with finite upper support is globally the sum of its upper-closed adic blocks. -/
theorem mtCoefficientAF_eq_sum_upperAdic
    {δ : ℝ} (hδ : 0 < δ) (α : ℕ → ℂ) (M : ℕ)
    (hα : ∀ {m : ℕ}, M < m → α m = 0) :
    mtCoefficientAF α =
      ∑ j ∈ Finset.range (mtUpperAdicIndex δ M + 1),
        mtUpperAdicCoefficientAF α δ j := by
  ext m
  by_cases hm : m = 0
  · subst m
    simp [mtCoefficientAF, mtUpperAdicCoefficientAF, mtRealIntervalAF]
  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
    by_cases hmM : m ≤ M
    · rw [mtCoefficientAF_apply_of_pos _ hmPos]
      exact (sum_mtUpperAdicCoefficientAF_apply hδ α hmPos hmM).symm
    · have hzero : α m = 0 := hα (Nat.lt_of_not_ge hmM)
      rw [mtCoefficientAF_apply_of_pos _ hmPos, hzero]
      rw [arithmeticFunction_finset_sum_apply]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hmPos]
      simp [hzero]

/-- On coefficients through `N`, convolution with the constant-one factor splits exactly into the
finite upper-closed adic family. -/
theorem mul_mtCoefficientAF_one_apply_eq_sum_upperAdic
    {δ : ℝ} (hδ : 0 < δ) (F : ArithmeticFunction ℂ)
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (F * mtCoefficientAF (fun _ => 1)) n =
      (∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
        F * mtUpperAdicOneAF δ j) n := by
  let G : ArithmeticFunction ℂ :=
    ∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1), mtUpperAdicOneAF δ j
  have hconv :
      (F * mtCoefficientAF (fun _ => 1)) n = (F * G) n := by
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    have hxProd : x.1 * x.2 = n := by
      exact (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hxTwoPos : 0 < x.2 := by
      by_contra h
      have hxZero : x.2 = 0 := Nat.eq_zero_of_not_pos h
      simp [hxZero] at hxProd
      exact hn.ne' hxProd.symm
    have hxTwoLe : x.2 ≤ N := by
      have hxLeN : x.2 ≤ n := by
        rw [← hxProd]
        exact Nat.le_mul_of_pos_left x.2 (Nat.pos_of_ne_zero (by
          intro hxOne
          simp [hxOne] at hxProd
          exact hn.ne' hxProd.symm))
      exact hxLeN.trans hnN
    rw [mtCoefficientAF_apply_of_pos _ hxTwoPos]
    change F x.1 * 1 = F x.1 * G x.2
    rw [sum_mtUpperAdicOneAF_apply hδ hxTwoPos hxTwoLe]
  rw [hconv]
  change (F * (∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
    mtUpperAdicOneAF δ j)) n = _
  rw [Finset.mul_sum]

/-- Exact two-variable adic box expansion of the truncated Legendre kernel on a finite window. -/
theorem mtTruncLegendreAF_apply_eq_sum_upperAdicBoxes
    {δ : ℝ} (hδ : 0 < δ) (z D : ℕ)
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    mtTruncLegendreAF z D n =
      (∑ i ∈ Finset.range (mtUpperAdicIndex δ D + 1),
        ∑ j ∈ Finset.range (mtUpperAdicIndex δ N + 1),
          mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i *
            mtUpperAdicOneAF δ j) n := by
  have hsupport : ∀ {e : ℕ}, D < e → mtTruncLegendreCoefficient z D e = 0 := by
    intro e he
    simp [mtTruncLegendreCoefficient, (not_le_of_gt he)]
  rw [mtTruncLegendreAF_eq_coefficient_mul_one,
    mtCoefficientAF_eq_sum_upperAdic hδ (mtTruncLegendreCoefficient z D) D hsupport,
    Finset.sum_mul, arithmeticFunction_finset_sum_apply,
    arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_mtCoefficientAF_one_apply_eq_sum_upperAdic hδ
    (mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ i) hn hnN

end

end RHTower.Sieve
