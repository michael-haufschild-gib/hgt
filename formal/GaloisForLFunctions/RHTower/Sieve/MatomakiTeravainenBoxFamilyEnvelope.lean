import GaloisForLFunctions.RHTower.Sieve.GeneralizedDivisorShortInterval
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainBoxExpansion

/-!
# Unsigned envelopes for finite box families

Product-scale filtering must aggregate boxes before taking moments.  These lemmas compose
coefficientwise finite-family envelopes through Dirichlet convolution and record that an
upper-closed adic partition has unsigned mass at most one.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

/-- Product-indexed finite convolution families inherit the convolution of their unsigned
coefficient envelopes. -/
theorem sum_norm_family_convolution_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ)
    (F : ι → ArithmeticFunction ℂ) (G : κ → ArithmeticFunction ℂ)
    (A B : ArithmeticFunction ℕ)
    (hF : ∀ m, ∑ i ∈ S, ‖F i m‖ ≤ (A m : ℝ))
    (hG : ∀ m, ∑ j ∈ T, ‖G j m‖ ≤ (B m : ℝ))
    (n : ℕ) :
    ∑ ij ∈ S.product T, ‖(F ij.1 * G ij.2) n‖ ≤ ((A * B) n : ℝ) := by
  calc
    ∑ ij ∈ S.product T, ‖(F ij.1 * G ij.2) n‖ ≤
        ∑ ij ∈ S.product T,
          ∑ de ∈ n.divisorsAntidiagonal,
            ‖F ij.1 de.1‖ * ‖G ij.2 de.2‖ := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [ArithmeticFunction.mul_apply]
      exact (norm_sum_le _ _).trans (by
        apply Finset.sum_le_sum
        intro de hde
        rw [norm_mul])
    _ = ∑ de ∈ n.divisorsAntidiagonal,
          (∑ i ∈ S, ‖F i de.1‖) * (∑ j ∈ T, ‖G j de.2‖) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro de hde
      calc
        ∑ ij ∈ S.product T, ‖F ij.1 de.1‖ * ‖G ij.2 de.2‖ =
            ∑ i ∈ S, ∑ j ∈ T, ‖F i de.1‖ * ‖G j de.2‖ :=
          Finset.sum_product S T _
        _ = (∑ i ∈ S, ‖F i de.1‖) * (∑ j ∈ T, ‖G j de.2‖) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ ≤ ∑ de ∈ n.divisorsAntidiagonal, (A de.1 : ℝ) * (B de.2 : ℝ) := by
      apply Finset.sum_le_sum
      intro de hde
      exact mul_le_mul (hF de.1) (hG de.2)
        (sum_nonneg fun j hj => norm_nonneg _) (by positivity)
    _ = ((A * B) n : ℝ) := by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl

/-- One upper-closed adic grid has unsigned coefficient mass at most one whenever the underlying
coefficient sequence is pointwise bounded by one. -/
theorem sum_norm_mtUpperAdicCoefficientAF_le_one
    {δ : ℝ} (hδ : 0 < δ) (α : ℕ → ℂ)
    (hα : ∀ {m : ℕ}, 0 < m → ‖α m‖ ≤ 1)
    (J n : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ‖mtUpperAdicCoefficientAF α δ j n‖ ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtUpperAdicCoefficientAF, mtRealIntervalAF]
  by_cases hindex : mtUpperAdicIndex δ n ∈ Finset.range (J + 1)
  · calc
      ∑ j ∈ Finset.range (J + 1), ‖mtUpperAdicCoefficientAF α δ j n‖ =
          ‖mtUpperAdicCoefficientAF α δ (mtUpperAdicIndex δ n) n‖ := by
        apply Finset.sum_eq_single (mtUpperAdicIndex δ n)
        · intro j hj hne
          rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hn]
          by_cases hblock : mtUpperAdicScale δ j < (n : ℝ) ∧
              (n : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
          · exact (hne ((mtUpperAdicIndex_eq_iff hδ hn j).2 hblock).symm).elim
          · simp [hblock]
        · exact fun hnot => (hnot hindex).elim
      _ = ‖α n‖ := by
        rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hn]
        simp [(mtUpperAdicIndex_eq_iff hδ hn (mtUpperAdicIndex δ n)).1 rfl]
      _ ≤ 1 := hα hn
  · have hzero : ∀ j ∈ Finset.range (J + 1),
        mtUpperAdicCoefficientAF α δ j n = 0 := by
      intro j hj
      rw [mtUpperAdicCoefficientAF_apply_of_pos _ _ _ hn]
      by_cases hblock : mtUpperAdicScale δ j < (n : ℝ) ∧
          (n : ℝ) ≤ (1 + δ) * mtUpperAdicScale δ j
      · exact False.elim (hindex (by
          have heq := (mtUpperAdicIndex_eq_iff hδ hn j).2 hblock
          simpa only [heq] using hj))
      · simp [hblock]
    calc
      ∑ j ∈ Finset.range (J + 1), ‖mtUpperAdicCoefficientAF α δ j n‖ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hzero j hj, norm_zero]
      _ ≤ 1 := by norm_num

/-- Constant-one adic factors have the same unsigned mass bound. -/
theorem sum_norm_mtUpperAdicOneAF_le_one
    {δ : ℝ} (hδ : 0 < δ) (J n : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ‖mtUpperAdicOneAF δ j n‖ ≤ 1 := by
  have hEq : ∀ j,
      mtUpperAdicOneAF δ j = mtUpperAdicCoefficientAF (fun _ => 1) δ j := by
    intro j
    rfl
  simp_rw [hEq]
  exact sum_norm_mtUpperAdicCoefficientAF_le_one hδ (fun _ => 1)
    (fun _ => by simp) J n

/-- Truncated Möbius adic factors have unsigned mass at most one. -/
theorem sum_norm_mtUpperAdicTruncLegendre_le_one
    {δ : ℝ} (hδ : 0 < δ) (z D J n : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        ‖mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ j n‖ ≤ 1 := by
  apply sum_norm_mtUpperAdicCoefficientAF_le_one hδ
  intro m hm
  by_cases hsupport : m ∣ siftModulus z ∧ m ≤ D
  · rw [mtTruncLegendreCoefficient, if_pos hsupport, Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  · simp [mtTruncLegendreCoefficient, hsupport]

end

end RHTower.Sieve
