import Mathlib

/-! Integrate bounded-overlap height windows with analytic multiplicity. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Finset
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

theorem count_by_height_cover (Z : Finset ℂ) (w : ℂ → ℝ) (F : ℝ → ℝ) (U h δ M : ℝ) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hZ : ∀ ρ ∈ Z, |ρ.im| + h ≤ U)
    (hF : IntervalIntegrable F volume (-U) U) (hF0 : ∀ τ, 0 ≤ F τ)
    (h1 : ∀ ρ ∈ Z, ∀ τ, |τ - ρ.im| ≤ h → δ ≤ F τ ∧
      ∑ z ∈ Z.filter (fun z => |τ - z.im| ≤ h), w z ≤ M) :
    δ * (2 * h) * ∑ ρ ∈ Z, w ρ ≤ M * ∫ τ in (-U)..U, F τ := by
  classical
  have hU' : -U ≤ U := by linarith
  set g : ℂ → ℝ → ℝ := fun ρ => (Set.Icc (ρ.im - h) (ρ.im + h)).indicator (fun _ => δ * w ρ) with hg
  have hgi : ∀ ρ, IntegrableOn (g ρ) (Set.Icc (-U) U) := fun ρ =>
    (integrableOn_const (by simp)).indicator measurableSet_Icc
  have hint : ∀ ρ ∈ Z, ∫ τ in Set.Icc (-U) U, g ρ τ = δ * (2 * h) * w ρ := by
    intro ρ hρ
    have := hZ ρ hρ
    have h2 := le_abs_self ρ.im
    have h3 := neg_abs_le ρ.im
    rw [hg]
    simp only
    rw [setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_self_of_subset_right (Set.Icc_subset_Icc (by linarith) (by linarith))]
    simp only [setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [Finset.mul_sum, ← Finset.sum_congr rfl hint, ← integral_finsetSum _ (fun ρ _ => hgi ρ),
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hU',
    ← integral_Icc_eq_integral_Ioc]
  refine integral_mono (integrable_finsetSum _ (fun ρ _ => hgi ρ)) ?_ fun τ => ?_
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hU').1 hF).const_mul M
  · have he : ∑ ρ ∈ Z, g ρ τ = δ * ∑ z ∈ Z.filter (fun z => |τ - z.im| ≤ h), w z := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      have hmem : τ ∈ Set.Icc (ρ.im - h) (ρ.im + h) ↔ |τ - ρ.im| ≤ h := by
        rw [Set.mem_Icc, abs_le]
        constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      change (Set.Icc (ρ.im - h) (ρ.im + h)).indicator (fun _ => δ * w ρ) τ =
        (if |τ - ρ.im| ≤ h then δ * w ρ else 0)
      by_cases hp : |τ - ρ.im| ≤ h
      · rw [Set.indicator_of_mem (hmem.mpr hp), if_pos hp]
      · rw [Set.indicator_of_notMem (fun hn => hp (hmem.mp hn)), if_neg hp]
    simp only
    rw [he]
    rcases (Z.filter (fun z => |τ - z.im| ≤ h)).eq_empty_or_nonempty with h0 | ⟨ρ, hρ⟩
    · rw [h0]; simpa using mul_nonneg hM (hF0 τ)
    · obtain ⟨a, b⟩ := Finset.mem_filter.1 hρ
      obtain ⟨c, d⟩ := h1 ρ a τ b
      calc _ ≤ δ * M := mul_le_mul_of_nonneg_left d hδ
        _ ≤ F τ * M := mul_le_mul_of_nonneg_right c hM
        _ = _ := mul_comm _ _

end QH.PrimeProgressions
