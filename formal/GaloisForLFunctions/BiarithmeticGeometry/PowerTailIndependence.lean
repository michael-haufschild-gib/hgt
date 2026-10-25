import GaloisForLFunctions.BiarithmeticGeometry.PowerTailCoefficients
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Independent unpaid power-tail classes

In a nonzero finite complex combination, the smallest active tail exponent
dominates after normalization. Its nonzero limiting coefficient gives a
divergent power-series lower bound. Thus distinct exponents at or below
one half remain independent modulo the square-partial-sum domain.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A finite complex combination of shifted power tails. -/
def powerTailCombination (s : Finset ℝ) (c : ℝ → ℂ) (M : ℕ) : ℂ :=
  ∑ α ∈ s, c α * (criticalPowerTail α M : ℂ)

private theorem criticalPowerTail_ratio (α β : ℝ) (M : ℕ) :
    criticalPowerTail β M / criticalPowerTail α M = criticalPowerTail (β - α) M := by
  simp only [criticalPowerTail]
  rw [← Real.rpow_sub (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
  congr 1
  ring

/-- Normalizing by the strictly smallest exponent retains exactly its coefficient. -/
theorem powerTailCombination_ratio_tendsto (s : Finset ℝ) (c : ℝ → ℂ)
    (α : ℝ) (hα : α ∈ s) (hmin : ∀ β ∈ s, β ≠ α → α < β) :
    Tendsto (fun M => powerTailCombination s c M / (criticalPowerTail α M : ℂ))
      atTop (𝓝 (c α)) := by
  classical
  have hterm (β : ℝ) (hβ : β ∈ s) :
      Tendsto (fun M => c β * (criticalPowerTail (β - α) M : ℂ)) atTop
        (𝓝 (if β = α then c β else 0)) := by
    by_cases hβα : β = α
    · subst β
      simp only [sub_self, criticalPowerTail, neg_zero, Real.rpow_zero, Complex.ofReal_one,
        mul_one]
      exact tendsto_const_nhds
    · rw [if_neg hβα]
      have ht := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
        (criticalPowerTail_tendsto (β - α) (sub_pos.mpr (hmin β hβ hβα)))
      simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero] using ht.const_mul (c β)
  have hsum := tendsto_finsetSum s hterm
  have hval : (∑ β ∈ s, if β = α then c β else 0) = c α := by simp [hα]
  rw [hval] at hsum
  have he (M : ℕ) : powerTailCombination s c M / (criticalPowerTail α M : ℂ) =
      ∑ β ∈ s, c β * (criticalPowerTail (β - α) M : ℂ) := by
    rw [powerTailCombination, div_eq_mul_inv, Finset.sum_mul]
    apply sum_congr rfl
    intro β _
    rw [mul_assoc, ← div_eq_mul_inv, ← Complex.ofReal_div, criticalPowerTail_ratio]
  simpa only [he] using hsum

/-- A nonzero dominant exponent at most one half forces infinite square energy. -/
theorem not_summable_sq_powerTailCombination_of_min (s : Finset ℝ) (c : ℝ → ℂ)
    (α : ℝ) (hα : α ∈ s) (hmin : ∀ β ∈ s, β ≠ α → α < β)
    (hc : c α ≠ 0) (hhalf : α ≤ (1 : ℝ) / 2) :
    ¬Summable (fun M => ‖powerTailCombination s c M‖ ^ 2) := by
  intro hsum
  have hnorm : 0 < ‖c α‖ := norm_pos_iff.mpr hc
  have hhalfNorm : 0 < ‖c α‖ / 2 := by positivity
  have hev : ∀ᶠ M : ℕ in atTop,
      ‖c α‖ / 2 < ‖powerTailCombination s c M / (criticalPowerTail α M : ℂ)‖ :=
    (powerTailCombination_ratio_tendsto s c α hα hmin).norm.eventually
      (eventually_gt_nhds (by linarith only [hnorm] : ‖c α‖ / 2 < ‖c α‖))
  have hbound : ∀ᶠ M : ℕ in atTop,
      (‖c α‖ / 2) ^ 2 * criticalPowerTail α M ^ 2 ≤ ‖powerTailCombination s c M‖ ^ 2 := by
    filter_upwards [hev] with M hM
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (criticalPowerTail_pos α M)] at hM
    have hb := (lt_div_iff₀ (criticalPowerTail_pos α M)).mp hM
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hhalfNorm.le (criticalPowerTail_pos α M).le) hb.le 2
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hs : Summable (fun M => ‖powerTailCombination s c (M + N)‖ ^ 2) :=
    (summable_nat_add_iff N).mpr hsum
  have hp : Summable (fun M => (‖c α‖ / 2) ^ 2 * criticalPowerTail α (M + N) ^ 2) :=
    hs.of_nonneg_of_le (fun M => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun M => hN (M + N) (by omega))
  have hpall : Summable (fun M => (‖c α‖ / 2) ^ 2 * criticalPowerTail α M ^ 2) :=
    (summable_nat_add_iff N).mp hp
  have hscale : (‖c α‖ / 2) ^ 2 ≠ 0 := (pow_pos hhalfNorm 2).ne'
  have htail : Summable (fun M => criticalPowerTail α M ^ 2) := by
    apply (hpall.div_const ((‖c α‖ / 2) ^ 2)).congr
    intro M
    field_simp [hscale]
  have hpaid : (1 : ℝ) / 2 < α :=
    (summable_sq_criticalPowerCoeff_partialSum_iff α).mp (by
      simpa only [criticalPowerCoeff_partialSum, neg_sq] using htail)
  exact (not_lt_of_ge hhalf) hpaid

/-- Every nonzero finite complex combination in the unpaid exponent interval has infinite energy. -/
theorem not_summable_sq_powerTailCombination (s : Finset ℝ) (c : ℝ → ℂ)
    (hhalf : ∀ α ∈ s, α ≤ (1 : ℝ) / 2) (hc : ∃ α ∈ s, c α ≠ 0) :
    ¬Summable (fun M => ‖powerTailCombination s c M‖ ^ 2) := by
  classical
  let t := s.filter (fun α => c α ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨α, hα, hcα⟩ := hc
    exact ⟨α, mem_filter.mpr ⟨hα, hcα⟩⟩
  let α := t.min' ht
  have hα : α ∈ t := min'_mem t ht
  have hmin : ∀ β ∈ t, β ≠ α → α < β := by
    intro β hβ hβα
    exact lt_of_le_of_ne (min'_le t β hβ) hβα.symm
  have he (M : ℕ) : powerTailCombination t c M = powerTailCombination s c M := by
    rw [powerTailCombination, powerTailCombination]
    change (∑ β ∈ s.filter (fun β => c β ≠ 0), c β * (criticalPowerTail β M : ℂ)) = _
    rw [sum_filter]
    apply sum_congr rfl
    intro β _
    by_cases hβ : c β = 0 <;> simp only [hβ, ne_eq, not_true_eq_false, if_false,
      zero_mul, not_false_eq_true, if_true]
  have haS := mem_filter.mp hα
  simpa only [he] using not_summable_sq_powerTailCombination_of_min t c α hα hmin
    haS.2 (hhalf α haS.1)

/-- Square-summable partial sums force every coefficient of the finite power-tail family to vanish. -/
theorem criticalPowerCoeff_independent_mod_squareSums (s : Finset ℝ) (c : ℝ → ℂ)
    (hhalf : ∀ α ∈ s, α ≤ (1 : ℝ) / 2)
    (hpaid : Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1),
      ∑ α ∈ s, c α * (criticalPowerCoeff α r : ℂ)‖ ^ 2)) :
    ∀ α ∈ s, c α = 0 := by
  have he (M : ℕ) : (∑ r ∈ range (M + 1), ∑ α ∈ s, c α * (criticalPowerCoeff α r : ℂ)) =
      -powerTailCombination s c M := by
    rw [sum_comm]
    simp only [← mul_sum, ← Complex.ofReal_sum, criticalPowerCoeff_partialSum,
      Complex.ofReal_neg, mul_neg, sum_neg_distrib, powerTailCombination]
  have hs : Summable (fun M => ‖powerTailCombination s c M‖ ^ 2) := by
    simpa only [he, norm_neg] using hpaid
  intro α hα
  by_contra hc
  exact not_summable_sq_powerTailCombination s c hhalf ⟨α, hα, hc⟩ hs

/-- The open unpaid exponent interval gives the same finite independence with its natural indexing. -/
theorem criticalPowerCoeff_interval_independent_mod_squareSums
    (s : Finset (Set.Ioo (0 : ℝ) (1 / 2))) (c : Set.Ioo (0 : ℝ) (1 / 2) → ℂ)
    (hpaid : Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1),
      ∑ α ∈ s, c α * (criticalPowerCoeff (α : ℝ) r : ℂ)‖ ^ 2)) :
    ∀ α ∈ s, c α = 0 := by
  classical
  let sr : Finset ℝ := s.image (fun α : Set.Ioo (0 : ℝ) (1 / 2) => (α : ℝ))
  let cr : ℝ → ℂ := fun a => if ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2) then c ⟨a, ha⟩ else 0
  have hc (α : Set.Ioo (0 : ℝ) (1 / 2)) : cr α = c α := by
    dsimp only [cr]
    rw [dif_pos α.property]
  have he (r : ℕ) : (∑ a ∈ sr, cr a * (criticalPowerCoeff a r : ℂ)) =
      ∑ α ∈ s, c α * (criticalPowerCoeff (α : ℝ) r : ℂ) := by
    symm
    refine sum_bij (fun α _ => (α : ℝ)) ?_ ?_ ?_ ?_
    · intro α hα
      exact mem_image.mpr ⟨α, hα, rfl⟩
    · intro α _ β _ h
      exact Subtype.ext h
    · intro a ha
      obtain ⟨α, hα, rfl⟩ := mem_image.mp ha
      exact ⟨α, hα, rfl⟩
    · intro α _
      rw [hc]
  have hs : Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1),
      ∑ a ∈ sr, cr a * (criticalPowerCoeff a r : ℂ)‖ ^ 2) := by
    simpa only [he] using hpaid
  have hz := criticalPowerCoeff_independent_mod_squareSums sr cr (by
    intro a ha
    obtain ⟨α, _, rfl⟩ := mem_image.mp ha
    exact α.property.2.le) hs
  intro α hα
  simpa only [hc] using hz (α : ℝ) (mem_image.mpr ⟨α, hα, rfl⟩)

end GaloisForLFunctions.BiarithmeticGeometry

