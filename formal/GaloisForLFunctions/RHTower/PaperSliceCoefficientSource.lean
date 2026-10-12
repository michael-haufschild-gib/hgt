import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion

/-! # The full signed Taylor source has finite negative support

Entire Taylor summability supplies a bounded coefficient sequence tending to zero.
The native high-order sign theorem confines every negative coefficient to a finite
low-order set at each height. No coefficient is discarded or rescaled.
-/

noncomputable section

open Filter Set
open scoped Topology ComplexOrder

namespace RHTower.PaperSliceCoefficient

abbrev Height := {t : ℝ // 0 ≤ t}

/-- The original coefficient, real by the Xi reflection law. -/
def coefficient (t : ℝ) (n : ℕ) : ℝ := (xiSliceCoeff t n).re

theorem coefficient_cast (t : ℝ) (n : ℕ) :
    (coefficient t n : ℂ) = xiSliceCoeff t n := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, xiSliceCoeff_im_eq_zero]

theorem hasSum_source (t : ℝ) (x : ℂ) :
    HasSum (fun n => (coefficient t n : ℂ) * x ^ n) (xiSliceProduct t x) := by
  simpa only [coefficient_cast] using hasSum_xiSliceCoeff t x

theorem summable_source (t : ℝ) : Summable (xiSliceCoeff t) := by
  simpa only [one_pow, mul_one] using (hasSum_xiSliceCoeff t 1).summable

theorem summable_norm_source (t : ℝ) : Summable (fun n => ‖xiSliceCoeff t n‖) :=
  (summable_source t).norm

/-- The actual absolute coefficient mass supplies the operator bound. -/
def budget (t : ℝ) : ℝ := ∑' n, ‖xiSliceCoeff t n‖

theorem budget_nonneg (t : ℝ) : 0 ≤ budget t := tsum_nonneg fun _ => norm_nonneg _

theorem norm_source_le_budget (t : ℝ) (n : ℕ) : ‖xiSliceCoeff t n‖ ≤ budget t :=
  (summable_norm_source t).le_tsum n (fun _ _ => norm_nonneg _)

theorem abs_coefficient_le_budget (t : ℝ) (n : ℕ) : |coefficient t n| ≤ budget t := by
  have h := norm_source_le_budget t n
  rw [← coefficient_cast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem tendsto_source_zero (t : ℝ) : Tendsto (xiSliceCoeff t) atTop (𝓝 0) :=
  (summable_source t).tendsto_atTop_zero

theorem coefficient_odd (t : ℝ) (k : ℕ) : coefficient t (2 * k + 1) = 0 := by
  simp only [coefficient, xiSliceCoeff_odd_eq_zero, Complex.zero_re]

/-- The source's negative coefficients occur only below a logarithmic even-order threshold. -/
theorem exists_negative_order_bound : ∃ K κ : ℝ, ∀ t : Height, ∀ n : ℕ,
    coefficient t n < 0 → ∃ k : ℕ, n = 2 * k ∧ (k : ℝ) < max K (κ * Real.log t) := by
  obtain ⟨K, κ, h⟩ := exists_xiSliceCoeff_pos_high_order
  refine ⟨K, κ, fun t n hn => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · refine ⟨k, rfl, ?_⟩
    by_contra hk
    have hp := (h t t.property k (le_of_not_gt hk)).le
    have hr := (Complex.nonneg_iff.mp hp).1
    exact not_lt_of_ge hr hn
  · rw [coefficient_odd] at hn
    exact (lt_irrefl _ hn).elim

theorem finite_negative_support (t : Height) : {n : ℕ | coefficient t n < 0}.Finite := by
  obtain ⟨K, κ, h⟩ := exists_negative_order_bound
  obtain ⟨N, hN⟩ := exists_nat_gt (max K (κ * Real.log t))
  apply (finite_Iio (2 * N)).subset
  intro n hn
  obtain ⟨k, rfl, hk⟩ := h t n hn
  have hkN : k < N := by exact_mod_cast hk.trans hN
  exact Nat.mul_lt_mul_of_pos_left hkN (by norm_num)

/-- Every negative coordinate of the full signed source. -/
def negatives (t : Height) : Finset ℕ := (finite_negative_support t).toFinset

@[simp] theorem mem_negatives (t : Height) (n : ℕ) :
    n ∈ negatives t ↔ coefficient t n < 0 := Set.Finite.mem_toFinset _

/-- Exact number of negative coefficient directions. -/
def negativeCount (t : Height) : ℕ := (negatives t).card

theorem nonneg_of_not_mem_negatives (t : Height) {n : ℕ} (hn : n ∉ negatives t) :
    0 ≤ coefficient t n := le_of_not_gt (fun h => hn ((mem_negatives t n).2 h))

theorem negativeCount_zero_iff (t : Height) :
    negativeCount t = 0 ↔ ∀ n, 0 ≤ coefficient t n := by
  simp only [negativeCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem,
    mem_negatives, not_lt]

theorem all_negativeCount_zero_iff :
    (∀ t : Height, negativeCount t = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_xiSliceCoeff_nonneg_of_nonneg_height
    intro t ht n
    rw [← coefficient_cast]
    exact Complex.zero_le_real.mpr ((negativeCount_zero_iff ⟨t, ht⟩).1 (h ⟨t, ht⟩) n)
  · intro h t
    apply (negativeCount_zero_iff t).2
    intro n
    exact (Complex.nonneg_iff.mp (xiSliceCoeff_nonneg_of_riemannHypothesis h t n)).1

end RHTower.PaperSliceCoefficient
