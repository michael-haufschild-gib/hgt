import GaloisForLFunctions.RHTower.Sieve.GeneralizedDivisorShortInterval
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundary

/-!
# Mean square of the product-scale boundary

Once the unsigned aggregate of a box family is bounded by one fixed generalized-divisor
coefficient, the exact endpoint-collar geometry converts its boundary mean square into two local
generalized-divisor moments.  No family-cardinality factor occurs.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

def mtLowerProductScaleCollar (Y eta : ℝ) : Finset ℕ :=
  Finset.Ioc (Nat.floor (Y / 2)) (Nat.floor ((1 + eta) * (Y / 2)))

def mtUpperProductScaleCollar (Y eta : ℝ) : Finset ℕ :=
  Finset.Ioc (Nat.floor (4 * Y)) (Nat.floor ((1 + eta) * (4 * Y)))

/-- The boundary square is paid by the two collar-local generalized-divisor squares. -/
theorem sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    {ι : Type*} [DecidableEq ι]
    (A : Finset ℕ) (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ)
    (Y eta : ℝ) (r : ℕ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hsupport : ∀ i ∈ S,
      MTRealScaleSupported (F i) (M i) ((1 + eta) * M i))
    (haggregate : ∀ n,
      ∑ i ∈ S, ‖F i n‖ ≤
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ)) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ (2 : ℕ) ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ))) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ)) := by
  let E := mtProductScaleBoundaryErrorAF S F M Y
  let G := fun n => ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ))
  let C₁ := mtLowerProductScaleCollar Y eta
  let C₂ := mtUpperProductScaleCollar Y eta
  have hpoint : ∀ n,
      ‖E n‖ ^ (2 : ℕ) ≤ (if n ∈ C₁ then G n else 0) + (if n ∈ C₂ then G n else 0) := by
    intro n
    by_cases hE : E n = 0
    · simp only [hE, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      split_ifs <;> positivity
    have hcollar := mtProductScaleBoundaryErrorAF_mem_endpointCollars
      S F M Y eta hY heta hsupport hE
    have hnorm : ‖E n‖ ≤
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) :=
      (norm_mtProductScaleBoundaryErrorAF_apply_le S F M Y n).trans (haggregate n)
    have hsq : ‖E n‖ ^ (2 : ℕ) ≤ G n := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rcases hcollar with hC₁ | hC₂
    · have hmem : n ∈ C₁ := by simpa [C₁, mtLowerProductScaleCollar] using hC₁
      simp only [hmem, if_true]
      exact hsq.trans (le_add_of_nonneg_right (by positivity))
    · have hmem : n ∈ C₂ := by simpa [C₂, mtUpperProductScaleCollar] using hC₂
      simp only [hmem, if_true]
      exact hsq.trans (le_add_of_nonneg_left (by positivity))
  have hsubset₁ : A.filter (fun n => n ∈ C₁) ⊆ C₁ := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hsubset₂ : A.filter (fun n => n ∈ C₂) ⊆ C₂ := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  calc
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ (2 : ℕ) =
        ∑ n ∈ A, ‖E n‖ ^ (2 : ℕ) := rfl
    _ ≤ ∑ n ∈ A,
        ((if n ∈ C₁ then G n else 0) + (if n ∈ C₂ then G n else 0)) := by
      exact Finset.sum_le_sum fun n hn => hpoint n
    _ = (∑ n ∈ A.filter (fun n => n ∈ C₁), G n) +
          ∑ n ∈ A.filter (fun n => n ∈ C₂), G n := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ ≤ (∑ n ∈ C₁, G n) + ∑ n ∈ C₂, G n := by
      apply add_le_add
      · exact Finset.sum_le_sum_of_subset_of_nonneg hsubset₁
          (fun n hn hnot => by positivity)
      · exact Finset.sum_le_sum_of_subset_of_nonneg hsubset₂
          (fun n hn hnot => by positivity)
    _ = (∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ)) := rfl

/-- Fully explicit two-collar polylog bound. -/
theorem sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_polylog
    {ι : Type*} [DecidableEq ι]
    (A : Finset ℕ) (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ)
    (Y eta : ℝ) (r T : ℕ) (hr : 2 ≤ r) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hsupport : ∀ i ∈ S,
      MTRealScaleSupported (F i) (M i) ((1 + eta) * M i))
    (haggregate : ∀ n,
      ∑ i ∈ S, ‖F i n‖ ≤
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ))
    (hT : 1 ≤ T)
    (hL₁ : 1 ≤ Nat.floor (Y / 2))
    (hL₂ : 1 ≤ Nat.floor (4 * Y))
    (hLU₁ : Nat.floor (Y / 2) ≤ Nat.floor ((1 + eta) * (Y / 2)))
    (hLU₂ : Nat.floor (4 * Y) ≤ Nat.floor ((1 + eta) * (4 * Y)))
    (hTU₁ : T ≤ Nat.floor ((1 + eta) * (Y / 2)))
    (hTU₂ : T ≤ Nat.floor ((1 + eta) * (4 * Y)))
    (hpow₁ : T ^ (r ^ (2 : ℕ)) ≤ Nat.floor (Y / 2))
    (hpow₂ : T ^ (r ^ (2 : ℕ)) ≤ Nat.floor (4 * Y)) :
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ (2 : ℕ) ≤
      ((r ^ (2 : ℕ) : ℕ) : ℝ) *
        (((Nat.floor ((1 + eta) * (Y / 2)) - Nat.floor (Y / 2) : ℕ) : ℝ) *
            (1 + Real.log (Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ)) ^
              (r ^ (2 : ℕ) - 1) +
          ((Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ) : ℝ) *
            (1 + Real.log (Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ)) ^
              (r ^ (2 : ℕ) - 2)) +
      ((r ^ (2 : ℕ) : ℕ) : ℝ) *
        (((Nat.floor ((1 + eta) * (4 * Y)) - Nat.floor (4 * Y) : ℕ) : ℝ) *
            (1 + Real.log (Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ)) ^
              (r ^ (2 : ℕ) - 1) +
          ((Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ) : ℝ) *
            (1 + Real.log (Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ)) ^
              (r ^ (2 : ℕ) - 2)) := by
  calc
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ (2 : ℕ) ≤
        (∑ n ∈ mtLowerProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ))) +
        ∑ n ∈ mtUpperProductScaleCollar Y eta,
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℝ) ^ (2 : ℕ)) :=
      sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
        A S F M Y eta r hY heta hsupport haggregate
    _ ≤ ((r ^ (2 : ℕ) : ℕ) : ℝ) *
          (((Nat.floor ((1 + eta) * (Y / 2)) - Nat.floor (Y / 2) : ℕ) : ℝ) *
              (1 + Real.log (Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ)) ^
                (r ^ (2 : ℕ) - 1) +
            ((Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ) : ℝ) *
              (1 + Real.log (Nat.floor ((1 + eta) * (Y / 2)) / T : ℕ)) ^
                (r ^ (2 : ℕ) - 2)) +
        ((r ^ (2 : ℕ) : ℕ) : ℝ) *
          (((Nat.floor ((1 + eta) * (4 * Y)) - Nat.floor (4 * Y) : ℕ) : ℝ) *
              (1 + Real.log (Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ)) ^
                (r ^ (2 : ℕ) - 1) +
            ((Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ) : ℝ) *
              (1 + Real.log (Nat.floor ((1 + eta) * (4 * Y)) / T : ℕ)) ^
                (r ^ (2 : ℕ) - 2)) := by
      apply add_le_add
      · simpa [mtLowerProductScaleCollar] using
          sum_zeta_pow_sq_Ioc_le_polylog r T
            (Nat.floor (Y / 2)) (Nat.floor ((1 + eta) * (Y / 2)))
            hr hT hL₁ hLU₁ hTU₁ hpow₁
      · simpa [mtUpperProductScaleCollar] using
          sum_zeta_pow_sq_Ioc_le_polylog r T
            (Nat.floor (4 * Y)) (Nat.floor ((1 + eta) * (4 * Y)))
            hr hT hL₂ hLU₂ hTU₂ hpow₂

end

end RHTower.Sieve
