import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationMasks
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Finite valuation splitting of Dirichlet convolution

Exact prime valuation is additive on the nonzero divisor pairs in a Dirichlet
convolution. Thus every fixed valuation component is a finite convolution sum.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem valuationMask_eq_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (k : ℕ) : valuationMask p k n = if n.factorization p = k then 1 else 0 := by
  have he : (p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n) ↔ n.factorization p = k := by
    rw [hp.pow_dvd_iff_le_factorization hn, hp.pow_dvd_iff_le_factorization hn]
    omega
  simp only [valuationMask, he]

private theorem valuation_indicator_add (a b k : ℕ) :
    (if a + b = k then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.range (k + 1),
        (if a = j then 1 else 0) * (if b = k - j then 1 else 0) := by
  by_cases ha : a ≤ k
  · rw [Finset.sum_eq_single a]
    · have he : a + b = k ↔ b = k - a := by omega
      simp [he]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · rw [if_neg (by omega)]
    · intro j hj
      rw [if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul]

theorem valuationMask_mul {p a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (k : ℕ) :
    valuationMask p k (a * b) = ∑ j ∈ Finset.range (k + 1),
      valuationMask p j a * valuationMask p (k - j) b := by
  simp_rw [valuationMask_eq_factorization hp (mul_ne_zero ha hb),
    valuationMask_eq_factorization hp ha, valuationMask_eq_factorization hp hb]
  rw [Nat.factorization_mul ha hb]
  exact valuation_indicator_add (a.factorization p) (b.factorization p) k

/-- No multiplicativity or coefficient sign is required. -/
theorem valuationPart_convolution {p : ℕ} (hp : p.Prime) (k : ℕ)
    (f g : ℕ → ℂ) :
    valuationPart p k (LSeries.convolution f g) =
      ∑ j ∈ Finset.range (k + 1),
        LSeries.convolution (valuationPart p j f) (valuationPart p (k - j) g) := by
  funext n
  simp only [valuationPart, LSeries.convolution_def, Finset.mul_sum,
    Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab hab
  obtain ⟨hn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have hab0 : ab.1 * ab.2 ≠ 0 := by rwa [hn]
  have ha : ab.1 ≠ 0 := fun h => hab0 (by rw [h, zero_mul])
  have hb : ab.2 ≠ 0 := fun h => hab0 (by rw [h, mul_zero])
  rw [← hn, valuationMask_mul hp ha hb]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem LSeries_valuationPart_convolution {p : ℕ} (hp : p.Prime) (k : ℕ)
    {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (valuationPart p k (LSeries.convolution f g)) s =
      ∑ j ∈ Finset.range (k + 1),
        LSeries (valuationPart p j f) s * LSeries (valuationPart p (k - j) g) s := by
  rw [valuationPart_convolution hp]
  rw [LSeries_sum (fun j _ => (summable_valuationPart p j hf).convolution
    (summable_valuationPart p (k - j) hg))]
  exact Finset.sum_congr rfl fun j _ =>
    LSeries_convolution' (summable_valuationPart p j hf)
      (summable_valuationPart p (k - j) hg)

end RHTower.WeilSingularArithmetic
