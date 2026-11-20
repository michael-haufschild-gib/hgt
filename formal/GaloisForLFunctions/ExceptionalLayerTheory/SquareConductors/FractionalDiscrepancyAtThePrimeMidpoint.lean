import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOuterCellsOfTheFractionalPrimeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons

/-!
# Fractional discrepancy at the prime midpoint

The two adjacent prime intervals have equal counting mass. Their centered
fractional discrepancy can therefore be tested against a single signed
difference of translated powers at any order between zero and one.
-/

noncomputable section

open MeasureTheory Finset
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

open GaloisForLFunctions.ExclusionOfTheCriticalState (ordinaryPrimeExcessCoeff)

private theorem centered_interval (a b : ℕ) :
    (∑ p ∈ Ioc a b, ordinaryPrimeExcessCoeff p) =
      (∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p) - (↑(b-a):ℝ) := by
  simp only [ordinaryPrimeExcessCoeff, sum_sub_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_one,
    Nat.card_Ioc]

/-- The entire centered field is tested before either interval is priced separately. -/
theorem integral_midpointFractionalField (n : ℕ) {b : ℝ} (hb : b ∈ Set.Ioo 0 1) :
    (∫ t, midpointFractionalTest n b t * midpointFractionalField n b t) =
      ProbabilityTheory.beta (1-b) b * primeMidpointPrice n := by
  let S := Ioc (2*n) (4*n)
  let B := ProbabilityTheory.beta (1-b) b
  have hi (j : ℕ) : Integrable (fun t => cutPower (-b) (t-j) * midpointFractionalField n b t) := by
    simpa only [show 1-b-1 = -b by ring, midpointFractionalField] using
      integrable_pairing S Nat.cast ordinaryPrimeExcessCoeff (sub_pos.mpr hb.2) hb.1 (j:ℝ)
  have ev (j : ℕ) :
      (∫ t, cutPower (-b) (t-j) * midpointFractionalField n b t) =
        B * ∑ p ∈ S.filter (j < ·), ordinaryPrimeExcessCoeff p := by
    simpa only [sum_filter, Nat.cast_lt, B, midpointFractionalField] using
      complementary_tail S Nat.cast ordinaryPrimeExcessCoeff hb (j:ℝ)
  have h₂ : S.filter (2*n < ·) = S := filter_true_of_mem fun p hp => (mem_Ioc.mp hp).1
  have h₃ : S.filter (3*n < ·) = Ioc (3*n) (4*n) := by
    ext p
    simp only [S, mem_filter, mem_Ioc]
    omega
  have hsplit := sum_Ioc_consecutive ordinaryPrimeExcessCoeff (show 2*n ≤ 3*n by omega)
    (show 3*n ≤ 4*n by omega)
  simp only [midpointFractionalTest, sub_mul, mul_assoc]
  rw [integral_sub (hi (2*n)) ((hi (3*n)).const_mul 2), integral_const_mul,
    ev, ev, h₂, h₃]
  change B * (∑ p ∈ Ioc (2*n) (4*n), ordinaryPrimeExcessCoeff p) - _ = _
  rw [← hsplit, centered_interval, centered_interval, primeMidpointPrice,
    show 3*n-2*n=n by omega, show 4*n-3*n=n by omega]
  dsimp only [B]
  ring

/-- At half order the signed square-root pairing is exactly π times the price. -/
theorem half_order_prime_midpoint (n : ℕ) :
    (∫ t, midpointFractionalTest n (1/2) t * midpointFractionalField n (1/2) t) =
      Real.pi * primeMidpointPrice n := by
  have h := integral_midpointFractionalField n (b := 1/2) (by constructor <;> norm_num)
  norm_num [ProbabilityTheory.beta, Real.Gamma_one_half_eq, Real.mul_self_sqrt Real.pi_pos.le] at h ⊢
  exact h

/-- The one-sided exponent of the unnormalized half-order pairing is the zero abscissa. -/
theorem half_order_prime_midpoint_spectrum {d : ℝ} (hd : 1/2 ≤ d) :
    (∀ t : ℝ, d < t → t < 1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (∫ x, midpointFractionalTest n (1/2) x * midpointFractionalField n (1/2) x) ≤ C*(n:ℝ)^t)
      ↔ _root_.RHTower.zetaZeroAbscissa ≤ d := by
  rw [← prime_midpoint_upper_spectrum_iff hd]
  simp_rw [half_order_prime_midpoint]
  constructor
  · intro h t hdt ht
    obtain ⟨C,hC⟩ := h t hdt ht
    refine ⟨C / Real.pi, fun n hn => ?_⟩
    calc
      primeMidpointPrice n ≤ (C*(n:ℝ)^t)/Real.pi :=
        (le_div_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm (primeMidpointPrice n)] using hC n hn)
      _ = _ := by ring
  · intro h t hdt ht
    obtain ⟨C,hC⟩ := h t hdt ht
    exact ⟨Real.pi*C, fun n hn => (mul_le_mul_of_nonneg_left (hC n hn) Real.pi_pos.le).trans_eq
      (mul_assoc _ _ _).symm⟩


end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
