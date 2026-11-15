import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanUniformSupport

/-!
# Both signs occur with fixed amplitude in every prime-field family

The exact first two moments force a positive mass of each sign. Removing values
of absolute size below `1/12` loses at most half the available mass, and the
uniform support bound converts the retained mass into a count. At least `p/36`
parameters have each sign and standardized amplitude at least `1/12`.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

private theorem positive_amplitude_count {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hmean : ∑ i, f i = 0)
    (hvar : ∑ i, f i ^ 2 = Fintype.card ι) (hbound : ∀ i, |f i| ≤ 3) :
    (Fintype.card ι : ℝ) ≤ 36 * (univ.filter (fun i => 1 / 12 ≤ f i)).card := by
  classical
  have hpoint (i : ι) :
      f i ^ 2 ≤ -3 * f i + 1 / 2 + if 1 / 12 ≤ f i then 18 else 0 := by
    have hb := hbound i
    have hs : f i ^ 2 ≤ 3 * |f i| := by
      have h := mul_nonneg (abs_nonneg (f i)) (sub_nonneg.mpr hb)
      nlinarith only [h, sq_abs (f i)]
    split_ifs with hi
    · have hab := (abs_le.mp hb).2
      nlinarith only [hs, hb, hab]
    · by_cases hz : f i ≤ 0
      · rw [abs_of_nonpos hz] at hs
        linarith only [hs]
      · rw [abs_of_pos (lt_of_not_ge hz)] at hs
        linarith only [hs, lt_of_not_ge hi]
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hpoint i)
  rw [hvar, sum_add_distrib, sum_add_distrib, ← mul_sum, hmean, mul_zero,
    zero_add, sum_const, nsmul_eq_mul, card_univ] at hsum
  have hc : (∑ i : ι, if 1 / 12 ≤ f i then (18 : ℝ) else 0) =
      18 * (univ.filter (fun i => 1 / 12 ≤ f i)).card := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [hc] at hsum
  linarith only [hsum]

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

private theorem standardized_trace_sum (p : Nat.Primes) :
    ∑ a : ZMod p.val, standardizedKloostermanTrace p a = 0 := by
  simp only [standardizedKloostermanTrace, ← sum_div, sum_primeKloostermanTrace,
    zero_div]

private theorem standardized_trace_square_sum (p : Nat.Primes) :
    ∑ a : ZMod p.val, standardizedKloostermanTrace p a ^ 2 = (p.val : ℝ) := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  simp only [standardizedKloostermanTrace, div_pow,
    Real.sq_sqrt (show 0 ≤ (p.val : ℝ) - 1 by linarith), ← sum_div,
    sum_primeKloostermanTrace_sq]
  exact mul_div_cancel_right₀ _ (ne_of_gt (sub_pos.mpr hp))

/-- A uniform fraction of the complete family has positive standardized amplitude. -/
theorem primeKloosterman_positive_amplitude_count (p : Nat.Primes) :
    (p.val : ℝ) ≤ 36 * ((univ : Finset (ZMod p.val)).filter
      (fun a => 1 / 12 ≤ standardizedKloostermanTrace p a)).card := by
  simpa only [ZMod.card] using positive_amplitude_count
    (standardizedKloostermanTrace p) (standardized_trace_sum p)
    (by simpa only [ZMod.card] using standardized_trace_square_sum p)
    (abs_standardizedKloostermanTrace_le_three p)

/-- The same fraction has negative standardized amplitude; centering treats both signs equally. -/
theorem primeKloosterman_negative_amplitude_count (p : Nat.Primes) :
    (p.val : ℝ) ≤ 36 * ((univ : Finset (ZMod p.val)).filter
      (fun a => standardizedKloostermanTrace p a ≤ -1 / 12)).card := by
  have h := positive_amplitude_count (fun a => -standardizedKloostermanTrace p a)
    (by rw [sum_neg_distrib, standardized_trace_sum, neg_zero])
    (by simpa only [neg_sq, ZMod.card] using standardized_trace_square_sum p)
    (fun a => by simpa only [abs_neg] using abs_standardizedKloostermanTrace_le_three p a)
  have he (x : ℝ) : 1 / 12 ≤ -x ↔ x ≤ -1 / 12 := by constructor <;> intro hx <;> linarith
  simpa only [he, ZMod.card] using h

#print axioms primeKloosterman_positive_amplitude_count
#print axioms primeKloosterman_negative_amplitude_count

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
