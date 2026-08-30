import GaloisForLFunctions.RHTower.CCMLambertRadicalIntegrality
import Mathlib.Tactic

/-!
# Dyadic algebraic integrality of literal CCM Lambert coefficients

Connes--Consani--Moscovici equation (53) writes every matrix entry as a
Lambert series.  Its coefficient at `q^n` is a finite sum over the odd
divisors `2 * ell + 1` of `n`.  This module represents that literal finite
coefficient, including its sign and dyadic factor, and proves that a power of
`2` clears it to an algebraic integer.

The paper proves more: the radical factors lie in the cyclotomic integer ring.
That cyclotomic-containment theorem is intentionally not replaced here by the
weaker algebraic-integrality statement.
-/

namespace RHTower

noncomputable section

/-- Complex numbers becoming algebraic integers after multiplication by some
power of `2`. -/
def CCMDyadicIntegral (z : ℂ) : Prop :=
  ∃ d : ℕ, IsIntegral ℤ ((2 : ℂ) ^ d * z)

private theorem ccmTwoPow_isIntegral (d : ℕ) : IsIntegral ℤ ((2 : ℂ) ^ d) := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num]
  exact ((isIntegral_one : IsIntegral ℤ (1 : ℂ)).add isIntegral_one).pow d

/-- Dyadic algebraic integrality is closed under finite addition. -/
theorem CCMDyadicIntegral.add {x y : ℂ}
    (hx : CCMDyadicIntegral x) (hy : CCMDyadicIntegral y) :
    CCMDyadicIntegral (x + y) := by
  obtain ⟨d, hd⟩ := hx
  obtain ⟨e, he⟩ := hy
  refine ⟨d + e, ?_⟩
  have hleft : IsIntegral ℤ ((2 : ℂ) ^ e * ((2 : ℂ) ^ d * x)) :=
    (ccmTwoPow_isIntegral e).mul hd
  have hright : IsIntegral ℤ ((2 : ℂ) ^ d * ((2 : ℂ) ^ e * y)) :=
    (ccmTwoPow_isIntegral d).mul he
  rw [pow_add, mul_add]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hleft.add hright

/-- A finite sum of dyadically algebraic-integral complex numbers is again
dyadically algebraic integral. -/
theorem ccmDyadicIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ a ∈ s, CCMDyadicIntegral (f a)) :
    CCMDyadicIntegral (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- The `ell`th summand in the literal CCM equation-(53) entry, represented
without a choice of fractional powers of two.  The factor `2 * sqrt(2)` is
exactly `2^(3/2)`. -/
def ccmLambertEntrySummand (ell i j : ℕ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) ^ (j + ell) * (2 * (Real.sqrt 2 : ℂ)) * z) /
    (2 : ℂ) ^ (2 * ell + i + j)

private theorem ccmSqrtTwo_isIntegral : IsIntegral ℤ (Real.sqrt 2 : ℂ) := by
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtC : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, hsqrt]
    norm_num
  rw [hsqrtC]
  convert (isIntegral_algebraMap : IsIntegral ℤ ((algebraMap ℤ ℂ) (2 : ℤ))) using 1
  norm_num

/-- Every individual equation-(53) Lambert summand becomes an algebraic
integer after its literal dyadic denominator is cleared. -/
theorem ccmLambertEntrySummand_dyadicIntegral (ell i j : ℕ) (z : ℂ)
    (hz : z ^ 2 = (ccmLambertRadicand ell i j : ℂ)) :
    CCMDyadicIntegral (ccmLambertEntrySummand ell i j z) := by
  refine ⟨2 * ell + i + j, ?_⟩
  rw [ccmLambertEntrySummand, mul_div_cancel₀]
  · exact (((isIntegral_one : IsIntegral ℤ (1 : ℂ)).neg.pow _).mul
      ((isIntegral_algebraMap : IsIntegral ℤ (2 : ℂ)).mul ccmSqrtTwo_isIntegral)).mul
        (ccmLambertRadical_isIntegral ell i j z hz)
  · exact pow_ne_zero _ (by norm_num)

/-- The literal coefficient of `q^n` in CCM equation (53), with a chosen
square root at every finite-rank source index.  The Lambert series has zero
constant coefficient: `q^(2 * ell + 1) / (1 - q^(2 * ell + 1))` contributes
only at positive degrees. -/
def ccmLambertEntryCoefficient (i j n : ℕ) (rad : ℕ → ℂ) : ℂ :=
  if n = 0 then 0 else
    ∑ ell ∈ Finset.range (n + 1),
      if 2 * ell + 1 ∣ n then ccmLambertEntrySummand ell i j (rad ell) else 0

theorem ccmLambertEntryCoefficient_zero (i j : ℕ) (rad : ℕ → ℂ) :
    ccmLambertEntryCoefficient i j 0 rad = 0 := by
  simp [ccmLambertEntryCoefficient]

/-- Every literal finite divisor coefficient of CCM equation (53) is an
algebraic integer after multiplication by a power of `2`.  This proves the
dyadic algebraic-integrality part of the paper's coefficient argument, but
not its stronger cyclotomic-containment assertion. -/
theorem ccmLambertEntryCoefficient_dyadicIntegral (i j n : ℕ) (rad : ℕ → ℂ)
    (hrad : ∀ ell, (rad ell) ^ 2 = (ccmLambertRadicand ell i j : ℂ)) :
    CCMDyadicIntegral (ccmLambertEntryCoefficient i j n rad) := by
  unfold ccmLambertEntryCoefficient
  split_ifs with hn
  · exact ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))⟩
  · apply ccmDyadicIntegral_sum
    intro ell _
    split_ifs with hdiv
    · exact ccmLambertEntrySummand_dyadicIntegral ell i j (rad ell) (hrad ell)
    · exact ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))⟩

end

end RHTower
