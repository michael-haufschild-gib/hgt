import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimateSharp
import GaloisForLFunctions.RHTower.Sieve.TypeIIBlockBounds

/-!
# The type-I totals as explicit powers

The fibre bound at the divisor `b` splits into a part independent of `b` and a part proportional
to `1/b`: the curvature scale `T r / A` is invariant under the dilation `u ↦ b u`, while the length
of the fibre shrinks like `1/b`.  Summing over the support of the coefficient therefore costs one
factor of the support length on the first part and one harmonic sum on the second.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The `b`-independent part of the fibre bound. -/
def fibreKernel (T r : ℝ) (A : ℕ) : ℝ := 2500 * Real.sqrt (T * r / (36 * Real.pi * A))

/-- The part of the fibre bound proportional to `1/b`. -/
def fibreTail (T r : ℝ) (B : ℕ) : ℝ :=
  22 * Real.sqrt (36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r))

theorem fibreKernel_nonneg (T r : ℝ) (A : ℕ) : 0 ≤ fibreKernel T r A := by
  rw [fibreKernel]; positivity

theorem fibreTail_nonneg (T r : ℝ) (B : ℕ) : 0 ≤ fibreTail T r B := by
  rw [fibreTail]; positivity

/-- The fibre's left endpoint is at least the dilated block endpoint. -/
theorem le_cast_fibre_low {A b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b) :
    (A : ℝ) / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hnat : A ≤ ((A - 1) / b + 1) * b := by
    calc A = b * ((A - 1) / b) + (A - 1) % b + 1 := by rw [Nat.div_add_mod]; omega
      _ ≤ b * ((A - 1) / b) + b := by
          have := Nat.mod_lt (A - 1) (show 0 < b by omega)
          omega
      _ = ((A - 1) / b + 1) * b := by ring
  rw [div_le_iff₀ hb0]
  exact_mod_cast hnat

/-- The fibre's right endpoint is at most twice the dilated block endpoint. -/
theorem cast_fibre_high_le {B b : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    (b : ℝ) * (((B - 1) / b + 1 : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
  have hnat : b * ((B - 1) / b + 1) ≤ 2 * B := by
    have h1 : (B - 1) / b * b ≤ B - 1 := Nat.div_mul_le_self (B - 1) b
    have h2 : b * ((B - 1) / b + 1) = (B - 1) / b * b + b := by ring
    omega
  exact_mod_cast hnat

/-- **The fibre bound splits.** -/
theorem fibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b)
    (hbB : b ≤ B) :
    fibreBound T r A B b ≤ fibreKernel T r A + fibreTail T r B / b := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (le_trans hb hbB)
  have hTr : (0 : ℝ) < T * r := by positivity
  have hlow := le_cast_fibre_low hA hb
  have hhigh := cast_fibre_high_le hb hbB
  have hlow0 : (0 : ℝ) < (((A - 1) / b + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hlow
  have hhigh0 : (0 : ℝ) ≤ (((B - 1) / b + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfirst : 2500 * Real.sqrt (T * (r / b) / (36 * Real.pi * (((A - 1) / b + 1 : ℕ) : ℝ)))
      ≤ fibreKernel T r A := by
    rw [fibreKernel]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
    have hstep : T * (r / b) / (36 * Real.pi * (((A - 1) / b + 1 : ℕ) : ℝ))
        ≤ T * (r / b) / (36 * Real.pi * ((A : ℝ) / b)) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [hlow]
    have heq : T * (r / b) / (36 * Real.pi * ((A : ℝ) / b)) = T * r / (36 * Real.pi * A) := by
      field_simp
    linarith [hstep, heq]
  have hsecond : 22 * Real.sqrt (36 * Real.pi / (T * (r / b)))
      * Real.sqrt ((((B - 1) / b + 1 : ℕ) : ℝ) ^ 3) ≤ fibreTail T r B / b := by
    have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
    have hkey : ((b : ℝ) * (((B - 1) / b + 1 : ℕ) : ℝ)) ^ 3 ≤ (2 * (B : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hhigh 3
    have harg : 36 * Real.pi / (T * (r / (b : ℝ))) * ((((B - 1) / b + 1 : ℕ)) : ℝ) ^ 3
        ≤ 36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r) / (b : ℝ) ^ 2 := by
      have e1 : 36 * Real.pi / (T * (r / (b : ℝ))) * ((((B - 1) / b + 1 : ℕ)) : ℝ) ^ 3
          = (36 * Real.pi * (b : ℝ) * ((((B - 1) / b + 1 : ℕ)) : ℝ) ^ 3) / (T * r) := by
        field_simp
      have e2 : 36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r) / (b : ℝ) ^ 2
          = (36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (b : ℝ) ^ 2) / (T * r) := by
        field_simp
      rw [e1, e2]
      have hnum : 36 * Real.pi * (b : ℝ) * ((((B - 1) / b + 1 : ℕ)) : ℝ) ^ 3
          ≤ 36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (b : ℝ) ^ 2 := by
        rw [le_div_iff₀ hb2]
        nlinarith [hkey, hpi]
      exact div_le_div_of_nonneg_right hnum hTr.le
    have hstep : Real.sqrt (36 * Real.pi / (T * (r / (b : ℝ)))
        * ((((B - 1) / b + 1 : ℕ)) : ℝ) ^ 3)
        ≤ Real.sqrt (36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r) / (b : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt harg
    rw [Real.sqrt_div
      (show (0:ℝ) ≤ 36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r) by positivity) ((b : ℝ) ^ 2),
      Real.sqrt_sq hb0.le] at hstep
    have hxnn : (0 : ℝ) ≤ 36 * Real.pi / (T * (r / (b : ℝ))) :=
      le_of_lt (div_pos (by positivity) (mul_pos hT (div_pos hr hb0)))
    calc 22 * Real.sqrt (36 * Real.pi / (T * (r / (b : ℝ))))
            * Real.sqrt ((((B - 1) / b + 1 : ℕ) : ℝ) ^ 3)
        = 22 * (Real.sqrt (36 * Real.pi / (T * (r / (b : ℝ))))
            * Real.sqrt ((((B - 1) / b + 1 : ℕ) : ℝ) ^ 3)) := by ring
      _ = 22 * Real.sqrt (36 * Real.pi / (T * (r / (b : ℝ)))
            * (((B - 1) / b + 1 : ℕ) : ℝ) ^ 3) := by rw [Real.sqrt_mul hxnn]
      _ ≤ 22 * (Real.sqrt (36 * Real.pi * (2 * (B : ℝ)) ^ 3 / (T * r)) / (b : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 22)
      _ = fibreTail T r B / b := by rw [fibreTail]; ring
  rw [fibreBound]
  linarith [hfirst, hsecond]

/-- **The first type-I total.** -/
theorem sum_log_fibreBound_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B K : ℕ} (hA : 1 ≤ A)
    (hK : 1 ≤ K) (hKB : K ≤ B) :
    (∑ b ∈ Finset.Icc 1 K, Real.log b * fibreBound T r A B b)
      ≤ Real.log K * ((K : ℝ) * fibreKernel T r A + fibreTail T r B * invSum K) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hstep : ∀ b ∈ Finset.Icc 1 K, Real.log b * fibreBound T r A B b
      ≤ Real.log K * (fibreKernel T r A + fibreTail T r B / b) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1
    have hlogb : (0 : ℝ) ≤ Real.log b := Real.log_nonneg hb1
    have hlogle : Real.log b ≤ Real.log K := Real.log_le_log (by linarith) (by exact_mod_cast hb.2)
    have hfb := fibreBound_le hT hr hA hb.1 (le_trans hb.2 hKB)
    have hfbnn : (0 : ℝ) ≤ fibreBound T r A B b := by rw [fibreBound]; positivity
    have hbnd : (0 : ℝ) ≤ fibreKernel T r A + fibreTail T r B / b := by
      have := fibreKernel_nonneg T r A
      have := fibreTail_nonneg T r B
      positivity
    nlinarith [hfb, hlogb, hlogle, hfbnn, hbnd]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
  have hcard : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by push_cast; ring
  have htail : (∑ b ∈ Finset.Icc 1 K, fibreTail T r B / (b : ℝ))
      = fibreTail T r B * invSum K := by
    rw [invSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [mul_one_div]
  rw [htail, nsmul_eq_mul, hcard]

/-- **The second type-I total.** -/
theorem sum_two_fibreBound_log_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B K : ℕ} (hA : 1 ≤ A)
    (hK : 1 ≤ K) (hKB : K ≤ B) :
    (∑ b ∈ Finset.Icc 1 K,
        2 * fibreBound T r A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))
      ≤ 2 * Real.log B * ((K : ℝ) * fibreKernel T r A + fibreTail T r B * invSum K) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans hK hKB
  have hstep : ∀ b ∈ Finset.Icc 1 K,
      2 * fibreBound T r A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)
        ≤ 2 * Real.log B * (fibreKernel T r A + fibreTail T r B / b) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
    have hlogle : Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) ≤ Real.log B := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]
        simpa using hlogB
      · refine Real.log_le_log (by exact_mod_cast h) ?_
        have hle : (B - 1) / b + 1 - 1 ≤ B := by
          have := Nat.div_le_self (B - 1) b
          omega
        exact_mod_cast hle
    have hlognn : (0 : ℝ) ≤ Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ) := by
      rcases Nat.eq_zero_or_pos ((B - 1) / b + 1 - 1) with h | h
      · rw [h]; simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have hfb := fibreBound_le hT hr hA hb.1 (le_trans hb.2 hKB)
    have hfbnn : (0 : ℝ) ≤ fibreBound T r A B b := by rw [fibreBound]; positivity
    have hbnd : (0 : ℝ) ≤ fibreKernel T r A + fibreTail T r B / b := by
      have := fibreKernel_nonneg T r A
      have := fibreTail_nonneg T r B
      have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb.1
      positivity
    nlinarith [hfb, hlogle, hlognn, hfbnn, hbnd, hlogB]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
  have hcard : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by push_cast; ring
  have htail : (∑ b ∈ Finset.Icc 1 K, fibreTail T r B / (b : ℝ))
      = fibreTail T r B * invSum K := by
    rw [invSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [mul_one_div]
  rw [htail, nsmul_eq_mul, hcard]

end

end RHTower.Sieve
