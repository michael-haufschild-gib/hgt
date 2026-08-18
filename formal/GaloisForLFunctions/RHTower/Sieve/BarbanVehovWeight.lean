import GaloisForLFunctions.RHTower.Sieve.LinearMollifierVonMangoldt

/-!
# The Barban–Vehov weight

The linear Levinson mollifier attaches to `m` the weight `μ(m) log(X/m)` truncated at `m ≤ X`.
The associated divisor coefficient is the Barban–Vehov coefficient

`b_X(k) = ∑_{m ∣ k, m ≤ X} μ(m) log(X/m)`,

which equals the von Mangoldt weight `Λ(k)` on the short range `k ≤ X` and is a genuinely partial
divisor sum beyond it.  Its mean square is Graham's theorem
`∑_{k ≤ N} b_X(k)² = N log X + O(N)`, which is the remaining analytic input of the mollified second
moment.  This module fixes the object and records the facts already available.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHTower.Sieve

/-- The Barban–Vehov weight at `m`, truncated at length `X`. -/
def barbanVehovWeight (X m : ℕ) : ℝ :=
  if m ≤ X then (μ m : ℝ) * Real.log ((X : ℝ) / (m : ℝ)) else 0

/-- The Barban–Vehov divisor coefficient `b_X(k) = ∑_{m ∣ k, m ≤ X} μ(m) log(X/m)`. -/
def barbanVehovCoeff (X k : ℕ) : ℝ := ∑ m ∈ k.divisors, barbanVehovWeight X m

theorem barbanVehovCoeff_eq_sum_filter (X k : ℕ) :
    barbanVehovCoeff X k
      = ∑ m ∈ k.divisors.filter (fun m => m ≤ X), (μ m : ℝ) * Real.log ((X : ℝ) / (m : ℝ)) := by
  rw [barbanVehovCoeff, Finset.sum_filter]
  rfl

/-- **On the short range the Barban–Vehov coefficient is the von Mangoldt weight.** -/
theorem barbanVehovCoeff_eq_vonMangoldt {k X : ℕ} (hk : 1 < k) (hkX : k ≤ X) :
    barbanVehovCoeff X k = vonMangoldt k := by
  rw [barbanVehovCoeff_eq_sum_filter]
  exact sum_moebius_filter_log_div_eq_vonMangoldt hk hkX

theorem barbanVehovCoeff_one {X : ℕ} (hX : 1 ≤ X) :
    barbanVehovCoeff X 1 = Real.log (X : ℝ) := by
  rw [barbanVehovCoeff_eq_sum_filter, filter_le_divisors_eq Nat.one_pos hX]
  simp

/-- The crude majorant: the coefficient never exceeds the divisor count times `log X`. -/
theorem abs_barbanVehovCoeff_le {X k : ℕ} (hX : 1 ≤ X) :
    |barbanVehovCoeff X k| ≤ (k.divisors.card : ℝ) * Real.log (X : ℝ) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  rw [barbanVehovCoeff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ k.divisors, |barbanVehovWeight X m| ≤ Real.log (X : ℝ) := by
    intro m hm
    have hmpos : 0 < m := Nat.pos_of_mem_divisors hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    rw [barbanVehovWeight]
    split_ifs with hmX
    · have hmXR : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hmX
      have h0 : (0 : ℝ) ≤ Real.log ((X : ℝ) / (m : ℝ)) := by
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ (by linarith)]
        linarith
      have hle : Real.log ((X : ℝ) / (m : ℝ)) ≤ Real.log (X : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      rw [abs_mul, abs_of_nonneg h0]
      calc |(μ m : ℝ)| * Real.log ((X : ℝ) / (m : ℝ))
          ≤ 1 * Real.log ((X : ℝ) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right (abs_moebius_le_one m) h0
        _ = Real.log ((X : ℝ) / (m : ℝ)) := one_mul _
        _ ≤ Real.log (X : ℝ) := hle
    · rw [abs_zero]
      exact hlogX
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [nsmul_eq_mul]

end RHTower.Sieve

end
