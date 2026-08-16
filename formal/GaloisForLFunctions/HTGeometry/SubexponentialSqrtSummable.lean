import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Summability of subexponential square-root decay

The sequence `e^{-a√n}` decays faster than any power, because `log` is little-o of every positive
power.  Cauchy condensation then makes `e^{-c√(log m)}/m` summable as well: it is exactly the
weight produced by a prime number theorem with square-root-logarithmic error.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **`e^{-a√n}` is summable.** -/
theorem summable_exp_neg_mul_sqrt {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-(a * Real.sqrt n))) := by
  have hlog : Real.log =o[atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)
  have hbound := hlog.def (c := a / 4) (by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hbound.and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (X ≤ (n : ℝ) + 1 ∧ 1 ≤ (n : ℝ)) := by
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge X
    refine ⟨N₁ + 1, fun n hn => ⟨?_, ?_⟩⟩
    · have : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N₁ ≤ n)
      linarith
    · have : (1 : ℕ) ≤ n := by omega
      exact_mod_cast this
  have hcomp : ∀ n : ℕ, N ≤ n → Real.exp (-(a * Real.sqrt n)) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    obtain ⟨hXn, hn1⟩ := hN n hn
    obtain ⟨hlogn, _⟩ := hX ((n : ℝ) + 1) hXn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hrpow : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) = Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.sqrt_eq_rpow]
    have hsqrt_le : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
      have h2 : (n : ℝ) + 1 ≤ 4 * (n : ℝ) := by linarith
      have := Real.sqrt_le_sqrt h2
      rw [show (4 : ℝ) * (n : ℝ) = 2 ^ 2 * (n : ℝ) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at this
      exact this
    have hlogb : Real.log ((n : ℝ) + 1) ≤ a / 4 * Real.sqrt ((n : ℝ) + 1) := by
      have h := hlogn
      rw [hrpow] at h
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ (n : ℝ) + 1)),
        abs_of_nonneg (Real.sqrt_nonneg ((n : ℝ) + 1))] at h
      exact h
    have hkey : 2 * Real.log ((n : ℝ) + 1) ≤ a * Real.sqrt (n : ℝ) := by
      have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      nlinarith [hlogb, hsqrt_le, ha, hs]
    have hexp : Real.exp (-(a * Real.sqrt n)) ≤ Real.exp (-(2 * Real.log ((n : ℝ) + 1))) :=
      Real.exp_le_exp.2 (by linarith)
    refine hexp.trans (le_of_eq ?_)
    rw [show -(2 * Real.log ((n : ℝ) + 1)) = Real.log ((((n : ℝ) + 1) ^ 2)⁻¹) by
      rw [Real.log_inv, Real.log_pow]
      push_cast
      ring]
    rw [Real.exp_log (by positivity), one_div]
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
    (fun n => hcomp (n + N) (by omega)) ?_
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)
    have h2 := (summable_nat_add_iff 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    ring
  exact (summable_nat_add_iff N).2 hsum

/-- **The prime-number-theorem weight is summable.**  Cauchy condensation turns
`e^{-c√(log m)}/m` into `e^{-(c√(log 2))√k}`. -/
theorem summable_exp_neg_sqrt_log_div {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℕ => Real.exp (-(c * Real.sqrt (Real.log m))) / m) := by
  set f : ℕ → ℝ := fun m => Real.exp (-(c * Real.sqrt (Real.log m))) / m with hf
  have hnonneg : ∀ m, 0 ≤ f m := by
    intro m
    rw [hf]
    positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hm1 hmn'
    have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by linarith) hmn'
    have hsq : Real.sqrt (Real.log (m : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) :=
      Real.sqrt_le_sqrt hlog
    have hexp : Real.exp (-(c * Real.sqrt (Real.log (n : ℝ))))
        ≤ Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [hsq, hc]
    have hinv : (1 : ℝ) / (n : ℝ) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le (by linarith) hmn'
    rw [hf]
    simp only
    rw [div_eq_mul_one_div (Real.exp (-(c * Real.sqrt (Real.log (n : ℝ))))),
      div_eq_mul_one_div (Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))))]
    exact mul_le_mul hexp hinv (by positivity) (Real.exp_pos _).le
  rw [← summable_condensed_iff_of_nonneg hnonneg hmono]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0 : ℝ) < c * Real.sqrt (Real.log 2) := by positivity
  refine (summable_exp_neg_mul_sqrt ha).congr fun k => ?_
  have h2k : (((2 : ℕ) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  have hlogpow : Real.log (((2 : ℕ) ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [h2k, Real.log_pow]
  have hsqrt : Real.sqrt ((k : ℝ) * Real.log 2)
      = Real.sqrt (k : ℝ) * Real.sqrt (Real.log 2) :=
    Real.sqrt_mul (Nat.cast_nonneg k) _
  rw [hf]
  simp only
  rw [hlogpow, hsqrt, h2k]
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

end

end GaloisForLFunctions.HTGeometry
