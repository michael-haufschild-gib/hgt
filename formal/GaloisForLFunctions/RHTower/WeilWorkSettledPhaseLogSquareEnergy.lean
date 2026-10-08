import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare
import GaloisForLFunctions.RHTower.WeilIntegerMassAtomicRigidity

/-!
# Square summability of the actual source logarithm

The paid dyadic mean-square law for the original Weil coefficients gives
square summability on every real line to the right of one. This pays the
absolute convergence of the logarithmic valuation twists.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic
open IntegerMassRigidity

theorem summable_lam_sq_div_rpow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => lam n ^ 2 / (n : ℝ) ^ σ) := by
  obtain ⟨C₀, hC⟩ := WeilMeanSquare.exists_sum_sq_Ioc_le_of_weilPositiveFull hW
  let r : ℝ := (2 : ℝ) ^ (1 - σ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let b : ℕ → ℝ := fun j => 2 * r ^ j * ((j + 1) * Real.log 2 + C₀) ^ 2
  have hbs : Summable b := by
    have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hrn).mul_left
      (2 * Real.log 2 ^ 2)
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hrn).mul_left
      (4 * Real.log 2 * (Real.log 2 + C₀))
    have h0 := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (2 * (Real.log 2 + C₀) ^ 2)
    refine ((h2.add h1).add h0).congr fun j => ?_
    simp only [b, pow_one]
    ring
  have hb0 (j : ℕ) : 0 ≤ b j := by dsimp [b]; positivity
  let f : ℕ → ℝ := fun n => lam n ^ 2 / (n : ℝ) ^ σ
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hblock (j : ℕ) :
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ b j := by
    let N : ℕ := 2 ^ j
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2N : 2 ^ (j + 1) = 2 * N := by rw [pow_succ, mul_comm]
    have hNr : (N : ℝ) / (N : ℝ) ^ σ = r ^ j := by
      have e1 : (N : ℝ) = (2 : ℝ) ^ (j : ℝ) := by
        dsimp only [N]
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      have e2 : (N : ℝ) ^ σ = (2 : ℝ) ^ ((j : ℝ) * σ) := by
        rw [e1, ← Real.rpow_mul (by norm_num)]
      have e3 : r ^ j = (2 : ℝ) ^ ((1 - σ) * (j : ℝ)) := by
        dsimp only [r]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [e2, e3, e1, ← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    have hlog : Real.log (2 * N : ℕ) = (j + 1) * Real.log 2 := by
      rw [← h2N, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      ring
    rw [h2N]
    calc
      _ ≤ ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / (N : ℝ) ^ σ := by
        apply Finset.sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hN0 _)
        exact Real.rpow_le_rpow hN0.le
          (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le) (by linarith)
      _ = (∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2) / (N : ℝ) ^ σ := by
        rw [Finset.sum_div]
      _ ≤ (2 * N : ℕ) * (Real.log (2 * N : ℕ) + C₀) ^ 2 / (N : ℝ) ^ σ :=
        div_le_div_of_nonneg_right (hC N hN1) (Real.rpow_nonneg hN0.le _)
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ σ) * ((j + 1) * Real.log 2 + C₀) ^ 2 := by
        rw [hlog]
        push_cast
        ring
      _ = b j := by rw [hNr]
  have hdyad (J : ℕ) :
      ∑ n ∈ Finset.Ioc 1 (2 ^ J), f n ≤ ∑ j ∈ Finset.range J, b j := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive f Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), Finset.sum_range_succ]
      exact add_le_add ih (hblock J)
  refine summable_of_sum_range_le (c := f 0 + f 1 + ∑' j, b j) hf0 fun T => ?_
  have hT : T ≤ 2 ^ T := Nat.lt_two_pow_self.le
  calc
    ∑ n ∈ Finset.range T, f n ≤ ∑ n ∈ Finset.range (2 ^ T + 1), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun n _ _ => hf0 n)
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc 1 (2 ^ T), f n :=
      WeilMeanSquare.sum_range_succ_eq_Ioc f (2 ^ T) Nat.one_le_two_pow
    _ ≤ f 0 + f 1 + ∑' j, b j := by
      have hh := (hdyad T).trans (hbs.sum_le_tsum _ fun j _ => hb0 j)
      linarith

/-- Original positivity pays the logarithmic square energy needed for every
fixed valuation twist in the square-root disk. -/
theorem summable_lamLog_sq_div_rpow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖lamLog lam n‖ ^ 2 / (n : ℝ) ^ σ) := by
  apply ((summable_lam_sq_div_rpow hW hσ).mul_left 4).of_nonneg_of_le
    (fun n => by positivity)
  intro n
  have hh : ‖lamLog lam n‖ ^ 2 ≤ 4 * lam n ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_lamLog_le lam n) 2
    simpa only [mul_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right hh (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

end RHTower.WeilSingularArithmetic
