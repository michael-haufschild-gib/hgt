import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseError

/-!
# The mean square of a Dirichlet polynomial supported on a sparse set

The mean value theorem, stated by the *size of the support* rather than by the length of the
polynomial: for coefficients bounded by `1` supported on `s ⊆ [1, M]`,

```text
∫_{|w| ≤ W} ‖ ∑_{n ∈ s} a(n) n^{2πiw} ‖² dw  ≤  ( (5π/2)·W + (5e/2)·M )·#s .
```

Both terms are proportional to `#s`, so a support of density `η` inside `[1, M]` contributes
`η·M²` to the height-free part.  That is the form in which the error terms of a factorisation are
paid: a sparse error is cheap in mean square even though its *pointwise* size is its cardinality,
and it is this distinction that decides whether a factorisation of the Möbius polynomial can be
afforded — the crude pointwise bound charges `#s²`, the mean square only `M·#s`.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

/-- **The mean value theorem by coefficient energy.** -/
theorem integral_Icc_normSq_logPoly_le_energy (a : ℕ → ℂ) {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s)
    {M : ℕ} (hsM : ∀ n ∈ s, n ≤ M) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  set δ : ℝ := 1 / (2 * Real.pi * W) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three, hW]
  have hWδ : 2 * Real.pi * δ * W ≤ 1 := by
    rw [hδdef]
    have hne : (2 : ℝ) * Real.pi * W ≠ 0 := by positivity
    rw [show 2 * Real.pi * (1 / (2 * Real.pi * W)) * W = (2 * Real.pi * W) / (2 * Real.pi * W) by
      ring, div_self hne]
  have hbase := integral_Icc_normSq_logPoly_le_general a s hs0 hδ0 hWδ
  have hexp : Real.exp δ - Real.exp (-δ) ≤ 2 * δ * Real.exp 1 := by
    have h1 : (1 : ℝ) - Real.exp (-(2 * δ)) ≤ 2 * δ := by
      have := Real.add_one_le_exp (-(2 * δ))
      linarith
    have hfac : Real.exp δ - Real.exp (-δ) = Real.exp δ * (1 - Real.exp (-(2 * δ))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring
    have hδe : Real.exp δ ≤ Real.exp 1 := Real.exp_le_exp.2 hδ1
    have hnn : (0 : ℝ) ≤ 1 - Real.exp (-(2 * δ)) := by
      have : Real.exp (-(2 * δ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      linarith
    rw [hfac]
    calc Real.exp δ * (1 - Real.exp (-(2 * δ))) ≤ Real.exp 1 * (1 - Real.exp (-(2 * δ))) :=
          mul_le_mul_of_nonneg_right hδe hnn
      _ ≤ Real.exp 1 * (2 * δ) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos 1).le
      _ = 2 * δ * Real.exp 1 := by ring
  have hterm : ∀ n ∈ s, ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) * ‖a n‖ ^ 2
      ≤ ((M : ℝ) * (2 * δ * Real.exp 1) + 1) * ‖a n‖ ^ 2 := by
    intro n hn
    have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hsM n hn
    have hinc : (0 : ℝ) ≤ Real.exp δ - Real.exp (-δ) := by
      have : Real.exp (-δ) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
      linarith
    have hfirst : (n : ℝ) * (Real.exp δ - Real.exp (-δ)) ≤ (M : ℝ) * (2 * δ * Real.exp 1) := by
      calc (n : ℝ) * (Real.exp δ - Real.exp (-δ)) ≤ (M : ℝ) * (Real.exp δ - Real.exp (-δ)) :=
            mul_le_mul_of_nonneg_right hnM hinc
        _ ≤ (M : ℝ) * (2 * δ * Real.exp 1) :=
            mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg M)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hsum : ∑ n ∈ s, ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) * ‖a n‖ ^ 2
      ≤ ((M : ℝ) * (2 * δ * Real.exp 1) + 1) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  refine le_trans hbase ?_
  have hcoef : (0 : ℝ) ≤ 5 / (4 * δ) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hcoef) (le_of_eq ?_)
  have hval : (5 : ℝ) / (4 * δ) = 5 * Real.pi / 2 * W := by
    rw [hδdef]
    field_simp
    ring
  rw [← mul_assoc, hval]
  congr 1
  rw [hδdef]
  field_simp
  ring

/-- **The mean value theorem by support size.** -/
theorem integral_Icc_normSq_logPoly_le_support (a : ℕ → ℂ) {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s)
    {M : ℕ} (hsM : ∀ n ∈ s, n ≤ M) (ha : ∀ n, ‖a n‖ ≤ 1) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * (s.card : ℝ) := by
  classical
  refine le_trans (integral_Icc_normSq_logPoly_le_energy a hs0 hsM hW) ?_
  have hcoef0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have := Real.pi_pos
    have := (Real.exp_pos 1).le
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef0
  have hbound : ∑ n ∈ s, ‖a n‖ ^ 2 ≤ ∑ _n ∈ s, (1 : ℝ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have := ha n
    nlinarith [norm_nonneg (a n)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hbound
  exact hbound

/-- The integers of `[1, M]` carrying no designated prime factor. -/
def supportMeanSquareRoughSet (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  {n ∈ Finset.Icc 1 M | primeFactorsIn P n = ∅}

/-- **The mean square of the rough Möbius polynomial.**  Only the rough *count* enters, so the
height-free part is `(5e/2)·M·#rough`: the factorisation can be afforded exactly when the rough
integers have density `o(1)`. -/
theorem integral_Icc_normSq_roughPoly_le (P : Finset ℕ) (M : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * ((supportMeanSquareRoughSet P M).card : ℝ) := by
  classical
  refine integral_Icc_normSq_logPoly_le_support _ ?_ ?_ ?_ hW
  · rw [supportMeanSquareRoughSet]
    intro hcon
    have := (Finset.mem_filter.1 hcon).1
    rw [Finset.mem_Icc] at this
    omega
  · intro n hn
    rw [supportMeanSquareRoughSet, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.2
  · intro n
    have hnorm : ‖((μ n : ℤ) : ℂ)‖ = |((μ n : ℤ) : ℝ)| := by
      rw [show (((μ n : ℤ)) : ℂ) = ((((μ n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact abs_moebius_real_le_one n

end RHTower.Sieve

end
