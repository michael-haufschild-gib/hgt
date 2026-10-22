import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileOddWindowQuantitativeMismatch
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileOddWindowCofinalCount

/-!
# Cofinal quantitative mismatch count on literal odd-log heads

The canonical windows eventually satisfy the finite prime-count inequality
for actual active vertices whose base displacement is at least the explicit
inverse-square-root threshold. The proof uses the same source and same
window as the qualitative PNT mismatch theorem, but asserts no signed bound.
-/

namespace RHTower

/-- On the canonical cofinal odd-log windows, prime supply is charged to
actual active vertices whose displacement from the base prime is at least
the explicit inverse-square-root threshold. -/
theorem eventually_ccmOddLogWindow_primeCount_le_twice_quantitativeMismatch_add_properPower :
    ∀ᶠ t : ℕ in Filter.atTop,
      ((Finset.Icc (ccmOddLogWindowLower t)
        (ccmOddLogWindowUpper t)).filter Nat.Prime).card ≤
        2 * (ccmOddLogWindowQuantitativeMismatchSet
          (ccmOddLogWindowLower t) (ccmOddLogWindowUpper t)).card +
        (((Finset.Icc (ccmOddLogWindowLower t)
          (ccmOddLogWindowUpper t)).filter IsPrimePow).filter
            (fun n => ¬ n.Prime)).card + 1 := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    eventually_ccmActualHead_prime_gap_resonance_error_lt_quarter
  let T : ℕ := ⌈max X (Real.exp 2)⌉₊ + 3
  filter_upwards [Filter.eventually_ge_atTop T] with t ht
  let x : ℝ := Real.exp ((2 * t + 1 : ℕ) : ℝ)
  let A : ℕ := ccmOddLogWindowLower t
  let B : ℕ := ccmOddLogWindowUpper t
  have hx0 : 0 < x := Real.exp_pos _
  have hxt : (t : ℝ) ≤ x := by
    have hexp := Real.add_one_le_exp ((2 * t + 1 : ℕ) : ℝ)
    have hlin : (t : ℝ) ≤ 1 + ((2 * t + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show t ≤ 1 + (2 * t + 1) by omega)
    dsimp only [x]
    linarith
  have hT : max X (Real.exp 2) ≤ (t : ℝ) := by
    have htR : (T : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    have hceil : max X (Real.exp 2) ≤
        (⌈max X (Real.exp 2)⌉₊ : ℝ) := Nat.le_ceil _
    dsimp only [T] at htR
    push_cast at htR
    linarith
  have hXx : X ≤ x := (le_max_left _ _).trans (hT.trans hxt)
  have hexp2x : Real.exp 2 ≤ x := (le_max_right _ _).trans (hT.trans hxt)
  have hAlo : x < (A : ℝ) := by
    dsimp only [A, ccmOddLogWindowLower, x]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.exp ((2 * t + 1 : ℕ) : ℝ))
  have hA3 : 3 ≤ A := by
    have hexp2three : (3 : ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp (2 : ℝ)
      linarith
    have hA3R : (3 : ℝ) ≤ (A : ℝ) :=
      (hexp2three.trans hexp2x).trans hAlo.le
    exact_mod_cast hA3R
  have hAexp : Real.exp 2 ≤ (A : ℝ) := hexp2x.trans hAlo.le
  have hBhi : (B : ℝ) ≤
      Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4) := by
    dsimp only [B, ccmOddLogWindowUpper]
    exact Nat.floor_le (Real.exp_pos _).le
  have herr : ∀ p : ℕ, A ≤ p → p ≤ B →
      Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4 := by
    intro p hpA _
    have hpR : (A : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpA
    exact hX _ (hXx.trans (hAlo.le.trans hpR))
  exact ccmOddLogWindow_primeCount_le_twice_quantitativeMismatch_add_properPower
    A B t hA3 hAexp hAlo.le hBhi herr

end RHTower
