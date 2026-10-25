import GaloisForLFunctions.RHTower.WeilMarkovFarOutNonnegativeOddPositivity
import GaloisForLFunctions.RHTower.MontgomeryPrimeSideBounds

/-!
# One global weighted bound for the prime source

Exponential position weight turns translation by `a` into a correlation bound with factor
`exp(-|a|)`. The full prime sum is then controlled by the convergent three-halves von
Mangoldt series, uniformly across compact supports.
-/

noncomputable section
open MeasureTheory Filter RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A positive quadratic source mass defined without an aperture cutoff. -/
def exponentialSourceMass (f : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, (Real.exp |t| * f t) ^ 2

theorem exponentialSourceMass_nonneg (f : ℝ → ℝ) : 0 ≤ exponentialSourceMass f :=
  integral_nonneg fun _ => sq_nonneg _

/-- The weighted source mass controls every autocorrelation with exponential decay in its lag. -/
theorem abs_correlation_le_exp_neg_mul_sourceMass {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (a : ℝ) :
    |∫ t : ℝ, f t * f (t - a)| ≤ Real.exp (-|a|) * exponentialSourceMass f := by
  let g : ℝ → ℝ := fun t => Real.exp |t| * |f t|
  have hgc : Continuous g := (Real.continuous_exp.comp continuous_abs).mul hf.abs
  have hgcs : HasCompactSupport g := by
    have h : HasCompactSupport (fun t : ℝ => Real.exp |t| * ‖f t‖) := hfc.norm.mul_left
    simpa only [g, Real.norm_eq_abs] using h
  have hfi := integrable_mul_comp_sub hf hfc f hf a
  have hgi := integrable_mul_comp_sub hgc hgcs g hgc a
  have hpt (t : ℝ) : Real.exp |a| * |f t * f (t - a)| ≤ g t * g (t - a) := by
    have ha : |a| ≤ |t| + |t - a| := by
      have hh := abs_sub_le t 0 (t - a)
      simpa only [sub_sub_cancel, sub_zero, zero_sub, abs_neg] using hh
    calc
      Real.exp |a| * |f t * f (t - a)| ≤
          Real.exp (|t| + |t - a|) * |f t * f (t - a)| :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (abs_nonneg _)
      _ = g t * g (t - a) := by
        rw [Real.exp_add, abs_mul]
        dsimp only [g]
        ring
  have hmass : (∫ t : ℝ, g t ^ 2) = exponentialSourceMass f := by
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [g, mul_pow, sq_abs]
  have hint : |∫ t : ℝ, f t * f (t - a)| ≤ ∫ t : ℝ, |f t * f (t - a)| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun t : ℝ => f t * f (t - a))
  have hbound : Real.exp |a| * |∫ t : ℝ, f t * f (t - a)| ≤ exponentialSourceMass f := by
    calc
      _ ≤ Real.exp |a| * ∫ t : ℝ, |f t * f (t - a)| :=
        mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
      _ = ∫ t : ℝ, Real.exp |a| * |f t * f (t - a)| := (integral_const_mul _ _).symm
      _ ≤ ∫ t : ℝ, g t * g (t - a) :=
        integral_mono (hfi.norm.const_mul _) hgi hpt
      _ ≤ ∫ t : ℝ, g t ^ 2 := integral_mul_sub_shift_le hgc hgcs a
      _ = exponentialSourceMass f := hmass
  have he : Real.exp (-|a|) * exponentialSourceMass f =
      exponentialSourceMass f / Real.exp |a| := by
    rw [Real.exp_neg, div_eq_mul_inv]
    ring
  rw [he, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hbound

private theorem atom_div_nat_eq_threeHalves (n : ℕ) :
    vonMangoldtAtom n / (n : ℝ) =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  by_cases hn : 2 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hp : Real.sqrt (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        _ = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_one]
        _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hn' _ _).symm
        _ = (n : ℝ) ^ (3 / 2 : ℝ) := by congr 1; ring
    rw [vonMangoldtAtom, if_pos hn, div_div, hp]
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> norm_num [vonMangoldtAtom]

/-- The entire prime source has one aperture-independent exponentially weighted mass bound. -/
theorem primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    primeSum f ≤ 2 * vonMangoldtThreeHalvesMass * exponentialSourceMass f := by
  have hterm (n : ℕ) : vonMangoldtAtom n *
      ((∫ t : ℝ, f t * f (t - Real.log n)) + ∫ t : ℝ, f t * f (t + Real.log n)) ≤
        (2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
          exponentialSourceMass f := by
    rw [← atom_div_nat_eq_threeHalves]
    by_cases hn : 2 ≤ n
    · have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      have he : Real.exp (-|Real.log (n : ℝ)|) = 1 / (n : ℝ) := by
        rw [abs_of_nonneg (Real.log_nonneg hn1), Real.exp_neg, Real.exp_log hn', one_div]
      have hminus := (le_abs_self _).trans (abs_correlation_le_exp_neg_mul_sourceMass hf hfc (Real.log n))
      have hplus := (le_abs_self _).trans (abs_correlation_le_exp_neg_mul_sourceMass hf hfc (-Real.log n))
      rw [he] at hminus
      simp only [sub_neg_eq_add, abs_neg, he] at hplus
      have hh := mul_le_mul_of_nonneg_left (add_le_add hminus hplus)
        (vonMangoldtAtom_nonneg' n)
      calc
        _ ≤ vonMangoldtAtom n *
            ((1 / (n : ℝ)) * exponentialSourceMass f + (1 / (n : ℝ)) * exponentialSourceMass f) := hh
        _ = _ := by ring
    · simp only [vonMangoldtAtom, if_neg hn, zero_mul, zero_div, mul_zero, le_refl]
  have hsum := (summable_primeSum_terms hfc).tsum_le_tsum hterm
    ((summable_vonMangoldt_div_threeHalves.mul_left 2).mul_right (exponentialSourceMass f))
  rw [tsum_mul_right, tsum_mul_left] at hsum
  exact hsum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
