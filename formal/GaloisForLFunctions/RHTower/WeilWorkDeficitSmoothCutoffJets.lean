import GaloisForLFunctions.RHTower.SmoothAFECutoffGaussianTail

/-!
# Uniform height derivatives of the actual Gaussian Mellin cutoff

The zeroth, first, and second height derivatives of `smoothAFECutoff (P/t)`
share one bound `C / t^j * min 1 ((t/P)^2)`, for every positive product P
and height t. The explicit derivatives are proved from the actual cutoff;
no asymptotic cutoff model or unproved derivative estimate is used.

This supplies the moving-amplitude input for twice integrating by parts
in the square-root-window twisted moment. The moment and spectral-deficit
conclusions are not asserted by this module.
-/

noncomputable section
open Real
namespace RHTower.WeilWorkDeficitCutoff

private theorem gaussian_weight (y : ℝ) :
    (1 + |y|) * exp (-y^2/4) ≤ exp 9 * min 1 (exp (-2*y)) := by
  have hbase : (1 + |y|) * exp (-y^2/4) ≤ exp (|y| - y^2/4) := by
    rw [show |y| - y^2/4 = |y| + (-y^2/4) by ring, exp_add]
    exact mul_le_mul_of_nonneg_right (by simpa [add_comm] using add_one_le_exp |y|)
      (exp_pos _).le
  have habs : |y|^2 = y^2 := sq_abs y
  have h1 : |y| - y^2/4 ≤ 9 := by nlinarith [sq_nonneg (|y|-2)]
  have h2 : |y| - y^2/4 ≤ 9 + (-2*y) := by
    nlinarith [sq_nonneg (|y|-6), le_abs_self y]
  rw [mul_min_of_nonneg _ _ (exp_pos 9).le, mul_one]
  exact le_min (hbase.trans (exp_le_exp.mpr h1))
    (hbase.trans (by rw [← exp_add]; exact exp_le_exp.mpr h2))

/-- First height derivative of the actual inverse-Mellin cutoff. -/
def cutoffFirst (P t : ℝ) : ℝ :=
  exp (-(log (P/t))^2/4) / (2 * sqrt π * t)

/-- Second height derivative of the actual inverse-Mellin cutoff. -/
def cutoffSecond (P t : ℝ) : ℝ :=
  exp (-(log (P/t))^2/4) * (log (P/t)/2-1) / (2 * sqrt π * t^2)

/-- The explicit first derivative is the derivative of the literal cutoff. -/
theorem hasDerivAt_cutoff {P t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (smoothAFECutoff (P/u)).re) (cutoffFirst P t) t := by
  have h := (hasDerivAt_smoothAFECutoff_re (div_pos hP ht)).comp t
    ((hasDerivAt_const t P).div (hasDerivAt_id t) ht.ne')
  change HasDerivAt (fun u : ℝ => (smoothAFECutoff (P/u)).re) _ t at h
  apply h.congr_deriv
  unfold cutoffFirst smoothAFECutoffDeriv
  field_simp [hP.ne', ht.ne']
  ring

/-- The explicit second derivative is the derivative of the first. -/
theorem hasDerivAt_cutoffFirst {P t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    HasDerivAt (cutoffFirst P) (cutoffSecond P t) t := by
  have hd := (hasDerivAt_const t P).div (hasDerivAt_id t) ht.ne'
  have hl := hd.log (ne_of_gt (div_pos hP ht))
  have hg := ((hl.pow 2).neg.div_const 4).exp
  have he := hg.div ((hasDerivAt_id t).const_mul (2*sqrt π))
    (mul_ne_zero (mul_ne_zero (by norm_num) (sqrt_pos.mpr pi_pos).ne') ht.ne')
  change HasDerivAt (cutoffFirst P) _ t at he
  apply he.congr_deriv
  unfold cutoffSecond
  dsimp
  field_simp [hP.ne', ht.ne']
  ring

private theorem cutoff_gaussian_bound {P t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    (1 + |log (P/t)|) * exp (-(log (P/t))^2/4) ≤
      exp 9 * min 1 ((t/P)^2) := by
  have he : exp (-2*log (P/t)) = (t/P)^2 := by
    rw [show -2*log (P/t) = -(log (P/t)+log (P/t)) by ring,
      exp_neg, exp_add, exp_log (div_pos hP ht)]
    field_simp
  simpa only [he] using gaussian_weight (log (P/t))

private theorem first_bound {P t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    |cutoffFirst P t| ≤ (exp 9 / (2*sqrt π)) / t * min 1 ((t/P)^2) := by
  have h := cutoff_gaussian_bound hP ht
  have hh : exp (-(log (P/t))^2/4) ≤ exp 9 * min 1 ((t/P)^2) := by
    calc _ ≤ (1 + |log (P/t)|) * exp (-(log (P/t))^2/4) := by
           nlinarith [exp_pos (-(log (P/t))^2/4), abs_nonneg (log (P/t))]
         _ ≤ _ := h
  unfold cutoffFirst
  rw [abs_of_pos (by positivity)]
  calc _ ≤ (exp 9 * min 1 ((t/P)^2)) / (2 * sqrt π * t) :=
      div_le_div_of_nonneg_right hh (by positivity)
       _ = _ := by ring

private theorem second_bound {P t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    |cutoffSecond P t| ≤ (exp 9 / (2*sqrt π)) / t^2 * min 1 ((t/P)^2) := by
  have h := cutoff_gaussian_bound hP ht
  have hb : |log (P/t)/2-1| ≤ 1+|log (P/t)| := by
    have ha := abs_sub (log (P/t)/2) 1
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), abs_one] at ha
    linarith [abs_nonneg (log (P/t))]
  unfold cutoffSecond
  rw [abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (show (0:ℝ)<2*sqrt π*t^2 by positivity)]
  calc _ ≤ (exp (-(log (P/t))^2/4) * (1+|log (P/t)|)) / (2*sqrt π*t^2) := by
          gcongr
       _ ≤ (exp 9 * min 1 ((t/P)^2)) / (2*sqrt π*t^2) :=
          div_le_div_of_nonneg_right (by simpa only [mul_comm] using h) (by positivity)
       _ = _ := by ring

/-- One constant bounds the actual moving cutoff and both height derivatives,
uniformly in every positive product and height. -/
theorem exists_uniform_cutoff_two_jet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ P t : ℝ, 0 < P → 0 < t →
      |(smoothAFECutoff (P/t)).re| ≤ C * min 1 ((t/P)^2) ∧
      |cutoffFirst P t| ≤ C/t * min 1 ((t/P)^2) ∧
      |cutoffSecond P t| ≤ C/t^2 * min 1 ((t/P)^2) := by
  obtain ⟨K,hK,hfar⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (by norm_num : (0:ℝ)<2)
  let C := 1 + K + exp 9 / (2*sqrt π)
  have hc : 0 < C := by dsimp [C]; positivity
  have hexp : 0 ≤ exp 9 / (2*sqrt π) := by positivity
  have h1 : 1 ≤ C := by dsimp [C]; linarith
  have hkc : K ≤ C := by dsimp [C]; linarith
  have hec : exp 9 / (2*sqrt π) ≤ C := by dsimp [C]; linarith
  refine ⟨C,hc,fun P t hP ht => ⟨?_,?_,?_⟩⟩
  · rw [mul_min_of_nonneg _ _ hc.le, mul_one]
    refine le_min ?_ ?_
    · rw [abs_of_nonneg (smoothAFECutoff_re_nonneg (div_pos hP ht))]
      exact (smoothAFECutoff_re_le_one (div_pos hP ht)).trans h1
    · have hf := hfar (div_pos hP ht)
      have hp : (P/t)^(-(2:ℝ)) = (t/P)^2 := by
        rw [rpow_neg (le_of_lt (div_pos hP ht)), rpow_two]
        field_simp
      rw [hp] at hf
      exact (Complex.abs_re_le_norm _).trans (hf.trans (by gcongr))
  · exact (first_bound hP ht).trans (by gcongr)
  · exact (second_bound hP ht).trans (by gcongr)

end RHTower.WeilWorkDeficitCutoff
