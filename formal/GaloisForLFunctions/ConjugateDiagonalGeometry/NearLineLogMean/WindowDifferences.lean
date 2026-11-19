import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Binomial differences of finite Dirichlet second moments

Gatea and Huang's signed binomial cancellation (arXiv:2610.34775, §2.4)
applied to the starting height of a window has an exact frequency multiplier.
Every positive-order difference removes the diagonal. Each nearby pair gains
one power of its logarithmic gap per difference, uniformly in the starting
height. Periodic aliases are suppressed to the same order.
-/

open Complex Finset MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

noncomputable section

private def phase (L t : ℝ) := Complex.exp (((L*t : ℝ) : ℂ) * I)

private theorem phase_add (L t h : ℝ) : phase L (t+h) = phase L t * phase L h := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Fourier multiplier of a single forward difference in the window origin. -/
def windowChord (L h : ℝ) : ℂ := phase L h - 1

private theorem expInt_shift (L t h U : ℝ) :
    expInt L (t+h) U = expInt L t U * phase L h := by
  by_cases hL : L = 0
  · subst L
    simp [expInt_zero, phase]
  rw [expInt_eq hL, expInt_eq hL]
  change (phase L (t+h+U) - phase L (t+h)) / _ = (phase L (t+U) - phase L t) / _ * _
  rw [show t+h+U = (t+U)+h by ring, phase_add L (t+U), phase_add L t]
  ring

/-- Exact action on each Fourier window, including zero gap and zero step. -/
theorem expInt_window_difference (r : ℕ) (L h U t : ℝ) :
    (fwdDiff h)^[r] (fun v => expInt L v U) t = expInt L t U * windowChord L h ^ r := by
  induction r generalizing t with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff h)^[r] _ (t+h) - (fwdDiff h)^[r] _ t = _
    rw [ih, ih, expInt_shift, windowChord, pow_succ]
    ring

/-- The gain is controlled by the distance to *any* multiple of a full turn. -/
theorem windowChord_le_alias (L h : ℝ) (m : ℤ) :
    ‖windowChord L h‖ ≤ |L*h - 2*Real.pi*m| := by
  simpa [windowChord, phase] using norm_expI_sub_expI_le (L*h) 0 m

/-- Positive-order binomial differences pay the diagonal exactly. -/
theorem expInt_diagonal_difference (r : ℕ) (h U t : ℝ) :
    (fwdDiff h)^[r+1] (fun v => expInt 0 v U) t = 0 := by
  simp [expInt_window_difference, windowChord, phase]

private theorem norm_expInt_le_abs_length (L t U : ℝ) : ‖expInt L t U‖ ≤ |U| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+U) (C := (1 : ℝ))
    (f := fun x : ℝ => phase L x) (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa [expInt, phase] using h

/-- Uniform suppression of near-diagonal and aliased frequencies on windows of any orientation. -/
theorem norm_window_difference_le_alias (r : ℕ) (L h U t : ℝ) (m : ℤ) :
    ‖(fwdDiff h)^[r] (fun v => expInt L v U) t‖ ≤ |U| * |L*h - 2*Real.pi*m|^r := by
  rw [expInt_window_difference, norm_mul, norm_pow]
  exact mul_le_mul (norm_expInt_le_abs_length _ _ _) (pow_le_pow_left₀ (norm_nonneg _)
    (windowChord_le_alias _ _ _) _) (by positivity) (abs_nonneg _)

/-- After one extra difference the inverse gap from integration cancels.
The estimate is independent of both the starting height and the length. -/
theorem norm_window_difference_le_gap (r : ℕ) (L h U t : ℝ) :
    ‖(fwdDiff h)^[r+1] (fun v => expInt L v U) t‖ ≤ 2 * |h|^(r+1) * |L|^r := by
  by_cases hL : L = 0
  · subst L
    rw [expInt_diagonal_difference, norm_zero]
    positivity
  have hc : ‖windowChord L h‖ ≤ |L|*|h| := by
    simpa [abs_mul] using windowChord_le_alias L h 0
  rw [expInt_window_difference, norm_mul, norm_pow]
  calc
    _ ≤ (2 / |L|) * (|L|*|h|)^(r+1) := mul_le_mul (norm_expInt_le hL _ _)
      (pow_le_pow_left₀ (norm_nonneg _) hc _) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, pow_succ |L|]; field_simp [abs_ne_zero.mpr hL]

/-- Windowed twisted second moment for arbitrary arithmetic coefficients. -/
def twistedWindow (a b : ℕ → ℂ) (S : Finset ℕ) (σ ω U t : ℝ) : ℂ :=
  ∫ v in t..(t+U), cdpoly a S σ v * (starRingEnd ℂ) (cdpoly b S σ v) *
    Complex.exp ((((ω*v : ℝ)) : ℂ) * I)

/-- Pair coefficient, retaining signs and phases of both arithmetic rows. -/
def windowPairWeight (a b : ℕ → ℂ) (σ : ℝ) (m n : ℕ) : ℂ :=
  (a m * (starRingEnd ℂ) (b n)) * (((m : ℝ)^(-σ) * (n : ℝ)^(-σ) : ℝ) : ℂ)

/-- Signed binomial differences of the whole moment keep the original pair weights.
Only the multiplier depends on the order of cancellation. -/
theorem twistedWindow_difference (a b : ℕ → ℂ) (S : Finset ℕ) (r : ℕ) (σ ω h U t : ℝ) :
    (fwdDiff h)^[r] (twistedWindow a b S σ ω U) t =
      ∑ m ∈ S, ∑ n ∈ S, windowPairWeight a b σ m n *
        (expInt (Real.log n - Real.log m + ω) t U * windowChord (Real.log n - Real.log m + ω) h ^ r) := by
  have hf : twistedWindow a b S σ ω U = ∑ m ∈ S, ∑ n ∈ S,
      windowPairWeight a b σ m n • (fun v => expInt (Real.log n - Real.log m + ω) v U) := by
    funext v
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, windowPairWeight, twistedWindow]
      using twisted_meanValue a b S σ ω v U
  rw [hf, fwdDiff_iter_finsetSum]
  simp only [fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, expInt_window_difference]

/-- The actual cost of any binomially differenced moment is bounded by an absolute
weighted moment of its logarithmic gaps, without dependence on the length or height. -/
theorem norm_twistedWindow_difference_le (a b : ℕ → ℂ) (S : Finset ℕ) (r : ℕ) (σ ω h U t : ℝ) :
    ‖(fwdDiff h)^[r+1] (twistedWindow a b S σ ω U) t‖ ≤
      ∑ m ∈ S, ∑ n ∈ S, ‖windowPairWeight a b σ m n‖ *
        (2 * |h|^(r+1) * |Real.log n - Real.log m + ω|^r) := by
  rw [twistedWindow_difference]
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun m _ => (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [norm_mul, ← expInt_window_difference]
  exact mul_le_mul_of_nonneg_left (norm_window_difference_le_gap _ _ _ _ _) (norm_nonneg _)

#print axioms expInt_window_difference
#print axioms norm_window_difference_le_alias
#print axioms norm_twistedWindow_difference_le

end

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
