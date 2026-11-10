import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A weighted trace floor controls absolute mass

For a nonnegative weight, `F ≥ −K` gives `|F| ≤ F + 2K`.
For a finite exponential sum the weighted mean is bounded by the sum of
its coefficient norms times the Fourier samples of the weight.
-/

open MeasureTheory Filter
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Finite exponential sum with real frequencies. -/
def finiteExpSum {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ) (t : ℝ) : ℂ :=
  ∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)

/-- Fourier sample with the positive exponential convention. -/
def weightFourier (w : ℝ → ℝ) (γ : ℝ) : ℂ :=
  ∫ t, (w t : ℂ) * Complex.exp (((γ * t : ℝ) : ℂ) * Complex.I)

theorem integrable_weight_character {w : ℝ → ℝ} (hw : Integrable w) (γ : ℝ) :
    Integrable (fun t => (w t : ℂ) * Complex.exp (((γ * t : ℝ) : ℂ) * Complex.I)) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (((γ * t : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  apply hw.ofReal.mul_bdd hc.aestronglyMeasurable (c := 1)
  exact Eventually.of_forall fun t => by simp [Complex.norm_exp]

theorem integrable_weight_finiteExpSum {n : ℕ} {w : ℝ → ℝ} (hw : Integrable w)
    (a : Fin n → ℂ) (γ : Fin n → ℝ) :
    Integrable (fun t => (w t : ℂ) * finiteExpSum a γ t) := by
  have h := integrable_finsetSum Finset.univ
    (fun j _ => (integrable_weight_character hw (γ j)).const_mul (a j))
  have he : (fun t => (w t : ℂ) * finiteExpSum a γ t) =
      fun t => ∑ j, a j * ((w t : ℂ) * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)) := by
    funext t
    simp only [finiteExpSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact h

/-- The weighted mean is the finite coefficient pairing with Fourier samples. -/
theorem integral_weight_finiteExpSum {n : ℕ} {w : ℝ → ℝ} (hw : Integrable w)
    (a : Fin n → ℂ) (γ : Fin n → ℝ) :
    (∫ t, (w t : ℂ) * finiteExpSum a γ t) = ∑ j, a j * weightFourier w (γ j) := by
  have he : (fun t => (w t : ℂ) * finiteExpSum a γ t) =
      fun t => ∑ j, a j * ((w t : ℂ) * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)) := by
    funext t
    simp only [finiteExpSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum Finset.univ
    (fun j _ => (integrable_weight_character hw (γ j)).const_mul (a j))]
  simp only [integral_const_mul, weightFourier]

/-- The exact floor inequality before estimating the signed mean. -/
theorem integral_weight_abs_le_of_floor {w f : ℝ → ℝ} {K : ℝ}
    (hw : Integrable w) (hw0 : ∀ t, 0 ≤ w t) (hwf : Integrable (fun t => w t * f t))
    (hK : 0 ≤ K) (hfloor : ∀ t, -K ≤ f t) :
    (∫ t, w t * |f t|) ≤ (∫ t, w t * f t) + 2 * K * ∫ t, w t := by
  have habs : Integrable (fun t => w t * |f t|) := by
    apply hwf.abs.congr
    exact Eventually.of_forall fun t => by
      change |w t * f t| = w t * |f t|
      rw [abs_mul, abs_of_nonneg (hw0 t)]
  have hpoint (t : ℝ) : |f t| ≤ f t + 2 * K := by
    rcases le_or_gt 0 (f t) with h | h
    · rw [abs_of_nonneg h]
      linarith only [hK]
    · rw [abs_of_neg h]
      linarith only [hfloor t]
  calc
    (∫ t, w t * |f t|) ≤ ∫ t, (w t * f t + (2 * K) * w t) := by
      apply integral_mono habs (hwf.add (hw.const_mul (2 * K)))
      intro t
      change w t * |f t| ≤ w t * f t + 2 * K * w t
      have h := mul_le_mul_of_nonneg_left (hpoint t) (hw0 t)
      nlinarith only [h]
    _ = _ := by rw [integral_add hwf (hw.const_mul (2 * K)), integral_const_mul]

/-- A floor controls weighted absolute trace with coefficient two and a Fourier leakage term. -/
theorem weighted_finiteExpSum_abs_le {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ)
    {w : ℝ → ℝ} (hw : Integrable w) (hw0 : ∀ t, 0 ≤ w t) {K : ℝ} (hK : 0 ≤ K)
    (hfloor : ∀ t, -K ≤ (finiteExpSum a γ t).re) :
    (∫ t, w t * |(finiteExpSum a γ t).re|) ≤
      2 * K * (∫ t, w t) + ∑ j, ‖a j‖ * ‖weightFourier w (γ j)‖ := by
  have hi := integrable_weight_finiteExpSum hw a γ
  have hir : Integrable (fun t => w t * (finiteExpSum a γ t).re) := by
    have hr : Integrable (fun t => ((w t : ℂ) * finiteExpSum a γ t).re) := hi.re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr
  have hre : (∫ t, w t * (finiteExpSum a γ t).re) =
      (∫ t, (w t : ℂ) * finiteExpSum a γ t).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hi]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hmean : (∫ t, w t * (finiteExpSum a γ t).re) ≤
      ∑ j, ‖a j‖ * ‖weightFourier w (γ j)‖ := by
    rw [hre, integral_weight_finiteExpSum hw a γ]
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun j => a j * weightFourier w (γ j))
  have h := integral_weight_abs_le_of_floor hw hw0 hir hK hfloor
  linarith only [h, hmean]

#print axioms weighted_finiteExpSum_abs_le

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
