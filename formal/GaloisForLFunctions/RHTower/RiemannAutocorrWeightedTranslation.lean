import GaloisForLFunctions.RHTower.WeilWorkExposingRayDifferentialParity
import GaloisForLFunctions.RHTower.WeilFullConeConvolutionPositivity

/-!
# Exponentially weighted translation bounds for the Riemann autocorrelation

The actual cusp-series derivative bounds imply a local Lipschitz estimate whose
constant decays exponentially with the translation center. No regularity or
decay hypothesis is added to the Riemann kernel.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- Every fixed actual Riemann derivative has a cubic exponential envelope. -/
theorem exists_riemannKernelDeriv_cubic_exp_envelope (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖riemannKernelDeriv k x‖ ≤ C * Real.exp (-(3 * |x|)) := by
  obtain ⟨C, hC, h⟩ := ExposingRayDifferential.kernel_derivative_upper_subcritical
    k (a := 1) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨C, hC, fun x => (h x).trans ?_⟩
  simp only [one_mul]
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp (2 * |x|)]

/-- Short translations of the real Riemann kernel retain exponential decay. -/
theorem exists_riemannKernelReal_translation_envelope :
    ∃ D : ℝ, 0 < D ∧ ∀ x h : ℝ, |h| ≤ 1 →
      |riemannKernelReal (x + h) - riemannKernelReal x| ≤
        D * Real.exp (-(3 * |x|)) * |h| := by
  obtain ⟨C, hC, hbound⟩ := exists_riemannKernelDeriv_cubic_exp_envelope 1
  refine ⟨C * Real.exp 3, by positivity, ?_⟩
  intro x h hh
  have hderiv (z : ℝ) (hz : z ∈ Icc (x - 1) (x + 1)) :
      ‖riemannKernelDeriv 1 z‖ ≤ (C * Real.exp 3) * Real.exp (-(3 * |x|)) := by
    have hzx : |z - x| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hdist := abs_sub_abs_le_abs_sub x z
    rw [abs_sub_comm x z] at hdist
    calc
      _ ≤ C * Real.exp (-(3 * |z|)) := hbound z
      _ ≤ C * Real.exp (3 - 3 * |x|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  have hx : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hxh : x + h ∈ Icc (x - 1) (x + 1) := by
    have := abs_le.mp hh
    constructor <;> linarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc (x - 1) (x + 1)) =>
      (hasDerivAt_riemannKernelDeriv 0 z).hasDerivWithinAt)
    hderiv (convex_Icc (x - 1) (x + 1)) hx hxh
  simpa only [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, add_sub_cancel_left] using hm

/-- The actual autocorrelation has a local translation modulus with a decaying
center weight. This is stronger than an unweighted global Lipschitz bound. -/
theorem exists_riemannAutocorr_translation_envelope :
    ∃ E : ℝ, 0 < E ∧ ∀ y h : ℝ, |h| ≤ 1 →
      |riemannAutocorr (y + h) - riemannAutocorr y| ≤
        E * |h| * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC, hzero⟩ := exists_riemannKernelDeriv_cubic_exp_envelope 0
  obtain ⟨D, hD, hshift⟩ := exists_riemannKernelReal_translation_envelope
  have hphi (t : ℝ) : |riemannKernelReal t| ≤ C * Real.exp (-(3 * |t|)) := by
    simpa only [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal,
      Complex.norm_real, Real.norm_eq_abs] using hzero t
  let I : ℝ := ∫ t : ℝ, Real.exp (-|t|)
  have hI : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C * D * (I + 1), by positivity, ?_⟩
  intro y h hh
  have heq : riemannAutocorr (y + h) - riemannAutocorr y =
      ∫ t : ℝ, riemannKernelReal t *
        (riemannKernelReal (t - (y + h)) - riemannKernelReal (t - y)) := by
    rw [riemannAutocorr, riemannAutocorr,
      ← integral_sub (integrable_riemannKernelReal_mul (y + h))
        (integrable_riemannKernelReal_mul y)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by ring
  have hb (t : ℝ) :
      |riemannKernelReal t *
        (riemannKernelReal (t - (y + h)) - riemannKernelReal (t - y))| ≤
      (C * D * |h| * Real.exp (-(2 * |y|))) * Real.exp (-|t|) := by
    have hs := hshift (t - y) (-h) (by simpa only [abs_neg] using hh)
    rw [show t - y + -h = t - (y + h) by ring, abs_neg] at hs
    have htriangle : |y| ≤ |t| + |t - y| := by
      have := abs_sub t (t - y)
      simpa only [sub_sub_cancel] using this
    rw [abs_mul]
    calc
      _ ≤ (C * Real.exp (-(3 * |t|))) *
          (D * Real.exp (-(3 * |t - y|)) * |h|) :=
        mul_le_mul (hphi t) hs (abs_nonneg _) (by positivity)
      _ = (C * D * |h|) * Real.exp (-(3 * |t|) - 3 * |t - y|) := by
        simp only [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ (C * D * |h|) * Real.exp (-(2 * |y|) - |t|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg (t - y)])) (by positivity)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  calc
    _ ≤ ∫ t : ℝ, |riemannKernelReal t *
        (riemannKernelReal (t - (y + h)) - riemannKernelReal (t - y))| := by
      rw [heq, ← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C * D * |h| * Real.exp (-(2 * |y|))) * Real.exp (-|t|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_exp_neg_abs.const_mul _) (Filter.Eventually.of_forall hb)
    _ = (C * D * |h| * Real.exp (-(2 * |y|))) * I := by
      rw [integral_const_mul]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (show I ≤ I + 1 by linarith)
        (show 0 ≤ C * D * |h| * Real.exp (-(2 * |y|)) by positivity)
      nlinarith

end RHTower
