import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquarePoleDecomposition
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightDerivativeBound

/-!
# Vertical integrability for the Gaussian zeta-square contour

Pure Gaussian control on the right line and quartic-Gaussian control on the reflected left line.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower.Sieve

theorem exists_norm_smoothAFEZetaSquareMellinIntegrand_right_one_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((1 : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-(v ^ 2)) := by
  let M : ℝ := smoothAFEZetaMajorant (3 / 2)
  let C : ℝ := (M * x * Real.exp 1) * M
  have hM : 0 ≤ M := by
    dsimp only [M, smoothAFEZetaMajorant]
    positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro v
  have hsingle := norm_smoothAFEZetaMellinIntegrand_vertical_le
    (s := linePt tau) (c := 1) hx (by norm_num)
    (by rw [linePt_re]; norm_num) v
  have hzeta := norm_riemannZeta_vertical_le_smoothAFEZetaMajorant
    (s := linePt tau) (c := 1)
    (by rw [linePt_re]; norm_num) v
  have hthree : (linePt tau).re + 1 = (3 / 2 : ℝ) := by
    rw [linePt_re]
    norm_num
  rw [hthree] at hsingle hzeta
  have hsingle' :
      ‖smoothAFEZetaMellinIntegrand (linePt tau) x
          ((1 : ℂ) + (v : ℂ) * I)‖ ≤
        (M * x * Real.exp 1) * Real.exp (-(v ^ 2)) := by
    simpa [M] using hsingle
  have hzeta' :
      ‖riemannZeta (linePt tau + ((1 : ℂ) + (v : ℂ) * I))‖ ≤ M := by
    simpa [M] using hzeta
  rw [smoothAFEZetaSquareMellinIntegrand_eq_single_mul_zeta, norm_mul]
  calc
    ‖smoothAFEZetaMellinIntegrand (linePt tau) x
          (1 + ↑v * I)‖ *
        ‖riemannZeta (linePt tau + (1 + ↑v * I))‖
      ≤ ((M * x * Real.exp 1) * Real.exp (-(v ^ 2))) * M := by gcongr
    _ = C * Real.exp (-(v ^ 2)) := by dsimp only [C]; ring

theorem smoothAFEZetaSquareMellinIntegrand_right_one_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Complex.VerticalIntegrable
      (smoothAFEZetaSquareMellinIntegrand (linePt tau) x) 1 := by
  rw [Complex.VerticalIntegrable]
  change Integrable (fun v : ℝ =>
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((1 : ℂ) + (v : ℂ) * I))
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_smoothAFEZetaSquareMellinIntegrand_right_one_le hx tau
  have hmajor : Integrable (fun v : ℝ => C * Real.exp (-(v ^ 2))) := by
    simpa only [neg_one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul C
  apply Integrable.mono' hmajor
  · have hsingleRaw :=
      smoothAFEZetaMellinIntegrand_right_one_verticalIntegrable hx tau
    rw [Complex.VerticalIntegrable] at hsingleRaw
    have hsingle : Integrable (fun v : ℝ =>
        smoothAFEZetaMellinIntegrand (linePt tau) x
          ((1 : ℂ) + (v : ℂ) * I)) := by
      simpa using hsingleRaw
    have hzeta : Continuous (fun v : ℝ =>
        riemannZeta (linePt tau + ((1 : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      · fun_prop
      · intro hpole
        have hre := congrArg Complex.re hpole
        rw [Complex.add_re, linePt_re, Complex.one_re] at hre
        norm_num at hre
    haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hpow : Continuous (fun v : ℝ =>
        (x : ℂ) ^ ((1 : ℂ) + (v : ℂ) * I)) :=
      (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
    have hkernel : Continuous (fun v : ℝ =>
        smoothAFEGaussianKernel ((1 : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (by fun_prop)).div
        (by fun_prop) (fun v hzero => by
          have hre := congrArg Complex.re hzero
          norm_num at hre)
    unfold smoothAFEZetaSquareMellinIntegrand
    exact ((hzeta.pow 2).mul hpow).mul hkernel |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall hbound

theorem exists_norm_smoothAFEZetaSquareMellinIntegrand_left_one_le
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖smoothAFEZetaSquareMellinIntegrand (linePt tau) x
          ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
        C * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  let D : ℝ := 6 * (1 + |tau|) * (4 + |tau|)
  let C : ℝ := (x⁻¹ * Real.exp 1 * D) * D
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro v
  have hsingle := norm_smoothAFEZetaMellinIntegrand_left_one_le hx tau v
  have hsingle' :
      ‖smoothAFEZetaMellinIntegrand (linePt tau) x
          ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
        (x⁻¹ * Real.exp 1 * D) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
    simpa [D] using hsingle
  have hzeta0 :=
    norm_riemannZeta_smoothAFEZetaLeftLinePt_le_quadratic (tau + v)
  have harg :
      linePt tau + ((-1 : ℂ) + (v : ℂ) * I) =
        smoothAFEZetaLeftLinePt (tau + v) :=
    linePt_add_left_one_eq_smoothAFEZetaLeftLinePt tau v
  have habs : |tau + v| ≤ |tau| + |v| := abs_add_le tau v
  have hzeta :
      ‖riemannZeta (linePt tau + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
        D * (1 + |v|) ^ 2 := by
    rw [harg]
    refine hzeta0.trans ?_
    have hfirst : 1 + |tau + v| ≤ (1 + |tau|) * (1 + |v|) := by
      have ht : 0 ≤ |tau| := abs_nonneg tau
      have hv : 0 ≤ |v| := abs_nonneg v
      nlinarith
    have hsecond : 4 + |tau + v| ≤ (4 + |tau|) * (1 + |v|) := by
      have ht : 0 ≤ |tau| := abs_nonneg tau
      have hv : 0 ≤ |v| := abs_nonneg v
      nlinarith
    calc
      6 * (1 + |tau + v|) * (4 + |tau + v|)
        ≤ 6 * ((1 + |tau|) * (1 + |v|)) *
            ((4 + |tau|) * (1 + |v|)) := by gcongr
      _ = D * (1 + |v|) ^ 2 := by dsimp only [D]; ring
  rw [smoothAFEZetaSquareMellinIntegrand_eq_single_mul_zeta, norm_mul]
  calc
    ‖smoothAFEZetaMellinIntegrand (linePt tau) x
          (-1 + ↑v * I)‖ *
        ‖riemannZeta (linePt tau + (-1 + ↑v * I))‖
      ≤ ((x⁻¹ * Real.exp 1 * D) *
          ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))) *
        (D * (1 + |v|) ^ 2) := by gcongr
    _ = C * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
      dsimp only [C]
      ring

theorem smoothAFEZetaSquareMellinIntegrand_left_one_verticalIntegrable
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    Complex.VerticalIntegrable
      (smoothAFEZetaSquareMellinIntegrand (linePt tau) x) (-1) := by
  rw [Complex.VerticalIntegrable]
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_smoothAFEZetaSquareMellinIntegrand_left_one_le hx tau
  have hmajor : Integrable (fun v : ℝ =>
      C * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
    RHTower.integrable_one_add_abs_pow_four_mul_exp_neg_sq.const_mul C
  apply Integrable.mono' hmajor
  · have hzeta : Continuous (fun v : ℝ =>
        riemannZeta
          (linePt tau + (((-1 : ℝ) : ℂ) + (v : ℂ) * I))) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      · fun_prop
      · intro hpole
        have hre := congrArg Complex.re hpole
        rw [Complex.add_re, linePt_re, Complex.one_re] at hre
        norm_num at hre
    haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hpow : Continuous (fun v : ℝ =>
        (x : ℂ) ^ (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) :=
      (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
    have hkernel : Continuous (fun v : ℝ =>
        smoothAFEGaussianKernel
          (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (by fun_prop)).div
        (by fun_prop) (fun v hzero => by
          have hre := congrArg Complex.re hzero
          norm_num at hre)
    unfold smoothAFEZetaSquareMellinIntegrand
    exact ((hzeta.pow 2).mul hpow).mul hkernel |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [ofReal_neg, ofReal_one] using hbound v


end RHTower.Sieve
