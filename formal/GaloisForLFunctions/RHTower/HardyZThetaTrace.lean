import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# Hardy Z as the normalized positive-theta trace

The continuous Hardy phase identifies the critical-line zeta value with one real amplitude.
The theta-cusp Fourier theory identifies the same centered Xi value with a positive-source cosine
trace.  This file closes the two interfaces exactly.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- The positive real factor converting Hardy Z into the centered Xi trace. -/
noncomputable def hardyZArchScale (τ : ℝ) : ℝ :=
  (1 / 4 + τ ^ 2) * ‖Gammaℝ (linePt τ)‖

/-- The Hardy-Z/Xi scale is strictly positive at every real height. -/
theorem hardyZArchScale_pos (τ : ℝ) : 0 < hardyZArchScale τ := by
  exact mul_pos (by positivity)
    (norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ)))

/-- The positive archimedean Hardy scale is even in the height. -/
@[simp] theorem hardyZArchScale_neg (τ : ℝ) :
    hardyZArchScale (-τ) = hardyZArchScale τ := by
  unfold hardyZArchScale
  rw [neg_sq]
  congr 1
  rw [show linePt (-τ) = 1 - linePt τ by
    unfold linePt
    push_cast
    ring]
  rw [← conj_linePt τ, Gammaℝ_conj, Complex.norm_conj]

/-- **Exact real-Xi/Hardy-Z value reflection.**  The corpus's centered real function `Xi` is the
negative Hardy amplitude multiplied by half of the positive archimedean scale. -/
theorem Xi_eq_neg_half_hardyZArchScale_mul_hardyZ (τ : ℝ) :
    Xi τ = -(hardyZArchScale τ) / 2 * hardyZ τ := by
  have hvalue := congrArg Complex.re (xi_line_eq_scale_mul_hardyZ τ)
  rw [Complex.ofReal_re] at hvalue
  unfold Xi
  rw [show ((1 : ℂ) / 2 + (τ : ℂ) * I) = linePt τ by
    unfold linePt
    push_cast
    ring]
  rw [hvalue]
  unfold hardyZArchScale
  ring

/-- The centered real Xi function is even. -/
@[simp] theorem Xi_neg (τ : ℝ) : Xi (-τ) = Xi τ := by
  have h := XiC_even (τ : ℂ)
  rw [show -((τ : ℂ)) = ((-τ : ℝ) : ℂ) by push_cast; rfl] at h
  rw [XiC_ofReal, XiC_ofReal] at h
  exact Complex.ofReal_injective h

/-- The real Xi and Hardy Z sign conventions are opposite at every nonzero value. -/
theorem Xi_pos_iff_hardyZ_neg (τ : ℝ) : 0 < Xi τ ↔ hardyZ τ < 0 := by
  rw [Xi_eq_neg_half_hardyZArchScale_mul_hardyZ]
  have hs := hardyZArchScale_pos τ
  constructor <;> intro h <;> nlinarith

/-- Exact zero interface between the corpus's real `Xi` and Hardy Z. -/
theorem Xi_eq_zero_iff_hardyZ (τ : ℝ) : Xi τ = 0 ↔ hardyZ τ = 0 := by
  rw [Xi_eq_neg_half_hardyZArchScale_mul_hardyZ]
  have hs := hardyZArchScale_pos τ
  constructor <;> intro h <;> nlinarith

/-- Removing the Gamma norm from Hardy Z leaves the completed positive-theta Fourier trace,
with exactly the rational correction forced by Xi's pole subtraction. -/
theorem norm_Gammaℝ_mul_hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction (τ : ℝ) :
    ‖Gammaℝ (linePt τ)‖ * hardyZ τ =
      (𝓕 xiThetaPositiveSource (τ / (4 * π))).re - 1 / (1 / 4 + τ ^ 2) := by
  have htrace :
      completedRiemannZeta₀ (linePt τ) =
        ((𝓕 xiThetaPositiveSource (τ / (4 * π))).re : ℂ) := by
    simpa [linePt] using completedRiemannZeta₀_critical_eq_re_positiveFourier τ
  have hpoly : linePt τ * (linePt τ - 1) / 2 =
      ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hvalue := xi_line_eq_scale_mul_hardyZ τ
  rw [xi, hpoly, htrace] at hvalue
  have hreal :
      (-(1 / 4 + τ ^ 2) / 2) *
            (𝓕 xiThetaPositiveSource (τ / (4 * π))).re + 1 / 2 =
        (-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * hardyZ τ := by
    have hre := congrArg Complex.re hvalue
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hre
    norm_num at hre
    convert hre using 1 <;> ring
  have hq : 1 / 4 + τ ^ 2 ≠ 0 := by positivity
  field_simp [hq]
  nlinarith [hreal]

/-- Exact positive-source Fourier formula for Hardy Z. -/
theorem hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction (τ : ℝ) :
    hardyZ τ =
      ((𝓕 xiThetaPositiveSource (τ / (4 * π))).re - 1 / (1 / 4 + τ ^ 2)) /
        ‖Gammaℝ (linePt τ)‖ := by
  have hn : ‖Gammaℝ (linePt τ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ))
  rw [eq_div_iff hn]
  simpa [mul_comm] using
    norm_Gammaℝ_mul_hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction τ

/-- The centered Xi value on the critical line is exactly twice the positive theta-cusp cosine
trace, expressed in the `linePt` coordinate used by Hardy Z. -/
theorem xi_line_eq_two_mul_thetaCuspCosine (τ : ℝ) :
    xi (linePt τ) =
      ((2 * ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x) : ℝ) : ℂ) := by
  simpa [XiC, linePt] using XiC_ofReal_eq_two_mul_thetaCuspCosine τ

/-- **Exact positive-theta value law for Hardy Z.**  Multiplication by the everywhere-positive
archimedean scale turns Hardy Z into minus four times the theta-cusp cosine trace. -/
theorem hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine (τ : ℝ) :
    hardyZArchScale τ * hardyZ τ =
      -4 * ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x) := by
  have hvalue := xi_line_eq_scale_mul_hardyZ τ
  rw [xi_line_eq_two_mul_thetaCuspCosine] at hvalue
  have hreal :
      2 * ∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (τ * x) =
        (-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * hardyZ τ := by
    have hre := congrArg Complex.re hvalue
    change
      2 * ∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (τ * x) =
        (-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * hardyZ τ at hre
    exact hre
  unfold hardyZArchScale
  nlinarith [hreal]

/-- **Two-height value reflection.**  The product of two Hardy values and the product of the
corresponding positive-theta cosine traces differ by an explicitly positive scale.  This single
law subsumes every two-height sign-bracket transfer between the two models. -/
theorem hardyZArchScale_pair_mul_hardyZ_pair_eq_sixteen_mul_thetaCuspCosine_pair
    (t₁ t₂ : ℝ) :
    (hardyZArchScale t₁ * hardyZArchScale t₂) * (hardyZ t₁ * hardyZ t₂) =
      16 * ((∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₂ * x))) := by
  calc
    (hardyZArchScale t₁ * hardyZArchScale t₂) * (hardyZ t₁ * hardyZ t₂) =
        (hardyZArchScale t₁ * hardyZ t₁) *
          (hardyZArchScale t₂ * hardyZ t₂) := by ring
    _ = (-4 * ∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (-4 * ∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (t₂ * x)) := by
      rw [hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine,
        hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine]
    _ = 16 * ((∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0,
          thetaCuspFullSource x * Real.cos (t₂ * x))) := by ring

/-- The positive archimedean pair scale makes theta-cusp and Hardy-Z sign brackets equivalent. -/
theorem hardyZ_mul_nonpos_iff_thetaCuspCosine_mul_nonpos (t₁ t₂ : ℝ) :
    hardyZ t₁ * hardyZ t₂ ≤ 0 ↔
      (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₂ * x)) ≤ 0 := by
  have hs : 0 < hardyZArchScale t₁ * hardyZArchScale t₂ :=
    mul_pos (hardyZArchScale_pos t₁) (hardyZArchScale_pos t₂)
  have hv :=
    hardyZArchScale_pair_mul_hardyZ_pair_eq_sixteen_mul_thetaCuspCosine_pair t₁ t₂
  constructor <;> intro h <;> nlinarith

/-- The positive archimedean pair scale also preserves strict opposite-sign brackets exactly. -/
theorem hardyZ_mul_neg_iff_thetaCuspCosine_mul_neg (t₁ t₂ : ℝ) :
    hardyZ t₁ * hardyZ t₂ < 0 ↔
      ( ∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₂ * x)) < 0 := by
  have hs : 0 < hardyZArchScale t₁ * hardyZArchScale t₂ :=
    mul_pos (hardyZArchScale_pos t₁) (hardyZArchScale_pos t₂)
  have hv :=
    hardyZArchScale_pair_mul_hardyZ_pair_eq_sixteen_mul_thetaCuspCosine_pair t₁ t₂
  constructor <;> intro h <;> nlinarith

/-- Exact theta-cusp cosine formula for Hardy Z. -/
theorem hardyZ_eq_neg_four_mul_thetaCuspCosine_div_archScale (τ : ℝ) :
    hardyZ τ =
      (-4 * ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x)) / hardyZArchScale τ := by
  rw [eq_div_iff (ne_of_gt (hardyZArchScale_pos τ))]
  simpa [mul_comm] using
    hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine τ

/-- **Hardy-Z sign reflection.**  A negative Hardy value is exactly a positive theta-cusp cosine
trace; the positive archimedean scale discharges every denominator premise. -/
theorem hardyZ_neg_iff_thetaCuspCosine_pos (τ : ℝ) :
    hardyZ τ < 0 ↔
      0 < ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x) := by
  have hscale := hardyZArchScale_pos τ
  have hvalue := hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine τ
  constructor <;> intro h <;> nlinarith

/-- Fourier-threshold form of the same Hardy-Z sign reflection. -/
theorem hardyZ_neg_iff_re_fourier_xiThetaPositiveSource_lt_correction (τ : ℝ) :
    hardyZ τ < 0 ↔
      (𝓕 xiThetaPositiveSource (τ / (4 * π))).re < 1 / (1 / 4 + τ ^ 2) := by
  have hnorm : 0 < ‖Gammaℝ (linePt τ)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ))
  have hvalue :=
    norm_Gammaℝ_mul_hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction τ
  constructor <;> intro h <;> nlinarith

/-- Hardy Z vanishes exactly when the positive theta-cusp cosine trace vanishes. -/
theorem hardyZ_eq_zero_iff_thetaCuspCosine (τ : ℝ) :
    hardyZ τ = 0 ↔
      ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x) = 0 := by
  have hscale := hardyZArchScale_pos τ
  have hvalue := hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine τ
  constructor <;> intro h <;> nlinarith

/-- **Unconditional source-level critical-line zero criterion for zeta.** -/
theorem riemannZeta_line_eq_zero_iff_thetaCuspCosine (τ : ℝ) :
    riemannZeta (linePt τ) = 0 ↔
      ∫ x : ℝ in Ioi 0,
        thetaCuspFullSource x * Real.cos (τ * x) = 0 := by
  exact (riemannZeta_line_eq_zero_iff_hardyZ τ).trans
    (hardyZ_eq_zero_iff_thetaCuspCosine τ)

/-- **Unconditional positive-source Fourier threshold criterion for critical-line zeta zeros.** -/
theorem riemannZeta_line_eq_zero_iff_re_fourier_xiThetaPositiveSource (τ : ℝ) :
    riemannZeta (linePt τ) = 0 ↔
      (𝓕 xiThetaPositiveSource (τ / (4 * π))).re = 1 / (1 / 4 + τ ^ 2) := by
  rw [riemannZeta_line_eq_zero_iff_hardyZ]
  have hnorm : 0 < ‖Gammaℝ (linePt τ)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ))
  have hvalue :=
    norm_Gammaℝ_mul_hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction τ
  constructor <;> intro h <;> nlinarith

/-- **Positive-source finite-tower zero criterion.**  The theta-cusp cosine trace vanishes exactly
when every nontrivial symmetrized-EM Hardy approximant is trapped by its explicit error cone. -/
theorem thetaCuspCosine_eq_zero_iff_forall_hardySEM_trapped (τ : ℝ) :
    (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (τ * x)) = 0 ↔
      ∀ N : ℕ, 1 ≤ N → |hardySEM N τ| ≤ hardySEMError N τ := by
  exact (riemannZeta_line_eq_zero_iff_thetaCuspCosine τ).symm.trans
    (riemannZeta_line_eq_zero_iff_forall_hardySEM_trapped τ)

/-- **Positive-source finite nonvanishing criterion.**  The theta-cusp cosine trace is nonzero
exactly when one finite symmetrized-EM level clears its explicit error cone. -/
theorem thetaCuspCosine_ne_zero_iff_exists_hardySEM_certificate (τ : ℝ) :
    (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (τ * x)) ≠ 0 ↔
      ∃ N : ℕ, 1 ≤ N ∧ hardySEMError N τ < |hardySEM N τ| := by
  exact (not_congr (riemannZeta_line_eq_zero_iff_thetaCuspCosine τ)).symm.trans
    (riemannZeta_line_ne_zero_iff_exists_hardySEM_certificate τ)

end RHTower
