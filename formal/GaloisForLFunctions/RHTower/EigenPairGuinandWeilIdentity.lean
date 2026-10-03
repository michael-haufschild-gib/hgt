import GaloisForLFunctions.RHTower.EigenPairFrequencyInversion
import GaloisForLFunctions.RHTower.EigenPairRectangleIdentity
import GaloisForLFunctions.RHTower.EigenPairVerticalBound
import GaloisForLFunctions.RHTower.XiCDerivStripDecay
import GaloisForLFunctions.RHTower.XiWeilArithmeticGram
import GaloisForLFunctions.RHTower.XiThetaEigenGramLaw
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.HedenmalmPairWeilPolarizationCapstone

/-!
# The eigen-pair Guinand–Weil identity

For zeros `α, β` of `XiC` let `U_α = i·dslope XiC α` be the removable quotients (the Fourier
images of the theta eigenfunctions) and `c_{α,β}(y) = ∫ u_α(x) conj(u_β(x - y)) dx` the time-side
correlation of the eigenfunctions.  For every line height `1/2 < Y < 1`:

`⟪U_α, U_β⟫_W = (2π)⁻¹ (A_Y(α,β) + A_Y(-α,-β)) - ∑_n Λ(n) n^{-1/2} (c_{α,β}(log n) + c_{α,β}(-log n))`,

where `⟪·,·⟫_W` is the multiplicity-exact Weil polarization (the antidiagonal Gram) and
`A_Y(α,β) = ∫ γ(1/2 + Y + it) U_α(t - iY) conj(U_β(t + iY)) dt` with
`γ(s) = s⁻¹ + (s-1)⁻¹ + Γ_ℝ'/Γ_ℝ(s)` is the archimedean pairing.  All series and integrals
converge absolutely.

The proof is the rectangle argument for the single-pole integrand
`(XiC'/XiC)·U_α·U_β^♯ = i·XiC'·U_β^♯/(z - α)`: the boundary integral is `2πi` times the residue at
`α`, which is the antidiagonal Gram datum; the vertical edges vanish by the substrip decay; the top
edge folds onto the bottom edge for `(-α, -β)` by the evenness of `XiC`; and on the bottom edge
`Re s > 1` the logarithmic derivative is the prime–archimedean expression, integrated termwise and
evaluated frequency by frequency by Fourier inversion.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex Filter Topology

/-! ## Evenness of the quotients -/

theorem dslope_XiC_neg (α z : ℂ) : dslope XiC α (-z) = -dslope XiC (-α) z := by
  by_cases hz : z = -α
  · subst hz
    rw [neg_neg, dslope_same, dslope_same, deriv_XiC_neg, neg_neg]
  · have h1 : -z ≠ α := fun h => hz (by rw [← h, neg_neg])
    rw [dslope_of_ne _ h1, dslope_of_ne _ hz, slope_def_field, slope_def_field, XiC_even,
      show XiC (-α) = XiC α from XiC_even α]
    have hden : z - -α ≠ 0 := sub_ne_zero.mpr hz
    have hden' : -z - α ≠ 0 := by
      intro h; apply hden; linear_combination -h
    field_simp
    ring

theorem xiThetaEigenFourier_neg (α z : ℂ) :
    xiThetaEigenFourier α (-z) = -xiThetaEigenFourier (-α) z := by
  rw [xiThetaEigenFourier, xiThetaEigenFourier, dslope_XiC_neg]; ring

theorem xiWeilSharp_xiThetaEigenFourier_neg (β z : ℂ) :
    xiWeilSharp (xiThetaEigenFourier β) (-z) = -xiWeilSharp (xiThetaEigenFourier (-β)) z := by
  rw [xiWeilSharp, xiWeilSharp, map_neg, xiThetaEigenFourier_neg, map_neg]

/-- The eigen-pair contour integrand `(XiC'/XiC)·U_α·U_β^♯`. -/
def eigenPairIntegrand (α β z : ℂ) : ℂ :=
  logDeriv XiC z * xiThetaEigenFourier α z * xiWeilSharp (xiThetaEigenFourier β) z

theorem eigenPairIntegrand_neg (α β z : ℂ) :
    eigenPairIntegrand α β (-z) = -eigenPairIntegrand (-α) (-β) z := by
  rw [eigenPairIntegrand, eigenPairIntegrand, logDeriv_XiC_neg, xiThetaEigenFourier_neg,
    xiWeilSharp_xiThetaEigenFourier_neg]
  ring

/-- The single-pole form `XiC'·U_β^♯·(z - p)⁻¹`. -/
def eigenSinglePole (β p z : ℂ) : ℂ :=
  deriv XiC z * xiWeilSharp (xiThetaEigenFourier β) z * (z - p)⁻¹

/-- Away from the divisor, the contour integrand is `i` times the single-pole form. -/
theorem eigenPairIntegrand_eq_singlePole {α β z : ℂ} (hα : XiC α = 0) (hz : XiC z ≠ 0)
    (hzα : z ≠ α) : eigenPairIntegrand α β z = I * eigenSinglePole β α z := by
  rw [eigenPairIntegrand, eigenSinglePole, xiThetaEigenFourier_eq_div hα hzα, logDeriv_apply]
  have hden : α - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzα)
  have hden' : z - α ≠ 0 := sub_ne_zero.mpr hzα
  field_simp
  ring

theorem eigenSinglePole_neg (β p z : ℂ) :
    eigenSinglePole β p (-z) = -eigenSinglePole (-β) (-p) z := by
  rw [eigenSinglePole, eigenSinglePole, deriv_XiC_neg, xiWeilSharp_xiThetaEigenFourier_neg,
    show -z - p = -(z - -p) by ring, inv_neg]
  ring

/-! ## Bounds on horizontal lines and vertical edges -/

theorem continuous_deriv_XiC : Continuous (deriv XiC) := by
  have h : AnalyticOnNhd ℂ XiC Set.univ := fun z _ =>
    XiC_differentiable.analyticAt z
  exact (h.deriv.continuousOn).comp_continuous continuous_id (fun _ => Set.mem_univ _)

theorem continuous_xiWeilSharp_eigen (β : ℂ) :
    Continuous (xiWeilSharp (xiThetaEigenFourier β)) := by
  unfold xiWeilSharp
  exact Complex.continuous_conj.comp
    ((continuous_xiThetaEigenFourier β).comp Complex.continuous_conj)

/-- The single-pole form is integrable on every horizontal line `|Im z| = Y` with
`|Im p| < Y < 1`. -/
theorem integrable_eigenSinglePole_line {β p : ℂ} (hβ : XiC β = 0) {Y Y' : ℝ} (hY1 : Y < 1)
    (hpY : |p.im| < Y) (hY' : |Y'| = Y) :
    Integrable (fun t : ℝ => eigenSinglePole β p ((t : ℂ) + (Y' : ℂ) * I)) := by
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hpY.le
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_XiC_deriv_horizontal_le hY1 (by norm_num : (0 : ℝ) ≤ 1/4)
    (by linarith [Real.pi_gt_three])
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_xiThetaEigenFourier_horizontal_le hβ hY0 hY1
    (by norm_num : (0 : ℝ) ≤ 1/4) (by linarith [Real.pi_gt_three])
  have hgap : 0 < Y - |p.im| := by linarith
  have hbase : Integrable (fun t : ℝ => Real.exp (-(1/4 : ℝ) * |t|)) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_abs 0 (by norm_num : (0 : ℝ) < 1/4)
  refine Integrable.mono' (hbase.const_mul (C₁ * C₂ * (Y - |p.im|)⁻¹)) ?_ ?_
  · have hne : ∀ t : ℝ, (t : ℂ) + (Y' : ℂ) * I - p ≠ 0 := fun t h => by
      have := congrArg Complex.im h
      simp at this
      have : |p.im| = Y := by rw [show p.im = Y' by linarith, hY']
      linarith
    refine Continuous.aestronglyMeasurable ?_
    unfold eigenSinglePole
    refine ((continuous_deriv_XiC.comp (by fun_prop)).mul
      ((continuous_xiWeilSharp_eigen β).comp (by fun_prop))).mul ?_
    exact Continuous.inv₀ (by fun_prop) hne
  · refine Eventually.of_forall fun t => ?_
    have hb₁ := h₁ t Y' (le_of_eq hY')
    have hb₂c : ‖xiWeilSharp (xiThetaEigenFourier β) ((t : ℂ) + (Y' : ℂ) * I)‖ =
        ‖xiThetaEigenFourier β ((t : ℂ) + ((-Y' : ℝ) : ℂ) * I)‖ := by
      rw [xiWeilSharp, RCLike.norm_conj]
      congr 1
      push_cast
      simp [map_add, map_mul, Complex.conj_I]
    have hb₂ : ‖xiWeilSharp (xiThetaEigenFourier β) ((t : ℂ) + (Y' : ℂ) * I)‖ ≤
        C₂ * Real.exp (-((1/4 : ℝ) * |t|)) := by
      rw [hb₂c]; exact h₂ t (-Y') (by rw [abs_neg, hY'])
    have hinv : ‖((t : ℂ) + (Y' : ℂ) * I - p)⁻¹‖ ≤ (Y - |p.im|)⁻¹ := by
      rw [norm_inv]
      refine inv_anti₀ hgap ?_
      calc Y - |p.im| = |Y'| - |p.im| := by rw [hY']
        _ ≤ |Y' - p.im| := abs_sub_abs_le_abs_sub _ _
        _ = |((t : ℂ) + (Y' : ℂ) * I - p).im| := by simp
        _ ≤ ‖(t : ℂ) + (Y' : ℂ) * I - p‖ := Complex.abs_im_le_norm _
    have hexp : Real.exp (-((1/4 : ℝ) * |t|)) * Real.exp (-((1/4 : ℝ) * |t|)) ≤
        Real.exp (-(1/4 : ℝ) * |t|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [abs_nonneg t])
    calc ‖eigenSinglePole β p ((t : ℂ) + (Y' : ℂ) * I)‖
        = ‖deriv XiC ((t : ℂ) + (Y' : ℂ) * I)‖ *
            ‖xiWeilSharp (xiThetaEigenFourier β) ((t : ℂ) + (Y' : ℂ) * I)‖ *
            ‖((t : ℂ) + (Y' : ℂ) * I - p)⁻¹‖ := by
          rw [eigenSinglePole, norm_mul, norm_mul]
      _ ≤ (C₁ * Real.exp (-((1/4 : ℝ) * |t|))) * (C₂ * Real.exp (-((1/4 : ℝ) * |t|))) *
            (Y - |p.im|)⁻¹ := by
          gcongr
      _ = C₁ * C₂ * (Y - |p.im|)⁻¹ *
            (Real.exp (-((1/4 : ℝ) * |t|)) * Real.exp (-((1/4 : ℝ) * |t|))) := by ring
      _ ≤ C₁ * C₂ * (Y - |p.im|)⁻¹ * Real.exp (-(1/4 : ℝ) * |t|) := by
          gcongr

/-- The left vertical edge of the single-pole integrand vanishes in the widening limit. -/
theorem tendsto_vertical_eigen_left {β p : ℂ} (hβ : XiC β = 0) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY1 : Y < 1) :
    Tendsto (fun X : ℝ => ∫ y in (-Y)..Y, eigenSinglePole β p ((-X : ℝ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
  have hβ' : XiC (-β) = 0 := by rw [XiC_even, hβ]
  have hR := tendsto_vertical_eigen_right (p := -p) hβ' hY1 (by norm_num : (0 : ℝ) < 1/4)
    (by linarith [Real.pi_gt_three]) hY0 hY0 le_rfl
  have heq : ∀ X : ℝ, (∫ y in (-Y)..Y, eigenSinglePole β p ((-X : ℝ) + (y : ℂ) * I)) =
      -∫ y in (-Y)..Y, deriv XiC ((X : ℂ) + (y : ℂ) * I) *
        xiWeilSharp (xiThetaEigenFourier (-β)) ((X : ℂ) + (y : ℂ) * I) *
        (((X : ℂ) + (y : ℂ) * I) - -p)⁻¹ := by
    intro X
    have hpt : ∀ y : ℝ, ((-X : ℝ) : ℂ) + (y : ℂ) * I = -((X : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      intro y; push_cast; ring
    simp_rw [hpt, eigenSinglePole_neg]
    rw [intervalIntegral.integral_neg]
    congr 1
    rw [intervalIntegral.integral_comp_neg
      (fun y : ℝ => eigenSinglePole (-β) (-p) ((X : ℂ) + (y : ℂ) * I)), neg_neg]
    rfl
  simp_rw [heq]
  simpa using hR.neg

/-! ## The rectangle limit -/

/-- **Rectangle limit.**  For a zero `α` and `|Im α| < Y < 1`, the bottom-minus-top line
integrals of the single-pole form equal `2πi` times its residue at `α`. -/
theorem integral_eigenSinglePole_lines {α β : ℂ} (hβ : XiC β = 0) {Y : ℝ} (hY1 : Y < 1)
    (hαY : |α.im| < Y) :
    (∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) -
        ∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + (Y : ℂ) * I) =
      2 * Real.pi * I * (deriv XiC α * xiWeilSharp (xiThetaEigenFourier β) α) := by
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hαY.le
  have hbot := integrable_eigenSinglePole_line hβ hY1 hαY (by rw [abs_neg, abs_of_nonneg hY0])
  have htop := integrable_eigenSinglePole_line hβ hY1 hαY (abs_of_nonneg hY0)
  have hF : Differentiable ℂ (xiThetaEigenFourier β) := fun z =>
    ((xiThetaEigenFourier_analytic β) z (Set.mem_univ z)).differentiableAt
  -- the rectangle identity for every large aperture
  have hrect : ∀ᶠ X : ℝ in atTop,
      ((∫ x in (-X)..X, eigenSinglePole β α ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)) -
          ∫ x in (-X)..X, eigenSinglePole β α ((x : ℂ) + (Y : ℂ) * I)) +
        I • (∫ y in (-Y)..Y, eigenSinglePole β α ((X : ℂ) + (y : ℂ) * I)) -
        I • (∫ y in (-Y)..Y, eigenSinglePole β α ((-X : ℝ) + (y : ℂ) * I)) =
      2 * Real.pi * I * (deriv XiC α * xiWeilSharp (xiThetaEigenFourier β) α) := by
    filter_upwards [eventually_gt_atTop (|α.re|)] with X hX
    have hre1 : ((-X : ℝ) + ((-Y : ℝ) : ℂ) * I).re < α.re := by
      simp; linarith [neg_abs_le α.re]
    have hre2 : α.re < ((X : ℂ) + (Y : ℂ) * I).re := by
      simp; linarith [le_abs_self α.re]
    have him1 : ((-X : ℝ) + ((-Y : ℝ) : ℂ) * I).im < α.im := by
      simp; linarith [neg_abs_le α.im]
    have him2 : α.im < ((X : ℂ) + (Y : ℂ) * I).im := by
      simp; linarith [le_abs_self α.im]
    have h := rectIntegral_singlePole_eigen hF hre1 hre2 him1 him2
    rw [rectIntegral] at h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Complex.add_im,
      zero_add] at h
    convert h using 3 <;> simp [eigenSinglePole]
  have hlimit : Tendsto (fun X : ℝ =>
      ((∫ x in (-X)..X, eigenSinglePole β α ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)) -
          ∫ x in (-X)..X, eigenSinglePole β α ((x : ℂ) + (Y : ℂ) * I)) +
        I • (∫ y in (-Y)..Y, eigenSinglePole β α ((X : ℂ) + (y : ℂ) * I)) -
        I • (∫ y in (-Y)..Y, eigenSinglePole β α ((-X : ℝ) + (y : ℂ) * I)))
      atTop (𝓝 (((∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) -
          ∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + (Y : ℂ) * I)) + I • 0 - I • 0)) := by
    refine ((((intervalIntegral_tendsto_integral hbot tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral htop tendsto_neg_atTop_atBot tendsto_id)).add
      ((tendsto_vertical_eigen_right hβ hY1 (by norm_num : (0 : ℝ) < 1/4)
        (by linarith [Real.pi_gt_three]) hY0 hY0 le_rfl).const_smul I)).sub
      ((tendsto_vertical_eigen_left hβ hY0 hY1).const_smul I))
  have := tendsto_nhds_unique hlimit (tendsto_const_nhds.congr' (hrect.mono fun X hX => hX.symm))
  simpa using this

/-! ## The prime–archimedean expansion of a bottom line -/

/-- The archimedean factor `γ(s) = s⁻¹ + (s - 1)⁻¹ + Γ_ℝ'/Γ_ℝ(s)`. -/
def eigenArchFactor (s : ℂ) : ℂ :=
  s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s

/-- The archimedean pairing `A_Y(α,β) = ∫ γ(1/2 + Y + it) U_α(t - iY) conj(U_β(t + iY)) dt`. -/
def eigenArchPairing (α β : ℂ) (Y : ℝ) : ℂ :=
  ∫ t : ℝ, eigenArchFactor (((1 / 2 + Y : ℝ) : ℂ) + t * I) * eigenPairLine α β Y t

/-- **The prime pairing** `P(α,β) = ∑_n Λ(n) n^{-1/2} (c_{α,β}(log n) + c_{α,β}(-log n))`. -/
def eigenPrimePairing (α β : ℂ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    (eigenPairCorrelation α β (Real.log n) + eigenPairCorrelation α β (-Real.log n))

theorem bottom_point_im {Y : ℝ} (t : ℝ) : ((t : ℂ) + ((-Y : ℝ) : ℂ) * I).im = -Y := by simp

theorem bottom_point_s {Y : ℝ} (t : ℝ) :
    (1 / 2 : ℂ) + ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) * I = ((1 / 2 + Y : ℝ) : ℂ) + t * I := by
  push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- On a bottom line the contour integrand is the prime–archimedean expression times the line
product. -/
theorem eigenPairIntegrand_bottom {α β : ℂ} {Y : ℝ} (hY : 1 / 2 < Y) (t : ℝ) :
    eigenPairIntegrand α β ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) =
      I * (eigenArchFactor (((1 / 2 + Y : ℝ) : ℂ) + t * I) * eigenPairLine α β Y t) -
        I * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((1 / 2 + Y : ℝ) : ℂ) + t * I) * eigenPairLine α β Y t) := by
  have him : ((t : ℂ) + ((-Y : ℝ) : ℂ) * I).im < -(1 / 2) := by rw [bottom_point_im]; linarith
  rw [eigenPairIntegrand, logDeriv_XiC_eq_arithmetic_of_im_lt_neg_half him, bottom_point_s,
    eigenPairLine, eigenArchFactor]
  have hsharp : xiWeilSharp (xiThetaEigenFourier β) ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (xiThetaEigenFourier β ((t : ℂ) + (Y : ℂ) * I)) := by
    rw [xiWeilSharp]; congr 2; push_cast; simp [Complex.conj_I]
  rw [hsharp]
  ring

/-- The von Mangoldt series is bounded on a vertical line in the half-plane of absolute
convergence. -/
theorem norm_LSeries_vonMangoldt_line_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ : ℂ) + t * I)‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeries]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans (le_of_eq (tsum_congr fun n => ?_))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.norm_term_eq, if_neg hn.ne']
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem integrable_LSeries_mul_eigenPairLine {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0)
    {Y : ℝ} (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    Integrable (fun t : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (((1 / 2 + Y : ℝ) : ℂ) + t * I) * eigenPairLine α β Y t) := by
  have hσ : 1 < 1 / 2 + Y := by linarith
  have hW : Integrable (eigenPairLine α β Y) :=
    integrable_eigenPair_line hα hβ (A := |Y|) (δ := 1/4) (abs_nonneg _)
      (by rw [abs_of_pos (by linarith)]; exact hY1) (by norm_num)
      (by linarith [Real.pi_gt_three]) le_rfl
  refine hW.bdd_mul (c := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    (n : ℝ) ^ (-(1 / 2 + Y))) ?_ (Eventually.of_forall fun t =>
      norm_LSeries_vonMangoldt_line_le hσ t)
  refine Continuous.aestronglyMeasurable ?_
  have hd := LSeries_differentiableOn (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  refine hd.continuousOn.comp_continuous (by fun_prop) fun t => ?_
  show LSeries.abscissaOfAbsConv _ < (((((1 / 2 + Y : ℝ) : ℂ) + t * I)).re : EReal)
  refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by exact_mod_cast hy)) ?_
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero]
  exact_mod_cast hσ

/-- **Bottom-line evaluation.**  The integral of the contour integrand along a bottom line is
`i A_Y(α,β) - 2πi ∑ Λ(n) n^{-1/2} c_{-α,-β}(-log n)`. -/
theorem integral_eigenPairIntegrand_bottom {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0)
    {Y : ℝ} (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    (∫ t : ℝ, eigenPairIntegrand α β ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) =
      I * eigenArchPairing α β Y -
        I * ∑' n : ℕ, 2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * eigenPairCorrelation (-α) (-β) (-Real.log n) := by
  have hαh := abs_im_lt_half_of_XiC_eq_zero hα
  have hσ : 1 < 1 / 2 + Y := by linarith
  have hYabs : |Y| < 1 := by rw [abs_of_pos (by linarith)]; exact hY1
  have hYα : (1 / 2 : ℝ) ≤ |Y| := by rw [abs_of_pos (by linarith)]; linarith
  have hW : Integrable (eigenPairLine α β Y) :=
    integrable_eigenPair_line hα hβ (A := |Y|) (δ := 1/4) (abs_nonneg _) hYabs (by norm_num)
      (by linarith [Real.pi_gt_three]) le_rfl
  have hL := integrable_LSeries_mul_eigenPairLine hα hβ hY hY1
  -- the contour integrand is integrable on the line
  have hG : Integrable (fun t : ℝ => eigenPairIntegrand α β ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) := by
    have hS := integrable_eigenSinglePole_line (p := α) hβ hY1 (by linarith)
      (Y' := -Y) (by rw [abs_neg, abs_of_pos (by linarith)])
    refine (hS.const_mul I).congr (Eventually.of_forall fun t => ?_)
    have hz : XiC ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) ≠ 0 := XiC_ne_zero_of_half_le_abs_im
      (by rw [bottom_point_im, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hzα : (t : ℂ) + ((-Y : ℝ) : ℂ) * I ≠ α := by
      intro h
      have := congrArg Complex.im h
      rw [bottom_point_im] at this
      rw [← this, abs_neg, abs_of_pos (by linarith)] at hαh
      linarith
    exact (eigenPairIntegrand_eq_singlePole hα hz hzα).symm
  have hA : Integrable (fun t : ℝ =>
      eigenArchFactor (((1 / 2 + Y : ℝ) : ℂ) + t * I) * eigenPairLine α β Y t) := by
    refine ((hG.const_mul (-I)).add hL).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    rw [eigenPairIntegrand_bottom hY]
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [eigenPairIntegrand_bottom hY]
  rw [integral_sub (hA.const_mul I) (hL.const_mul I), integral_const_mul, integral_const_mul,
    eigenArchPairing, integral_LSeries_vonMangoldt_mul_eq_tsum hσ hW]
  congr 2
  refine tsum_congr fun n => ?_
  exact integral_vonMangoldt_term_mul_eigenPairLine hα hβ hYabs hYα n

theorem summable_eigenPrimeTerm {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) {Y : ℝ}
    (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    Summable fun n : ℕ => 2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * eigenPairCorrelation (-α) (-β) (-Real.log n) := by
  have hσ : 1 < 1 / 2 + Y := by linarith
  have hYabs : |Y| < 1 := by rw [abs_of_pos (by linarith)]; exact hY1
  have hYα : (1 / 2 : ℝ) ≤ |Y| := by rw [abs_of_pos (by linarith)]; linarith
  have hW : Integrable (eigenPairLine α β Y) :=
    integrable_eigenPair_line hα hβ (A := |Y|) (δ := 1/4) (abs_nonneg _) hYabs (by norm_num)
      (by linarith [Real.pi_gt_three]) le_rfl
  refine Summable.of_norm_bounded
    ((summable_vonMangoldt_mul_rpow hσ).mul_right (∫ t : ℝ, ‖eigenPairLine α β Y t‖)) fun n => ?_
  rw [← integral_vonMangoldt_term_mul_eigenPairLine hα hβ hYabs hYα n,
    ← integral_norm_vonMangoldt_line_term (F := eigenPairLine α β Y) n]
  exact norm_integral_le_integral_norm _

/-! ## The identity -/

/-- **The eigen-pair Guinand–Weil identity, residue form.**  For zeros `α, β` and every line
height `1/2 < Y < 1`, the residue datum `i XiC'(α)·U_β^♯(α)` equals the archimedean pairing minus
the prime pairing. -/
theorem eigenPair_guinandWeil_residue {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) {Y : ℝ}
    (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    I * deriv XiC α * xiWeilSharp (xiThetaEigenFourier β) α =
      (2 * Real.pi : ℂ)⁻¹ * (eigenArchPairing α β Y + eigenArchPairing (-α) (-β) Y) -
        eigenPrimePairing α β := by
  have hαh := abs_im_lt_half_of_XiC_eq_zero hα
  have hβh := abs_im_lt_half_of_XiC_eq_zero hβ
  have hnα : XiC (-α) = 0 := by rw [XiC_even, hα]
  have hnβ : XiC (-β) = 0 := by rw [XiC_even, hβ]
  have hαY : |α.im| < Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  -- the rectangle limit, written with the contour integrand
  have hlines := integral_eigenSinglePole_lines hβ hY1 hαY
  have hbotG : (∫ t : ℝ, eigenPairIntegrand α β ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) =
      I * ∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hz : XiC ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) ≠ 0 := XiC_ne_zero_of_half_le_abs_im
      (by rw [bottom_point_im, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hzα : (t : ℂ) + ((-Y : ℝ) : ℂ) * I ≠ α := by
      intro h
      have := congrArg Complex.im h
      rw [bottom_point_im] at this
      rw [← this, abs_neg, abs_of_pos (by linarith)] at hαY
      linarith
    exact eigenPairIntegrand_eq_singlePole hα hz hzα
  -- the top line folds onto the bottom line of the negated zeros
  have htopG : (∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + (Y : ℂ) * I)) =
      I * ∫ t : ℝ, eigenPairIntegrand (-α) (-β) ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
    have hpt : ∀ t : ℝ, (t : ℂ) + (Y : ℂ) * I = -(((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
      intro t; push_cast; ring
    have hrw : (fun t : ℝ => eigenSinglePole β α ((t : ℂ) + (Y : ℂ) * I)) =
        fun t => I * eigenPairIntegrand (-α) (-β) (((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
      funext t
      rw [hpt t]
      have hz : XiC (-(((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I)) ≠ 0 := by
        rw [← hpt t]
        exact XiC_ne_zero_of_half_le_abs_im (by simp [abs_of_pos (by linarith : 0 < Y)]; linarith)
      have hzα : -(((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I) ≠ α := by
        rw [← hpt t]
        intro h
        have := congrArg Complex.im h
        simp at this
        rw [← this, abs_of_pos (by linarith)] at hαY
        linarith
      have h1 := eigenPairIntegrand_eq_singlePole (β := β) hα hz hzα
      rw [eigenPairIntegrand_neg] at h1
      have h2 : eigenSinglePole β α (-(((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I)) =
          -I * -eigenPairIntegrand (-α) (-β) (((-t : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * I) := by
        rw [h1, ← mul_assoc, show -I * I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
      rw [h2]
      ring
    rw [hrw, integral_const_mul]
    congr 1
    exact integral_neg_eq_self (fun t : ℝ =>
      eigenPairIntegrand (-α) (-β) ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) volume
  have hbot := integral_eigenPairIntegrand_bottom hα hβ hY hY1
  have hbot' := integral_eigenPairIntegrand_bottom hnα hnβ hY hY1
  simp only [neg_neg] at hbot'
  -- assemble
  have hS1 : ∫ t : ℝ, eigenSinglePole β α ((t : ℂ) + ((-Y : ℝ) : ℂ) * I) =
      -I * (∫ t : ℝ, eigenPairIntegrand α β ((t : ℂ) + ((-Y : ℝ) : ℂ) * I)) := by
    rw [hbotG, ← mul_assoc, show -I * I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  rw [hS1, htopG, hbot, hbot'] at hlines
  have hsum1 := summable_eigenPrimeTerm hα hβ hY hY1
  have hsum2 := summable_eigenPrimeTerm hnα hnβ hY hY1
  simp only [neg_neg] at hsum2
  have hP : eigenPrimePairing α β =
      (2 * Real.pi : ℂ)⁻¹ * ((∑' n : ℕ, 2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * eigenPairCorrelation (-α) (-β) (-Real.log n)) +
        ∑' n : ℕ, 2 * Real.pi * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * eigenPairCorrelation α β (-Real.log n)) := by
    rw [← hsum1.tsum_add hsum2, ← tsum_mul_left, eigenPrimePairing]
    refine tsum_congr fun n => ?_
    rw [eigenPairCorrelation_neg_neg hα hβ]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    field_simp
  rw [hP]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have key : I * deriv XiC α * xiWeilSharp (xiThetaEigenFourier β) α =
      (2 * Real.pi * I)⁻¹ * (I * (2 * Real.pi * I * (deriv XiC α *
        xiWeilSharp (xiThetaEigenFourier β) α))) := by
    field_simp
  rw [key, ← hlines]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The residue datum is the antidiagonal Gram entry. -/
theorem residue_eq_xiThetaEigenGram {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) :
    I * deriv XiC α * xiWeilSharp (xiThetaEigenFourier β) α = xiThetaEigenGram α β := by
  rw [xiThetaEigenGram, xiWeilSharp]
  by_cases hb : β = (starRingEnd ℂ) α
  · rw [if_pos hb, ← hb, xiThetaEigenFourier_self]
    by_cases hd : deriv XiC α = 0
    · rw [hd]; ring
    · have hord : analyticOrderAt XiC α = 1 := by
        have han : AnalyticAt ℂ XiC α := XiC_differentiable.analyticAt α
        have h1 := han.analyticOrderAt_deriv_add_one
        have h0 : analyticOrderAt (deriv XiC) α = 0 :=
          (XiC_differentiable.analyticAt α).deriv.analyticOrderAt_eq_zero.2 hd
        have hfun : (fun x => XiC x - XiC α) = XiC := by funext x; rw [hα, sub_zero]
        rw [h0, zero_add, hfun] at h1
        exact h1.symm
      rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hα, hord]
      simp
  · rw [if_neg hb]
    have hconj : XiC ((starRingEnd ℂ) α) = 0 := XiC_conj_eq_zero hα
    rw [xiThetaEigenFourier_eq_zero_of_XiC_eq_zero hβ hconj (Ne.symm hb), map_zero, mul_zero]

/-- **The eigen-pair Guinand–Weil identity.**  For zeros `α, β` of `XiC` and every line height
`1/2 < Y < 1`, the Weil polarization (antidiagonal Gram) of the theta-eigenfunction quotients is
the archimedean pairing minus the absolutely convergent prime pairing:
`⟪U_α, U_β⟫_W = (2π)⁻¹ (A_Y(α,β) + A_Y(-α,-β)) - ∑ Λ(n) n^{-1/2} (c(log n) + c(-log n))`. -/
theorem eigenPair_guinandWeil_identity {α β : ℂ} (hα : XiC α = 0) (hβ : XiC β = 0) {Y : ℝ}
    (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    xiWeilPolarization (xiThetaEigenFourier α) (xiThetaEigenFourier β) =
      (2 * Real.pi : ℂ)⁻¹ * (eigenArchPairing α β Y + eigenArchPairing (-α) (-β) Y) -
        eigenPrimePairing α β := by
  rw [xiWeilPolarization_thetaEigen hα hβ, ← residue_eq_xiThetaEigenGram hα hβ,
    eigenPair_guinandWeil_residue hα hβ hY hY1]

/-! ## Prime-sum form of eigen-span positivity -/

/-- The prime–archimedean Gram entry `(2π)⁻¹ (A_Y(α,β) + A_Y(-α,-β)) - P(α,β)`. -/
def eigenPrimeArchGram (α β : ℂ) (Y : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * (eigenArchPairing α β Y + eigenArchPairing (-α) (-β) Y) -
    eigenPrimePairing α β

/-- **Eigen-span positivity in prime-sum form.**  For any line height `1/2 < Y < 1`, the
prime–archimedean Gram matrix is positive definite on every nonzero finite span of theta
eigenfunctions exactly when the Riemann hypothesis holds and every zero is simple. -/
theorem eigenSpan_primeArch_positive_iff {Y : ℝ} (hY : 1 / 2 < Y) (hY1 : Y < 1) :
    (∀ (A : Finset ℂ) (c : ℂ → ℂ), (∀ α ∈ A, XiC α = 0) → (∃ α ∈ A, c α ≠ 0) →
        0 < (∑ α ∈ A, ∑ β ∈ A, c α * (starRingEnd ℂ) (c β) * eigenPrimeArchGram α β Y).re) ↔
      RiemannHypothesis ∧ ∀ α : ℂ, XiC α = 0 → deriv XiC α ≠ 0 := by
  have hcap : HedenmalmThetaEigenSpanPositiveDefinite ↔
      RiemannHypothesis ∧ ∀ α : ℂ, XiC α = 0 → deriv XiC α ≠ 0 :=
    hedenmalmPairWeilPolarizationLaw.2.2.2.2
  rw [← hcap, HedenmalmThetaEigenSpanPositiveDefinite]
  refine forall_congr' fun A => forall_congr' fun c => forall_congr' fun hA => ?_
  rw [xiWeilPolarization_thetaEigen_finsetSum hA c c]
  have hsum : (∑ α ∈ A, ∑ β ∈ A, c α * (starRingEnd ℂ) (c β) * eigenPrimeArchGram α β Y) =
      ∑ α ∈ A, ∑ β ∈ A, c α * (starRingEnd ℂ) (c β) * xiThetaEigenGram α β := by
    refine Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β hβ => ?_
    rw [eigenPrimeArchGram, ← eigenPair_guinandWeil_identity (hA α hα) (hA β hβ) hY hY1,
      xiWeilPolarization_thetaEigen (hA α hα) (hA β hβ)]
  rw [hsum]

/-! ## The Wronskian reduction of the time-side pair product -/

/-- **(D1)** The pointwise pair product satisfies
`(u_α ū_β)' = -i(α - β̄) u_α ū_β + i k (u_α - ū_β)`. -/
theorem hasDerivAt_eigenPairProduct {α β : ℂ} (hα : |α.im| < 1) (hβ : |β.im| < 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => hedenmalmCausalVolterra α y *
        (starRingEnd ℂ) (hedenmalmCausalVolterra β y))
      (-I * (α - (starRingEnd ℂ) β) * (hedenmalmCausalVolterra α x *
          (starRingEnd ℂ) (hedenmalmCausalVolterra β x)) +
        I * (thetaCuspFullSource x : ℂ) *
          (hedenmalmCausalVolterra α x - (starRingEnd ℂ) (hedenmalmCausalVolterra β x))) x := by
  have hu := hasDerivAt_hedenmalmCausalVolterra hα x
  have hv : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (hedenmalmCausalVolterra β y))
      ((starRingEnd ℂ) (-I * β * hedenmalmCausalVolterra β x -
        I * (thetaCuspFullSource x : ℂ))) x :=
    (hasDerivAt_hedenmalmCausalVolterra hβ x).star
  have h : HasDerivAt (fun y : ℝ => hedenmalmCausalVolterra α y *
      (starRingEnd ℂ) (hedenmalmCausalVolterra β y))
      ((-I * α * hedenmalmCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) *
          (starRingEnd ℂ) (hedenmalmCausalVolterra β x) +
        hedenmalmCausalVolterra α x * (starRingEnd ℂ) (-I * β * hedenmalmCausalVolterra β x -
          I * (thetaCuspFullSource x : ℂ))) x := hu.mul hv
  refine h.congr_deriv ?_
  simp only [map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **(D1)–(D2)** Off the antidiagonal `β ≠ ᾱ` (where `α - β̄ ≠ 0`) the pair product is the
derivative term plus the source terms:
`u_α ū_β = i (α - β̄)⁻¹ ((u_α ū_β)' - i k (u_α - ū_β))`; the reduction degenerates exactly on the
antidiagonal, the support of the Gram law. -/
theorem eigenPairProduct_reduction {α β : ℂ} (hα : |α.im| < 1) (hβ : |β.im| < 1)
    (hne : α - (starRingEnd ℂ) β ≠ 0) (x : ℝ) :
    hedenmalmCausalVolterra α x * (starRingEnd ℂ) (hedenmalmCausalVolterra β x) =
      I * (α - (starRingEnd ℂ) β)⁻¹ *
        (deriv (fun y : ℝ => hedenmalmCausalVolterra α y *
            (starRingEnd ℂ) (hedenmalmCausalVolterra β y)) x -
          I * (thetaCuspFullSource x : ℂ) *
            (hedenmalmCausalVolterra α x - (starRingEnd ℂ) (hedenmalmCausalVolterra β x))) := by
  rw [(hasDerivAt_eigenPairProduct hα hβ x).deriv]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem antidiagonal_iff {α β : ℂ} : α - (starRingEnd ℂ) β = 0 ↔ β = (starRingEnd ℂ) α := by
  constructor
  · intro h
    have : α = (starRingEnd ℂ) β := sub_eq_zero.1 h
    rw [this, Complex.conj_conj]
  · intro h
    rw [h, Complex.conj_conj, sub_self]

end

end RHTower
