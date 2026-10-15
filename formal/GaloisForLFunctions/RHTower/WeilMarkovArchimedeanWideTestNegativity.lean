import GaloisForLFunctions.RHTower.WeilMarkovFarOutNonnegativeOddPositivity
import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# The archimedean form is negative on wide tests

The archimedean symbol of the Weil form is `Ω(r) = Re ψ(¼ + ir/2) − log π = 2θ′(r)`, and the
Lévy–Khintchine representation gives `θ′(r) − θ′(0) = ∫_0^∞ ω(x)(1 − cos(rx)) dx` with the Lévy
density `ω(x) = e^{−x/2}/(1 − e^{−2x})`. Since `1 − cos(rx) ≤ r²x²/2`, the symbol is bounded by its
central value plus a quadratic term,
`Ω(r) ≤ Ω(0) + m₂ r²`, `m₂ = ∫_0^∞ x² ω(x) dx ≤ 18`
(`gammaBracket_le_quadratic`, `levySecondMoment_le`). Plancherel then bounds the archimedean form of
a real `C²` compactly supported test `g` by
`A(g) ≤ 2θ′(0) ‖g‖² + m₂ · (1/2π) ∫ r² |ĝ(r)|² dr`
(`archForm_le`). The central value `2θ′(0) = ψ(¼) − log π` is negative, so the archimedean form is
negative on every wide test, i.e. on every test whose Fourier `H¹` seminorm is a small multiple of
its `L²` norm (`exists_wide_archForm_le`).

Consequences for the archimedean-minus-prime form `M = A − P`: on nonnegative wide tests the ratio
pairing `P` is nonnegative, so `M(g) ≤ θ′(0) ‖g‖² < 0` (`exists_wide_nonneg_markovEnergy_le`). The
single negative square of `M` therefore does not arise as "positive archimedean form minus a small
prime perturbation": the archimedean form itself is negative on an infinite-dimensional set of
tests, and the positivity of the odd sector on wide nonnegative half-line tests is carried entirely
by the product-prime pairing and the trivial-zero squares, which under the Riemann hypothesis must
exceed `−θ′(0) ‖g‖²` (`wide_nonneg_productPairing_ge_of_riemannHypothesis`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

variable {g : ℝ → ℝ}

/-! ## The second moment of the Lévy density -/

/-- `m₂ = ∫_0^∞ x² ω(x) dx`. -/
def levySecondMoment : ℝ := ∫ x in Ioi (0 : ℝ), x ^ 2 * archLevyDensity x

theorem one_sub_exp_neg_two_mul_ge {x : ℝ} (hx : 0 < x) :
    2 * x / (1 + 2 * x) ≤ 1 - Real.exp (-2 * x) := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have h2 : Real.exp (-2 * x) ≤ 1 / (1 + 2 * x) := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  have h3 : 2 * x / (1 + 2 * x) = 1 - 1 / (1 + 2 * x) := by
    field_simp
    ring
  linarith

/-- `x² ω(x) ≤ x² e^{−x/2} + (x/2) e^{−x/2}` on `(0, ∞)`. -/
theorem sq_mul_archLevyDensity_le {x : ℝ} (hx : 0 < x) :
    x ^ 2 * archLevyDensity x ≤
      x ^ 2 * Real.exp (-(1 / 2 * x)) + x * Real.exp (-(1 / 2 * x)) / 2 := by
  unfold archLevyDensity
  have hden := one_sub_exp_neg_two_mul_ge hx
  have hden_pos : 0 < 2 * x / (1 + 2 * x) := by positivity
  have hexp : Real.exp (-x / 2) = Real.exp (-(1 / 2 * x)) := by congr 1; ring
  rw [hexp]
  have h1 : Real.exp (-(1 / 2 * x)) / (1 - Real.exp (-2 * x)) ≤
      Real.exp (-(1 / 2 * x)) / (2 * x / (1 + 2 * x)) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hden_pos hden
  have h2 : Real.exp (-(1 / 2 * x)) / (2 * x / (1 + 2 * x)) =
      Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x) := by
    field_simp
  calc x ^ 2 * (Real.exp (-(1 / 2 * x)) / (1 - Real.exp (-2 * x)))
      ≤ x ^ 2 * (Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = x ^ 2 * Real.exp (-(1 / 2 * x)) + x * Real.exp (-(1 / 2 * x)) / 2 := by
        field_simp; ring

/-- `∫_0^∞ x² e^{−x/2} dx = 16`. -/
theorem integral_sq_mul_exp_neg_half_Ioi :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-(1 / 2 * x)) = 16 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1 / 2) (by norm_num) (by norm_num)
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hpow : ((1 : ℝ) / (1 / 2)) ^ (3 : ℝ) = 8 := by
    rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  have hfun : (fun t : ℝ => t ^ ((3 : ℝ) - 1) * Real.exp (-(1 / 2 * t))) =
      fun t => t ^ 2 * Real.exp (-(1 / 2 * t)) := by
    funext t; rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  rw [hfun, h3, hpow] at h
  linarith

/-- `∫_0^∞ x e^{−x/2} dx = 4`. -/
theorem integral_mul_exp_neg_half_Ioi :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / 2 * x)) = 4 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / 2) (by norm_num) (by norm_num)
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hpow : ((1 : ℝ) / (1 / 2)) ^ (2 : ℝ) = 4 := by
    rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, Real.rpow_two]
    norm_num
  have hfun : (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-(1 / 2 * t))) =
      fun t => t * Real.exp (-(1 / 2 * t)) := by
    funext t; rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  rw [hfun, h2, hpow] at h
  linarith

theorem integrableOn_sq_mul_exp_neg_half :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(1 / 2 * x))) (Ioi 0) := by
  have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((3 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hG2 : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ 2) (Ioi 0) :=
    IntegrableOn.congr_fun hG (fun y _ => by
      show Real.exp (-y) * y ^ ((3 : ℝ) - 1) = Real.exp (-y) * y ^ 2
      rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]) measurableSet_Ioi
  have hs : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 * x)) * (1 / 2 * x) ^ 2) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y) * y ^ 2) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by simpa using hG2)
    exact this
  refine IntegrableOn.congr_fun (hs.const_mul 4) (fun x _ => ?_) measurableSet_Ioi
  show 4 * (Real.exp (-(1 / 2 * x)) * (1 / 2 * x) ^ 2) = x ^ 2 * Real.exp (-(1 / 2 * x))
  ring

theorem integrableOn_mul_exp_neg_half :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(1 / 2 * x))) (Ioi 0) := by
  have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((2 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hG2 : IntegrableOn (fun y : ℝ => Real.exp (-y) * y) (Ioi 0) :=
    IntegrableOn.congr_fun hG (fun y _ => by
      show Real.exp (-y) * y ^ ((2 : ℝ) - 1) = Real.exp (-y) * y
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]) measurableSet_Ioi
  have hs : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 * x)) * (1 / 2 * x)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y) * y) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by simpa using hG2)
    exact this
  refine IntegrableOn.congr_fun (hs.const_mul 2) (fun x _ => ?_) measurableSet_Ioi
  show 2 * (Real.exp (-(1 / 2 * x)) * (1 / 2 * x)) = x * Real.exp (-(1 / 2 * x))
  ring

theorem integrableOn_sq_mul_archLevyDensity :
    IntegrableOn (fun x : ℝ => x ^ 2 * archLevyDensity x) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(1 / 2 * x)) +
      x * Real.exp (-(1 / 2 * x)) / 2) (Ioi 0) :=
    integrableOn_sq_mul_exp_neg_half.add (integrableOn_mul_exp_neg_half.div_const 2)
  refine hdom.mono' ?_ ?_
  · exact ((measurable_id.pow_const 2).mul measurable_archLevyDensity).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (archLevyDensity_pos hx).le)]
    exact sq_mul_archLevyDensity_le hx

theorem levySecondMoment_le : levySecondMoment ≤ 18 := by
  unfold levySecondMoment
  have hdom : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(1 / 2 * x)) +
      x * Real.exp (-(1 / 2 * x)) / 2) (Ioi 0) :=
    integrableOn_sq_mul_exp_neg_half.add (integrableOn_mul_exp_neg_half.div_const 2)
  have hmono : ∫ x in Ioi (0 : ℝ), x ^ 2 * archLevyDensity x ≤
      ∫ x in Ioi (0 : ℝ), (x ^ 2 * Real.exp (-(1 / 2 * x)) + x * Real.exp (-(1 / 2 * x)) / 2) :=
    setIntegral_mono_on integrableOn_sq_mul_archLevyDensity hdom measurableSet_Ioi
      fun x hx => sq_mul_archLevyDensity_le hx
  rw [integral_add integrableOn_sq_mul_exp_neg_half (integrableOn_mul_exp_neg_half.div_const 2),
    integral_div, integral_sq_mul_exp_neg_half_Ioi, integral_mul_exp_neg_half_Ioi] at hmono
  linarith

theorem levySecondMoment_nonneg : 0 ≤ levySecondMoment :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx =>
    mul_nonneg (sq_nonneg _) (archLevyDensity_pos hx).le

/-! ## The quadratic symbol bound -/

/-- **The archimedean symbol is at most its central value plus `m₂ r²`.** -/
theorem gammaBracket_le_quadratic (r : ℝ) :
    EF.gammaBracket r ≤ EF.gammaBracket 0 + levySecondMoment * r ^ 2 := by
  rw [WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  have h := gammaHardyPhaseRate_sub_zero_eq_integral r
  have hint1 := integrableOn_archLevyDensity_mul_one_sub_cos r
  have hint2 : IntegrableOn (fun x : ℝ => r ^ 2 / 2 * (x ^ 2 * archLevyDensity x)) (Ioi 0) :=
    integrableOn_sq_mul_archLevyDensity.const_mul _
  have hmono : ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (r * x)) ≤
      ∫ x in Ioi (0 : ℝ), r ^ 2 / 2 * (x ^ 2 * archLevyDensity x) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun x hx => ?_
    have hc := Real.one_sub_sq_div_two_le_cos (x := r * x)
    have hω := (archLevyDensity_pos hx).le
    calc archLevyDensity x * (1 - Real.cos (r * x))
        ≤ archLevyDensity x * ((r * x) ^ 2 / 2) := mul_le_mul_of_nonneg_left (by linarith) hω
      _ = r ^ 2 / 2 * (x ^ 2 * archLevyDensity x) := by ring
  rw [integral_const_mul] at hmono
  unfold levySecondMoment
  nlinarith [hmono, h]

/-! ## The archimedean form of a test -/

/-- The Fourier `H¹` seminorm `(1/2π) ∫ r² |ĝ(r)|² dr` of a real test. -/
def fourierH1 (g : ℝ → ℝ) : ℝ :=
  1 / (2 * π) * ∫ r : ℝ, r ^ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2

/-- Uniform decay of the transform of a real `C²` compactly supported test: there is `N` with
`‖ĝ(r)‖² ≤ N²/((1 + |r|)²)²`. -/
theorem exists_normSq_paperFT_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ r : ℝ,
      ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 ≤ N ^ 2 / ((1 + |r|) ^ 2) ^ 2 := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hG2 : ContDiff ℝ 2 G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  obtain ⟨a, ha⟩ := hGc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hsupp : ∀ u, G u ≠ 0 → |u| ≤ a := by
    intro u hu
    have h1 : u ∈ tsupport G := subset_tsupport G hu
    have h2 := ha h1
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
  refine ⟨4 * ((∫ u, ‖G u‖) + ∫ u, ‖deriv (deriv G) u‖), ?_, fun r => ?_⟩
  · have h1 : 0 ≤ ∫ u, ‖G u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv G) u‖ := integral_nonneg fun u => norm_nonneg _
    positivity
  · have h := norm_paperFT_le_decay hG2 hsupp (r : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.ofReal_re] at h
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem sq_div_pow_four_le {r : ℝ} : r ^ 2 / ((1 + |r|) ^ 2) ^ 2 ≤ (1 + r ^ 2)⁻¹ := by
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h0 := abs_nonneg r
  have h1 : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  rw [h1]
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]

theorem one_div_pow_four_le {r : ℝ} : 1 / ((1 + |r|) ^ 2) ^ 2 ≤ (1 + r ^ 2)⁻¹ := by
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  have h0 := abs_nonneg r
  have h1 : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  rw [h1]
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]

theorem integrable_normSq_paperFT_ofReal (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable fun r : ℝ => ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 := by
  obtain ⟨N, -, hN⟩ := exists_normSq_paperFT_le hg hgc
  have hGi : Integrable fun u => (g u : ℂ) :=
    (Complex.continuous_ofReal.comp hg.continuous).integrable_of_hasCompactSupport
      (hgc.comp_left Complex.ofReal_zero)
  refine (integrable_inv_one_add_sq.const_mul (N ^ 2)).mono' ?_ (Eventually.of_forall fun r => ?_)
  · exact ((continuous_paperFT_real_of_integrable hGi).norm.pow 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 ≤ N ^ 2 / ((1 + |r|) ^ 2) ^ 2 := hN r
      _ = N ^ 2 * (1 / ((1 + |r|) ^ 2) ^ 2) := by ring
      _ ≤ N ^ 2 * (1 + r ^ 2)⁻¹ := mul_le_mul_of_nonneg_left one_div_pow_four_le (sq_nonneg _)

theorem integrable_sq_mul_normSq_paperFT (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable fun r : ℝ => r ^ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 := by
  obtain ⟨N, -, hN⟩ := exists_normSq_paperFT_le hg hgc
  have hGi : Integrable fun u => (g u : ℂ) :=
    (Complex.continuous_ofReal.comp hg.continuous).integrable_of_hasCompactSupport
      (hgc.comp_left Complex.ofReal_zero)
  refine (integrable_inv_one_add_sq.const_mul (N ^ 2)).mono' ?_ (Eventually.of_forall fun r => ?_)
  · exact ((continuous_id.pow 2).mul
      ((continuous_paperFT_real_of_integrable hGi).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r ^ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 ≤ r ^ 2 * (N ^ 2 / ((1 + |r|) ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (hN r) (sq_nonneg _)
      _ = N ^ 2 * (r ^ 2 / ((1 + |r|) ^ 2) ^ 2) := by ring
      _ ≤ N ^ 2 * (1 + r ^ 2)⁻¹ := mul_le_mul_of_nonneg_left sq_div_pow_four_le (sq_nonneg _)

theorem fourierH1_nonneg (g : ℝ → ℝ) : 0 ≤ fourierH1 g := by
  unfold fourierH1
  exact mul_nonneg (by positivity) (integral_nonneg fun r => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **The archimedean form is bounded by its central value plus `m₂` times the Fourier `H¹`
seminorm:** `A(g) ≤ 2θ′(0) ‖g‖² + m₂ · (1/2π) ∫ r² |ĝ|²`. -/
theorem archForm_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    archForm g ≤ 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levySecondMoment * fourierH1 g := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hG2 : ContDiff ℝ 2 G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  obtain ⟨a, ha⟩ := hGc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at ha
  have hplanch := integral_norm_paperFT_sq hG2 ha
  have hGsq : ∫ x, ‖G x‖ ^ 2 = ∫ u, g u ^ 2 := by
    congr 1
    funext x
    simp only [hG, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 := integrable_normSq_paperFT_ofReal hg hgc
  have h2 := integrable_sq_mul_normSq_paperFT hg hgc
  have hint1 := integrable_normSq_paperFT_mul_gammaBracket hg hgc
  have hint2 : Integrable fun r : ℝ =>
      ‖paperFT G (r : ℂ)‖ ^ 2 * (EF.gammaBracket 0 + levySecondMoment * r ^ 2) := by
    refine ((h1.const_mul (EF.gammaBracket 0)).add (h2.const_mul levySecondMoment)).congr
      (Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply]
    ring
  have hmono : ∫ r : ℝ, ‖paperFT G (r : ℂ)‖ ^ 2 * EF.gammaBracket r ≤
      ∫ r : ℝ, ‖paperFT G (r : ℂ)‖ ^ 2 * (EF.gammaBracket 0 + levySecondMoment * r ^ 2) :=
    integral_mono hint1 hint2 fun r =>
      mul_le_mul_of_nonneg_left (gammaBracket_le_quadratic r) (sq_nonneg _)
  have hsplit : ∫ r : ℝ, ‖paperFT G (r : ℂ)‖ ^ 2 * (EF.gammaBracket 0 + levySecondMoment * r ^ 2) =
      EF.gammaBracket 0 * (∫ r : ℝ, ‖paperFT G (r : ℂ)‖ ^ 2) +
        levySecondMoment * ∫ r : ℝ, r ^ 2 * ‖paperFT G (r : ℂ)‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1
    funext r
    ring
  unfold archForm fourierH1
  calc 1 / (2 * π) * ∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r
      ≤ 1 / (2 * π) * ∫ r : ℝ, ‖paperFT G (r : ℂ)‖ ^ 2 *
          (EF.gammaBracket 0 + levySecondMoment * r ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) +
        levySecondMoment * (1 / (2 * π) * ∫ r : ℝ, r ^ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2) := by
        rw [hsplit, hplanch, hGsq, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
        have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

/-- **Wide tests have negative archimedean form.** There is `κ > 0` such that every real `C²`
compactly supported test whose Fourier `H¹` seminorm is at most `κ ‖g‖²` satisfies
`A(g) ≤ θ′(0) ‖g‖²`, and `θ′(0) < 0`. -/
theorem exists_wide_archForm_le :
    ∃ κ : ℝ, 0 < κ ∧ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      fourierH1 g ≤ κ * ∫ u, g u ^ 2 → archForm g ≤ gammaHardyPhaseRate 0 * ∫ u, g u ^ 2 := by
  have hθ := gammaHardyPhaseRate_zero_neg
  have hm := levySecondMoment_nonneg
  refine ⟨-gammaHardyPhaseRate 0 / (levySecondMoment + 1),
    div_pos (neg_pos.mpr hθ) (by linarith), ?_⟩
  intro g hg hgc hH
  have hA := archForm_le hg hgc
  have hN0 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h1 : levySecondMoment * fourierH1 g ≤
      levySecondMoment * (-gammaHardyPhaseRate 0 / (levySecondMoment + 1) * ∫ u, g u ^ 2) :=
    mul_le_mul_of_nonneg_left hH hm
  have h2 : levySecondMoment * (-gammaHardyPhaseRate 0 / (levySecondMoment + 1) * ∫ u, g u ^ 2) ≤
      -gammaHardyPhaseRate 0 * ∫ u, g u ^ 2 := by
    have hfrac : levySecondMoment / (levySecondMoment + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have heq : levySecondMoment * (-gammaHardyPhaseRate 0 / (levySecondMoment + 1) * ∫ u, g u ^ 2)
        = levySecondMoment / (levySecondMoment + 1) * (-gammaHardyPhaseRate 0 * ∫ u, g u ^ 2) := by
      have hne : levySecondMoment + 1 ≠ 0 := by linarith
      field_simp
    rw [heq]
    exact mul_le_of_le_one_left (mul_nonneg (by linarith) hN0) hfrac
  linarith

/-! ## Consequences for the archimedean-minus-prime form -/

theorem primeSum_nonneg (hpos : ∀ x, 0 ≤ g x) : 0 ≤ primeSum g := by
  unfold primeSum
  refine tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg' n) (add_nonneg ?_ ?_)
  · exact integral_nonneg fun t => mul_nonneg (hpos t) (hpos _)
  · exact integral_nonneg fun t => mul_nonneg (hpos t) (hpos _)

theorem markovEnergy_le_archForm_of_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hpos : ∀ x, 0 ≤ g x) : markovEnergy (fun x => (g x : ℂ)) ≤ archForm g := by
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hg hgc]
  linarith [primeSum_nonneg hpos]

/-- **Wide nonnegative tests have negative archimedean-minus-prime form:** `M(g) ≤ θ′(0) ‖g‖²`
whenever the Fourier `H¹` seminorm of `g ≥ 0` is at most `κ ‖g‖²`. -/
theorem exists_wide_nonneg_markovEnergy_le :
    ∃ κ : ℝ, 0 < κ ∧ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → (∀ x, 0 ≤ g x) →
      fourierH1 g ≤ κ * ∫ u, g u ^ 2 →
      markovEnergy (fun x => (g x : ℂ)) ≤ gammaHardyPhaseRate 0 * ∫ u, g u ^ 2 := by
  obtain ⟨κ, hκ, h⟩ := exists_wide_archForm_le
  exact ⟨κ, hκ, fun g hg hgc hpos hH =>
    (markovEnergy_le_archForm_of_nonneg hg hgc hpos).trans (h g hg hgc hH)⟩

/-- Under the Riemann hypothesis, the product-prime pairing and the trivial-zero squares of a wide
nonnegative half-line test carry at least `−θ′(0) ‖g‖²`: the positivity of the odd sector on such
tests is entirely arithmetic. -/
theorem wide_nonneg_productPairing_ge_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (g : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 g → HasCompactSupport g → 0 < ε →
      (∀ x, x < ε → g x = 0) → (∀ x, 0 ≤ g x) → fourierH1 g ≤ κ * ∫ u, g u ^ 2 →
      -gammaHardyPhaseRate 0 * ∫ u, g u ^ 2 ≤
        (∑' k : ℕ, trivialZeroMoment g k ^ 2) + productPrimePairing g := by
  obtain ⟨κ, hκ, h⟩ := exists_wide_nonneg_markovEnergy_le
  refine ⟨κ, hκ, fun g ε hg hgc hε hsupp hpos hH => ?_⟩
  have h1 := halfLine_markovEnergy_add_nonneg_of_riemannHypothesis hRH hg hgc hε hsupp
  have h2 := h g hg hgc hpos hH
  linarith

end

end RHTower
