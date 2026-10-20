import GaloisForLFunctions.ArithmeticCriticalityTheory.ReflectedPrimeMassAsymptotics
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThetaConvolutionFoldedInfinityFailure

/-!
# The cosh-moment law of folded failure

Let `φ ∈ C²_c` be odd with theta convolution `M = Φ ∗ φ ≥ 0` on `(0, ∞)`. The folded defect of the
convolution gauge is `Φ(x)[B_φ sinh(x/2) − 2 C_φ(x)]` (`foldedDefect_convGauge`), the two-sided source
`B_φ sinh(x/2)` is exact and the collar `C_φ` is evaluated at infinity by the prime number theorem
(`tendsto_exp_neg_half_mul_reflectedPrimeMass`). With `B_φ/2 = 2 ∫_0^∞ M sinh(r/2)` and
`e^{r/2} − sinh(r/2) = cosh(r/2)`:

    (𝓛_N ω_φ − Φ cosh(x/2) ω_φ)(x) / (Φ(x) e^{x/2})  →  −2 ∫_0^∞ M(r) cosh(r/2) dr
    (`tendsto_foldedDefect_convGauge_div`).

The folding converts the odd profile's failure at infinity into its half-line **cosh moment**, the
even-pole quantity: the sinh (odd-pole) parts of source and collar cancel to leading order, and what
remains is the full `e^{±r/2}` average. Every positive profile fails by exactly this amount; for the
shifted ground states it is `−(sinh(a/2) + 2 ∫_0^∞ e^{−r/2} m_a)`, the form `1 − R(a)` of the collar ratio.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- Super-exponential decay of a theta convolution against a continuous compactly supported `ψ`. -/
theorem exists_abs_thetaConv_le_of_continuous {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |thetaConv ψ y| ≤ C * Real.exp (-(24 * |y|)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hψc
  have hψi : Integrable fun b => |ψ b| := (hψ.integrable_of_hasCompactSupport hψc).abs
  refine ⟨C₀ * Real.exp (24 * R) * ∫ b, |ψ b|,
    mul_nonneg (by positivity) (integral_nonneg fun b => abs_nonneg _), fun y => ?_⟩
  unfold thetaConv
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hψi.const_mul (C₀ * Real.exp (24 * R) *
    Real.exp (-(24 * |y|)))) (Eventually.of_forall fun b => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
    by_cases hb : |b| ≤ R
    · have h1 := hC (y - b)
      have h2 := exp_neg_mul_abs_sub_le 24 y b (by norm_num)
      have h3 : Real.exp (24 * |b|) ≤ Real.exp (24 * R) := Real.exp_le_exp.mpr (by linarith)
      have : riemannKernelReal (y - b) ≤ C₀ * Real.exp (24 * R) * Real.exp (-(24 * |y|)) := by
        refine h1.trans ?_
        calc C₀ * Real.exp (-(24 * |y - b|)) ≤ C₀ * (Real.exp (24 * |b|) * Real.exp (-(24 * |y|))) :=
              mul_le_mul_of_nonneg_left h2 hC₀
          _ ≤ C₀ * (Real.exp (24 * R) * Real.exp (-(24 * |y|))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) hC₀
          _ = _ := by ring
      nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg (ψ b))]
    · rw [hsupp b (not_le.mp hb)]
      simp
  · rw [integral_const_mul]
    ring

/-- `(Φ ∗ φ)' = Φ ∗ φ'`. -/
theorem hasDerivAt_thetaConv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (x : ℝ) : HasDerivAt (thetaConv φ) (thetaConv (deriv φ) x) x := by
  have h := hφc.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ
    integrable_riemannKernelReal.locallyIntegrable x
  rw [← thetaConv_eq_convolution, ← thetaConv_eq_convolution] at h
  exact h

section CoshMoment

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
  (hodd : ∀ b, φ (-b) = -φ b) (hnn : ∀ y, 0 < y → 0 ≤ thetaConv φ y)
include hφ hφc

/-- Decay of `M = Φ ∗ φ` and `M'` on the half line. -/
theorem exists_thetaConv_decay :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ r, 0 ≤ r → |thetaConv φ r| ≤ C * Real.exp (-(2 * r))) ∧
      ∀ r, 0 ≤ r → |deriv (thetaConv φ) r| ≤ C * Real.exp (-(2 * r)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_thetaConv_le_of_continuous hφ.continuous hφc
  have hd1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_abs_thetaConv_le_of_continuous (hφ.continuous_deriv (by norm_num))
    (hφc.deriv)
  refine ⟨C₁ + C₂, by positivity, fun r hr => ?_, fun r hr => ?_⟩
  · have he : Real.exp (-(24 * |r|)) ≤ Real.exp (-(2 * r)) :=
      Real.exp_le_exp.mpr (by rw [abs_of_nonneg hr]; linarith)
    nlinarith [h₁ r, mul_le_mul_of_nonneg_left he hC₁, mul_nonneg hC₂ (Real.exp_pos (-(2 * r))).le]
  · rw [(hasDerivAt_thetaConv hd1 hφc r).deriv]
    have he : Real.exp (-(24 * |r|)) ≤ Real.exp (-(2 * r)) :=
      Real.exp_le_exp.mpr (by rw [abs_of_nonneg hr]; linarith)
    nlinarith [h₂ r, mul_le_mul_of_nonneg_left he hC₂, mul_nonneg hC₁ (Real.exp_pos (-(2 * r))).le]

include hodd hnn

omit hφ hφc in
theorem max_thetaConv_eq_ite (y : ℝ) :
    max (thetaConv φ y) 0 = if 0 < y then thetaConv φ y else 0 := by
  split_ifs with hy
  · exact max_eq_left (hnn y hy)
  · refine max_eq_right ?_
    rcases eq_or_lt_of_le (not_lt.mp hy) with h0 | hneg
    · have := thetaConv_neg_of_odd hodd 0
      rw [neg_zero] at this
      rw [h0]
      linarith
    · have h := hnn (-y) (by linarith)
      rw [thetaConv_neg_of_odd hodd] at h
      linarith

omit hodd hnn in
theorem integrable_thetaConv : Integrable (thetaConv φ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le_of_continuous hφ.continuous hφc
  refine ((integrable_exp_neg_eight_mul_abs.const_mul C)).mono'
    (contDiff_thetaConv hφ hφc).continuous.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact (hC y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    linarith [abs_nonneg y])) hC0)

/-- The archimedean collar of an odd convolution gauge is bounded: `≤ ω(x) ∫ |M|`. -/
theorem archConvCollar_le {x : ℝ} (hx : 0 < x) :
    0 ≤ (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0) ∧
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0) ≤
        archLevyDensity x * ∫ y, |thetaConv φ y| := by
  have hint := integrableOn_archLevy_max_thetaConv hφ hφc hodd hnn hx
  have hMi := integrable_thetaConv hφ hφc
  have hmaj : IntegrableOn (fun t => archLevyDensity x * |thetaConv φ (t - x)|) (Ioi 0) :=
    ((hMi.abs.comp_sub_right x).const_mul _).integrableOn
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _), ?_⟩
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0)
      ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity x * |thetaConv φ (t - x)| := by
        refine setIntegral_mono_on hint hmaj measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        rw [max_thetaConv_eq_ite hodd hnn]
        split_ifs with htx
        · have hle : archLevyDensity t ≤ archLevyDensity x :=
            strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hx) (mem_Ioi.mpr ht0) (by linarith)
          exact mul_le_mul hle (le_abs_self _) (hnn _ htx) (archLevyDensity_pos hx).le
        · rw [mul_zero]
          exact mul_nonneg (archLevyDensity_pos hx).le (abs_nonneg _)
    _ ≤ archLevyDensity x * ∫ y, |thetaConv φ y| := by
        rw [integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (archLevyDensity_pos hx).le
        calc (∫ t in Ioi (0 : ℝ), |thetaConv φ (t - x)|) ≤ ∫ t, |thetaConv φ (t - x)| :=
              setIntegral_le_integral (hMi.abs.comp_sub_right x)
                (Eventually.of_forall fun t => abs_nonneg _)
          _ = ∫ y, |thetaConv φ y| := integral_sub_right_eq_self (fun y => |thetaConv φ y|) x

/-- **The collar of an odd convolution gauge at infinity.** `e^{−x/2} C_φ(x) → ∫_0^∞ e^{r/2} M`. -/
theorem tendsto_exp_neg_half_mul_convCollarMass :
    Tendsto (fun x => Real.exp (-x / 2) * convCollarMass φ x) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * thetaConv φ r)) := by
  obtain ⟨C, hC0, hdec, hdec'⟩ := exists_thetaConv_decay hφ hφc
  have hM0 : thetaConv φ 0 = 0 := by
    have := thetaConv_neg_of_odd hodd 0
    rw [neg_zero] at this
    linarith
  have hprime := tendsto_exp_neg_half_mul_reflectedPrimeMass
    ((contDiff_thetaConv hφ hφc).of_le (by norm_num)) hM0 hC0 hdec hdec'
  have hI : 0 ≤ ∫ y, |thetaConv φ y| := integral_nonneg fun y => abs_nonneg _
  have harch : Tendsto (fun x => Real.exp (-x / 2) *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (thetaConv φ (t - x)) 0) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-x / 2) * (archLevyDensity 1 *
        ∫ y, |thetaConv φ y|)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).mul_const
        (archLevyDensity 1 * ∫ y, |thetaConv φ y|)
      simpa [Function.comp_def, neg_div] using this
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg (Real.exp_pos _).le (archConvCollar_le hφ hφc hodd hnn hx).1
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hb := (archConvCollar_le hφ hφc hodd hnn (by linarith : (0 : ℝ) < x)).2
      have hω : archLevyDensity x ≤ archLevyDensity 1 :=
        strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr (by linarith)) hx
      refine mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right hω hI
  have hsum := harch.add hprime
  rw [zero_add] at hsum
  refine hsum.congr fun x => ?_
  unfold convCollarMass
  rw [mul_add]
  congr 2
  refine tsum_congr fun n => ?_
  rw [max_thetaConv_eq_ite hodd hnn]
  by_cases h : x < Real.log n
  · rw [if_pos h, if_pos (sub_pos.mpr h)]
  · rw [if_neg h, if_neg (by rwa [sub_pos])]

/-- **The cosh-moment law.** `(𝓛_N ω_φ − Φ cosh(x/2) ω_φ)(x)/(Φ(x) e^{x/2}) → −2 ∫_0^∞ M(r) cosh(r/2) dr`. -/
theorem tendsto_foldedDefect_convGauge_div :
    Tendsto (fun x => (foldedGenerator (convGauge φ) x -
        riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x) /
        (riemannKernelReal x * Real.exp (x / 2))) atTop
      (𝓝 (-2 * ∫ r in Ioi (0 : ℝ), thetaConv φ r * Real.cosh (r / 2))) := by
  have hC := tendsto_exp_neg_half_mul_convCollarMass hφ hφc hodd hnn
  have hsh : Tendsto (fun x : ℝ => Real.exp (-x / 2) * Real.sinh (x / 2)) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      ((tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero).div_const 2)
    rw [sub_zero] at h1
    refine h1.congr fun x => ?_
    rw [Real.sinh_eq]
    have e1 : Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have e2 : Real.exp (-x / 2) * Real.exp (-(x / 2)) = Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (-1 / 2) * e1 + (1 / 2) * e2
  have hlim := (hsh.const_mul (convSinhCoefficient φ)).sub (hC.const_mul 2)
  -- the value
  obtain ⟨C₁, hC₁, hdec, -⟩ := exists_thetaConv_decay hφ hφc
  have hMi := integrable_thetaConv hφ hφc
  have hMs : Integrable fun r => thetaConv φ r * Real.sinh (r / 2) := by
    obtain ⟨C, hC0, hCb⟩ := exists_abs_thetaConv_le_of_continuous hφ.continuous hφc
    refine (integrable_exp_neg_eight_mul_abs.const_mul C).mono'
      ((contDiff_thetaConv hφ hφc).continuous.mul (Real.continuous_sinh.comp
        (continuous_id.div_const 2))).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hs : |Real.sinh (r / 2)| ≤ Real.exp (8 * |r|) :=
      (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight r)
    have he : Real.exp (-(24 * |r|)) * Real.exp (8 * |r|) ≤ Real.exp (-(8 * |r|)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [abs_nonneg r])
    calc |thetaConv φ r| * |Real.sinh (r / 2)| ≤ (C * Real.exp (-(24 * |r|))) * Real.exp (8 * |r|) :=
          mul_le_mul (hCb r) hs (abs_nonneg _) (by positivity)
      _ = C * (Real.exp (-(24 * |r|)) * Real.exp (8 * |r|)) := by ring
      _ ≤ C * Real.exp (-(8 * |r|)) := mul_le_mul_of_nonneg_left he hC0
  have hEi : IntegrableOn (fun r => Real.exp (r / 2) * thetaConv φ r) (Ioi 0) :=
    integrableOn_exp_half_mul hdec (contDiff_thetaConv hφ hφc).continuous
  have hsinhIoi : (∫ r in Ioi (0 : ℝ), thetaConv φ r * Real.sinh (r / 2)) =
      convSinhCoefficient φ / 4 := by
    rw [integral_Ioi_eq_half_of_even hMs (fun r => by
      rw [thetaConv_neg_of_odd hodd, show -r / 2 = -(r / 2) by ring, Real.sinh_neg]; ring),
      integral_thetaConv_mul_sinh_half hφ hφc]
    ring
  have hval : convSinhCoefficient φ * (1 / 2) - 2 * ∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * thetaConv φ r
      = -2 * ∫ r in Ioi (0 : ℝ), thetaConv φ r * Real.cosh (r / 2) := by
    have e : (fun r => thetaConv φ r * Real.cosh (r / 2)) =
        fun r => Real.exp (r / 2) * thetaConv φ r - thetaConv φ r * Real.sinh (r / 2) :=
      funext fun r => by rw [Real.cosh_eq, Real.sinh_eq]; ring
    rw [e, integral_sub hEi hMs.integrableOn, hsinhIoi]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [foldedDefect_convGauge hφ hφc hodd hnn hx]
  have hΦ := (riemannKernelReal_pos x).ne'
  have he : Real.exp (x / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hee : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [hee]
  field_simp

omit hodd in
/-- The half-line cosh moment of a nonzero positive profile is positive, so the limit of the
cosh-moment law is negative. -/
theorem integral_Ioi_thetaConv_mul_cosh_pos {x₀ : ℝ} (hx₀ : 0 < x₀) (hM : 0 < thetaConv φ x₀) :
    0 < ∫ r in Ioi (0 : ℝ), thetaConv φ r * Real.cosh (r / 2) := by
  have hc : Continuous fun r => thetaConv φ r * Real.cosh (r / 2) :=
    (contDiff_thetaConv hφ hφc).continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  obtain ⟨C, hC0, hCb⟩ := exists_abs_thetaConv_le_of_continuous hφ.continuous hφc
  have hi : IntegrableOn (fun r => thetaConv φ r * Real.cosh (r / 2)) (Ioi 0) := by
    refine ((integrable_exp_neg_eight_mul_abs.const_mul C).integrableOn).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _)]
    have hs : Real.cosh (r / 2) ≤ Real.exp (8 * |r|) :=
      (cosh_le_exp_abs _).trans (exp_abs_half_le_exp_eight r)
    have he : Real.exp (-(24 * |r|)) * Real.exp (8 * |r|) ≤ Real.exp (-(8 * |r|)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [abs_nonneg r])
    calc |thetaConv φ r| * Real.cosh (r / 2) ≤ (C * Real.exp (-(24 * |r|))) * Real.exp (8 * |r|) :=
          mul_le_mul (hCb r) hs (Real.cosh_pos _).le (by positivity)
      _ = C * (Real.exp (-(24 * |r|)) * Real.exp (8 * |r|)) := by ring
      _ ≤ C * Real.exp (-(8 * |r|)) := mul_le_mul_of_nonneg_left he hC0
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi
    fun r hr => mul_nonneg (hnn r hr) (Real.cosh_pos _).le) hi]
  have hopen : IsOpen (Function.support (fun r => thetaConv φ r * Real.cosh (r / 2)) ∩ Ioi 0) :=
    (isOpen_ne_fun hc continuous_const).inter isOpen_Ioi
  exact hopen.measure_pos volume ⟨x₀, (mul_pos hM (Real.cosh_pos _)).ne', hx₀⟩

end CoshMoment

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
