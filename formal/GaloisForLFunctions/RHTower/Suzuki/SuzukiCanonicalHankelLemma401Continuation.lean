import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelOneSidedSupport
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOneSidedFourierLaplaceAnalytic

/-!
# Suzuki (2012), equation (4.01) in the upper half-plane

The boundary `L²` multiplier identity is insufficient for Suzuki's Lemma 4.3: the proof evaluates
both sides at complex spectral parameters.  This module proves the actual analytic identity.  It
first derives the equality on the absolute-convergence half-plane from the literal arithmetic
kernel, continues it by holomorphic uniqueness for compact-smooth data, and then uses
support-preserving density to reach every sharply supported `L²` source.

No boundary-value uniqueness assertion is assumed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform Convolution ENNReal

noncomputable section


namespace RHTower

/-! ## Literal high-line identity -/

/-- Exact high-line transform identity for Suzuki's literal logarithmic kernel. -/
theorem integral_exp_I_mul_suzukiLiteralLogHankel
    {omega : ℝ} (homega : 0 < omega)
    (g : DeningerMeyerStrongLogTarget) {z : ℂ}
    (hz : 1 / 2 + omega < z.im) :
    (∫ r : ℝ, Complex.exp (I * z * (r : ℂ)) *
        suzukiLiteralLogHankel omega g r) =
      suzukiCanonicalTheta omega z *
        ∫ t : ℝ, Complex.exp (-I * z * (t : ℂ)) * (g : ℝ → ℂ) t := by
  let c : ℝ := z.im
  let xi : ℝ := -z.re / (2 * Real.pi)
  have hc : 1 / 2 + omega < c := by simpa [c] using hz
  have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hleft :
      (∫ r : ℝ, Complex.exp (I * z * (r : ℂ)) *
          suzukiLiteralLogHankel omega g r) =
        FourierTransform.fourier
          (suzukiTiltedHankelConvolution omega c g) xi := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with r
    rw [suzukiLiteralLogHankel_eq_exp_mul_tiltedConvolution omega c g r]
    simp only [smul_eq_mul]
    have hxi : -2 * Real.pi * r * xi = z.re * r := by
      dsimp [xi]
      field_simp
    have hphase :
        Complex.exp (I * z * (r : ℂ)) * (Real.exp (c * r) : ℂ) =
          Complex.exp (((z.re * r : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> norm_num [c, Complex.mul_re, Complex.mul_im] <;> ring
    rw [← mul_assoc, hphase, ← hxi]
  rw [hleft, fourier_suzukiTiltedHankelConvolution homega hc]
  have hthetaArg :
      (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * I) = z := by
    apply Complex.ext
    · dsimp [xi, c]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        mul_zero, sub_zero]
      field_simp
      ring
    · simp [c]
  have hmellinArg :
      (c : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * I = -I * z := by
    apply Complex.ext
    · simp [c, Complex.mul_re]
    · dsimp [xi]
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, zero_add,
        neg_im, mul_im, I_re]
      field_simp
      norm_num
  rw [hthetaArg, hmellinArg, deningerMeyerStrongLogMellin]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul]

/-! ## Continuation on the compact-smooth core -/

/-- **Suzuki (2012), equation (4.01), compact-smooth analytic form.**  For a compact-smooth
source with logarithmic support in `(-∞,A]`, the literal equation holds at every point of the
strict upper half-plane for the actual canonical Hankel unitary. -/
theorem suzuki2012_equation_four_zero_one_on_compact_smooth_log_core
    {omega A : ℝ} (homega : 1 / 2 < omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g)
    (hg : ∀ t, A ≤ t → g t = 0) {z : ℂ} (hz : 0 < z.im) :
    suzukiLowerFourierLaplace (-A)
        (suzukiCanonicalLogHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
          (suzukiCompactSmoothLogL2 g hsmooth hcompact)) z =
      suzukiCanonicalTheta omega z *
        suzukiUpperFourierLaplace A
          (suzukiCompactSmoothLogL2 g hsmooth hcompact) z := by
  let hinner := suzukiCanonicalTheta_meromorphicInner_of_half_lt homega
  let q := suzukiCompactSmoothLogL2 g hsmooth hcompact
  let H := suzukiCanonicalLogHankelUnitary omega hinner
  let G := suzukiCompactSmoothStrongLogTarget g hsmooth hcompact
  let c : ℝ := 2 + omega
  have homega0 : 0 < omega := by linarith
  have hc : 1 / 2 + omega < c := by dsimp [c]; linarith
  have hqae : (q : ℝ → ℂ) =ᵐ[volume] g := by
    exact suzukiStrongLogL2_ae G hcompact
  have hHeq : H q =
      suzukiCompactSmoothLiteralLogHankelL2 omega c homega0 hc hinner
        g hsmooth hcompact := by
    exact suzukiCanonicalLogHankelUnitary_eq_literal_on_compact_smooth
      homega0 hc hinner g hsmooth hcompact
  have hHae : (H q : ℝ → ℂ) =ᵐ[volume]
      suzukiLiteralLogHankel omega G := by
    rw [hHeq]
    exact (memLp_two_suzukiLiteralLogHankel homega0 hc hinner G hcompact).coeFn_toLp
  have hsource (w : ℂ) :
      suzukiUpperFourierLaplace A q w =
        ∫ t : ℝ, Complex.exp (-I * w * (t : ℂ)) * g t := by
    unfold suzukiUpperFourierLaplace suzukiUpperFourierLaplaceIntegrand
    apply integral_congr_ae
    filter_upwards [hqae] with t ht
    by_cases htA : t ∈ Iic A
    · rw [indicator_of_mem htA, ht]
    · rw [indicator_of_notMem htA, hg t (le_of_lt (lt_of_not_ge htA))]
      simp
  have houtput (w : ℂ) :
      suzukiLowerFourierLaplace (-A) (H q) w =
        ∫ r : ℝ, Complex.exp (I * w * (r : ℂ)) *
          suzukiLiteralLogHankel omega G r := by
    rw [suzukiLowerFourierLaplace_eq_integral]
    apply integral_congr_ae
    filter_upwards [hHae] with r hr
    by_cases hrA : r ∈ Ici (-A)
    · rw [indicator_of_mem hrA, hr]
    · rw [indicator_of_notMem hrA,
        suzukiLiteralLogHankel_eq_zero_of_lt_neg_support G hg
          (lt_of_not_ge hrA)]
      simp
  let L : ℂ → ℂ := fun w => suzukiLowerFourierLaplace (-A) (H q) w
  let R : ℂ → ℂ := fun w => suzukiCanonicalTheta omega w *
    suzukiUpperFourierLaplace A q w
  have hL : AnalyticOnNhd ℂ L suzukiUpperHalfPlane :=
    analyticOnNhd_suzukiLowerFourierLaplace (-A) (H q)
  have htheta : AnalyticOnNhd ℂ (suzukiCanonicalTheta omega)
      suzukiUpperHalfPlane := by
    intro w hw
    exact hinner.2.1 w hw
  have hR : AnalyticOnNhd ℂ R suzukiUpperHalfPlane :=
    htheta.mul (analyticOnNhd_suzukiUpperFourierLaplace A q)
  let z₀ : ℂ := (omega + 1 : ℂ) * I
  have hz₀ : z₀ ∈ suzukiUpperHalfPlane := by
    change 0 < z₀.im
    simp [z₀]
    linarith
  have hhighOpen : IsOpen {w : ℂ | 1 / 2 + omega < w.im} :=
    isOpen_lt continuous_const (by fun_prop)
  have hz₀high : z₀ ∈ {w : ℂ | 1 / 2 + omega < w.im} := by
    change 1 / 2 + omega < z₀.im
    simp [z₀]
    norm_num
    linarith
  have hevent : L =ᶠ[𝓝 z₀] R := by
    filter_upwards [hhighOpen.eventually_mem hz₀high] with w hw
    dsimp only [L, R]
    rw [houtput, hsource]
    exact integral_exp_I_mul_suzukiLiteralLogHankel homega0 G hw
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    isPreconnected_suzukiUpperHalfPlane hz₀ hevent hz

/-! ## Extension to every supported `L²` source -/

/-- **Suzuki (2012), equation (4.01), exact upper-half-plane theorem.**  The equation holds for
every `L²` logarithmic source sharply supported in `(-∞,A]`.  This is the source-faithful analytic
continuation statement used in Lemma 4.3. -/
theorem suzuki2012_equation_four_zero_one
    {omega A : ℝ} (homega : 1 / 2 < omega)
    (q : SoninL2) (hq : logHalflineCutoff A q = q)
    {z : ℂ} (hz : 0 < z.im) :
    suzukiLowerFourierLaplace (-A)
        (suzukiCanonicalLogHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q) z =
      suzukiCanonicalTheta omega z *
        suzukiUpperFourierLaplace A q z := by
  let hinner := suzukiCanonicalTheta_meromorphicInner_of_half_lt homega
  let H := suzukiCanonicalLogHankelUnitary omega hinner
  let L := suzukiLowerFourierLaplaceCLM (-A) z hz
  let U := suzukiUpperFourierLaplaceCLM A z hz
  rw [suzukiLowerFourierLaplace_eq_CLM (-A) _ z hz,
    suzukiUpperFourierLaplace_eq_CLM A q z hz]
  apply eq_of_forall_dist_le
  intro ε hε
  let C : ℝ := ‖L‖ + ‖suzukiCanonicalTheta omega z‖ * ‖U‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  obtain ⟨g, hcompact, hsmooth, hg, hqg⟩ :=
    exists_suzukiOneSidedCompactSmoothL2_dist_lt hq
      (show 0 < ε / C by positivity)
  let v := suzukiOneSidedCompactSmoothL2 g hcompact hsmooth
  have hvEq : v = suzukiCompactSmoothLogL2 g hsmooth hcompact :=
    suzukiOneSidedCompactSmoothL2_eq_suzukiCompactSmoothLogL2
      g hcompact hsmooth
  have hcore : L (H v) = suzukiCanonicalTheta omega z * U v := by
    rw [hvEq]
    have h := suzuki2012_equation_four_zero_one_on_compact_smooth_log_core
      homega g hsmooth hcompact hg hz
    rw [suzukiLowerFourierLaplace_eq_CLM,
      suzukiUpperFourierLaplace_eq_CLM] at h
    exact h
  have hleft : dist (L (H q)) (L (H v)) ≤ ‖L‖ * dist q v := by
    calc
      dist (L (H q)) (L (H v)) ≤ ‖L‖ * dist (H q) (H v) :=
        L.dist_le_opNorm _ _
      _ = ‖L‖ * dist q v := by rw [H.dist_map]
  have hupper : dist (U v) (U q) ≤ ‖U‖ * dist q v := by
    simpa only [dist_comm] using U.dist_le_opNorm v q
  have hright :
      dist (suzukiCanonicalTheta omega z * U v)
          (suzukiCanonicalTheta omega z * U q) ≤
        (‖suzukiCanonicalTheta omega z‖ * ‖U‖) * dist q v := by
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    calc
      ‖suzukiCanonicalTheta omega z‖ * ‖U v - U q‖ =
          ‖suzukiCanonicalTheta omega z‖ * dist (U v) (U q) := by
            rw [dist_eq_norm]
      _ ≤ ‖suzukiCanonicalTheta omega z‖ * (‖U‖ * dist q v) := by
        gcongr
      _ = (‖suzukiCanonicalTheta omega z‖ * ‖U‖) * dist q v := by ring
  apply le_of_lt
  calc
    dist (L (H q)) (suzukiCanonicalTheta omega z * U q) ≤
        dist (L (H q)) (L (H v)) +
          dist (L (H v)) (suzukiCanonicalTheta omega z * U v) +
          dist (suzukiCanonicalTheta omega z * U v)
            (suzukiCanonicalTheta omega z * U q) := by
      calc
        dist (L (H q)) (suzukiCanonicalTheta omega z * U q) ≤
            dist (L (H q)) (L (H v)) +
              dist (L (H v)) (suzukiCanonicalTheta omega z * U q) :=
          dist_triangle _ _ _
        _ ≤ dist (L (H q)) (L (H v)) +
            (dist (L (H v)) (suzukiCanonicalTheta omega z * U v) +
              dist (suzukiCanonicalTheta omega z * U v)
                (suzukiCanonicalTheta omega z * U q)) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    _ = dist (L (H q)) (L (H v)) +
          dist (suzukiCanonicalTheta omega z * U v)
            (suzukiCanonicalTheta omega z * U q) := by rw [hcore, dist_self, add_zero]
    _ ≤ ‖L‖ * dist q v +
          (‖suzukiCanonicalTheta omega z‖ * ‖U‖) * dist q v :=
      add_le_add hleft hright
    _ = (‖L‖ + ‖suzukiCanonicalTheta omega z‖ * ‖U‖) * dist q v := by ring
    _ < C * (ε / C) := by
      have hcoeff : ‖L‖ + ‖suzukiCanonicalTheta omega z‖ * ‖U‖ < C := by
        dsimp only [C]
        linarith
      have hqg' : dist q v < ε / C := by simpa only [v] using hqg
      exact (mul_le_mul_of_nonneg_right hcoeff.le dist_nonneg).trans_lt
        (mul_lt_mul_of_pos_left hqg' hC)
    _ = ε := by field_simp

end RHTower
