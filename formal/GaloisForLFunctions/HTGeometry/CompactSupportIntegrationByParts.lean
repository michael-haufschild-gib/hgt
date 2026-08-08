import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# The integral of a derivative of a compactly supported function vanishes

On the line, `∫ g' = 0` whenever `g` is differentiable with compact support.  The derivative
vanishes off the support because `g` vanishes on an open neighbourhood of every exterior point, so
the integral reduces to a compact interval and the fundamental theorem of calculus closes it with
two zero boundary values.

This is the step that moves a derivative from a profile onto a convolution kernel.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Off the support, the derivative vanishes. -/
theorem deriv_eq_zero_of_notMem_tsupport {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    {t : ℝ} (ht : t ∉ tsupport g) : g' t = 0 := by
  have hev : g =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    have hopen : IsOpen (tsupport g)ᶜ := (isClosed_tsupport g).isOpen_compl
    filter_upwards [hopen.mem_nhds ht] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have h0 : HasDerivAt g 0 t := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  exact (hg t).unique h0

/-- **The integral of the derivative of a compactly supported function is zero.** -/
theorem integral_deriv_eq_zero_of_hasCompactSupport {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg'c : Continuous g') (hc : HasCompactSupport g) :
    (∫ t, g' t) = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  set R := |R₀| + 1 with hRdef
  have hR0 : 0 < R := by positivity
  have hsub : tsupport g ⊆ Ioo (-R) R := by
    intro t ht
    have h1 : t ∈ Metric.closedBall (0 : ℝ) R₀ := hR₀ ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : |t| ≤ |R₀| := le_trans h1 (le_abs_self R₀)
    constructor
    · have := neg_abs_le t; simp only [hRdef]; linarith [abs_nonneg R₀]
    · have := le_abs_self t; simp only [hRdef]; linarith [abs_nonneg R₀]
  have hzero : ∀ t : ℝ, t ∉ Icc (-R) R → g' t = 0 := by
    intro t ht
    refine deriv_eq_zero_of_notMem_tsupport hg fun hmem => ht ?_
    exact Ioo_subset_Icc_self (hsub hmem)
  have hrestrict : (∫ t, g' t) = ∫ t in Icc (-R) R, g' t :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hIcc : (∫ t in Icc (-R) R, g' t) = ∫ t in (-R)..R, g' t := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  have hend : ∀ t : ℝ, t ∉ Ioo (-R) R → g t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport fun hmem => ht (hsub hmem)
  have hgR : g R = 0 := hend R (by simp)
  have hgnR : g (-R) = 0 := hend (-R) (by simp)
  have hftc : (∫ t in (-R)..R, g' t) = g R - g (-R) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
      (hg'c.intervalIntegrable _ _)
  rw [hrestrict, hIcc, hftc, hgR, hgnR, sub_self]

/-- **The derivative moves from the profile onto the kernel.**  This is the card's `(19)`: a
convolution against the derivative of the profile equals the convolution of the profile against the
derivative of the kernel. -/
theorem lineConvolution_deriv_eq {k k' V V' : ℝ → ℝ}
    (hk : ∀ t, HasDerivAt k (k' t) t) (hkc : Continuous k) (hk'c : Continuous k')
    (hV : ∀ x, HasDerivAt V (V' x) x) (hVc : Continuous V) (hV'c : Continuous V')
    (hsupp : HasCompactSupport k) (x : ℝ) :
    lineConvolution k V' x = lineConvolution k' V x := by
  set g : ℝ → ℝ := fun t => -(k t * V (x - t)) with hgdef
  set g' : ℝ → ℝ := fun t => k t * V' (x - t) - k' t * V (x - t) with hg'def
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have hVt : HasDerivAt (fun t : ℝ => V (x - t)) (-V' (x - t)) t := by
      have hb : HasDerivAt (fun t : ℝ => x - t) (-1 : ℝ) t := by
        simpa using (hasDerivAt_id t).const_sub x
      have hcomp : HasDerivAt (fun t : ℝ => V (x - t)) (V' (x - t) * (-1)) t :=
        HasDerivAt.comp t (hV (x - t)) hb
      simpa using hcomp
    have hprod := (hk t).mul hVt
    have := hprod.neg
    refine this.congr_deriv ?_
    rw [hg'def]
    ring
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro (hsupp.isCompact) fun t ht => ?_
    have : k t = 0 := image_eq_zero_of_notMem_tsupport ht
    rw [hgdef]
    simp [this]
  have hg'cont : Continuous g' := by
    rw [hg'def]
    exact (hkc.mul (hV'c.comp (by fun_prop))).sub (hk'c.mul (hVc.comp (by fun_prop)))
  have hzero := integral_deriv_eq_zero_of_hasCompactSupport hgd hg'cont hgc
  have hsplit : (∫ t, g' t) = (∫ t, k t * V' (x - t)) - ∫ t, k' t * V (x - t) := by
    rw [hg'def]
    refine integral_sub ?_ ?_
    · exact ((hkc.mul (hV'c.comp (by fun_prop))).integrable_of_hasCompactSupport
        (hsupp.mul_right))
    · have hk'supp : HasCompactSupport k' :=
        HasCompactSupport.intro hsupp.isCompact fun t ht =>
          deriv_eq_zero_of_notMem_tsupport hk ht
      exact ((hk'c.mul (hVc.comp (by fun_prop))).integrable_of_hasCompactSupport
        hk'supp.mul_right)
  rw [hsplit] at hzero
  rw [lineConvolution, lineConvolution]
  linarith [hzero]


/-- Convolution against a compactly supported continuous kernel is linear in the profile. -/
theorem lineConvolution_sub_smul {k V V' : ℝ → ℝ} (σ : ℝ)
    (hkc : Continuous k) (hVc : Continuous V) (hV'c : Continuous V')
    (hsupp : HasCompactSupport k) (x : ℝ) :
    lineConvolution k (fun y => V' y - σ * V y) x
      = lineConvolution k V' x - σ * lineConvolution k V x := by
  have h1 : Integrable (fun t => k t * V' (x - t)) :=
    (hkc.mul (hV'c.comp (by fun_prop))).integrable_of_hasCompactSupport hsupp.mul_right
  have h2 : Integrable (fun t => k t * (σ * V (x - t))) :=
    (hkc.mul ((continuous_const.mul (hVc.comp (by fun_prop))))).integrable_of_hasCompactSupport
      hsupp.mul_right
  have hrw : (fun t => k t * (V' (x - t) - σ * V (x - t)))
      = fun t => k t * V' (x - t) - k t * (σ * V (x - t)) := by
    funext t; ring
  rw [lineConvolution, lineConvolution, lineConvolution, hrw, integral_sub h1 h2]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with t
  ring

/-- **The card's `(19)`.**  Mollifying `U = V' − σV` produces the derivative of the kernel against
`V`, minus `σ` times the kernel against `V` — no derivative of the profile survives. -/
theorem lineConvolution_weightedDeriv {k k' V V' : ℝ → ℝ} (σ : ℝ)
    (hk : ∀ t, HasDerivAt k (k' t) t) (hkc : Continuous k) (hk'c : Continuous k')
    (hV : ∀ x, HasDerivAt V (V' x) x) (hVc : Continuous V) (hV'c : Continuous V')
    (hsupp : HasCompactSupport k) (x : ℝ) :
    lineConvolution k (fun y => V' y - σ * V y) x
      = lineConvolution k' V x - σ * lineConvolution k V x := by
  rw [lineConvolution_sub_smul σ hkc hVc hV'c hsupp x,
    lineConvolution_deriv_eq hk hkc hk'c hV hVc hV'c hsupp x]


end GaloisForLFunctions.HTGeometry
