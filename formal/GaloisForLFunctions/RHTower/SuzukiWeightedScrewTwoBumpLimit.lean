import GaloisForLFunctions.RHTower.SuzukiPolarTranslateMultiplier
import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The twisted two-bump limit

For the polar translate multiplier `M` with spectral symbol `M(γ) = (cos(γh) − 1)(cos(γh) − cosh(h/2))`,
Suzuki's form on the multiplied two-bump test `M∗(b_t − b_0)` is the ray energy
`Σ_q M(γ_q)² B̄_q B_q / γ_q²`, and as the bump width tends to zero the ray coefficients tend to
`e^{±iγ_q t} − 1`.  Dominated convergence over the zero copies gives the limit

  `Q(M∗(b_t − b_0)) → 2 Φ_h(t)`,  `Φ_h(t) := Σ_q M(γ_q)² (1 − cos(γ_q t)) / γ_q²`,

the **weighted screw divisor**.  Consequently nonnegativity of the pole-vanishing ground energy at
every aperture forces `Φ_h(t) ≥ 0` for every real `t`.  The weighted divisor is real-valued because
the weights and the terms are both conjugated by the Schwarz copy equivalence.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The weighted screw divisor -/

/-- `Σ'_q W_q (1 − cos(γ_q t)) / γ_q²`. -/
def weightedXiScrewDivisor (W : XiZeroCopy → ℂ) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, W q * xiScrewDivisorTerm t q

/-- The polar spectral weights `M(γ_q)²`. -/
def polarSpectralWeight (h : ℝ) (q : XiZeroCopy) : ℂ :=
  polarMultiplierSpectral h (xiSpectralPoint q) ^ (2 : ℕ)

/-- `‖cos(γ h)‖ ≤ cosh(h/2)` when `|Im γ| ≤ 1/2` and `h ≥ 0`. -/
theorem norm_cos_mul_le_cosh_half {γ : ℂ} {h : ℝ} (hh : 0 ≤ h) (hγ : |γ.im| ≤ 1 / 2) :
    ‖Complex.cos (γ * h)‖ ≤ Real.cosh (h / 2) := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (γ * h * I)‖ = Real.exp (-(γ.im * h)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have h2 : ‖Complex.exp (-(γ * h) * I)‖ = Real.exp (γ.im * h) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hcosh : (Real.exp (-(γ.im * h)) + Real.exp (γ.im * h)) / 2 = Real.cosh (γ.im * h) := by
    rw [Real.cosh_eq]
    ring
  calc ‖(Complex.exp (γ * h * I) + Complex.exp (-(γ * h) * I)) / 2‖
      ≤ (‖Complex.exp (γ * h * I)‖ + ‖Complex.exp (-(γ * h) * I)‖) / 2 := by
        rw [norm_div]
        simp only [Complex.norm_ofNat]
        gcongr
        exact norm_add_le _ _
    _ = Real.cosh (γ.im * h) := by rw [h1, h2, hcosh]
    _ ≤ Real.cosh (h / 2) := by
        rw [Real.cosh_le_cosh]
        rw [abs_mul, abs_of_nonneg hh, abs_of_nonneg (by linarith : (0 : ℝ) ≤ h / 2)]
        calc |γ.im| * h ≤ (1 / 2) * h := mul_le_mul_of_nonneg_right hγ hh
          _ = h / 2 := by ring

/-- Uniform bound on the polar spectral symbol over the zero strip. -/
def polarSymbolBound (h : ℝ) : ℝ := (Real.cosh (h / 2) + 1) * (2 * Real.cosh (h / 2))

theorem polarSymbolBound_nonneg (h : ℝ) : 0 ≤ polarSymbolBound h := by
  unfold polarSymbolBound
  positivity

theorem norm_polarMultiplierSpectral_le {h : ℝ} (hh : 0 ≤ h) (q : XiZeroCopy) :
    ‖polarMultiplierSpectral h (xiSpectralPoint q)‖ ≤ polarSymbolBound h := by
  unfold polarMultiplierSpectral polarSymbolBound
  have hc := norm_cos_mul_le_cosh_half hh (abs_xiSpectralPoint_im_lt_half q).le
  have hcosh1 : 1 ≤ Real.cosh (h / 2) := Real.one_le_cosh _
  rw [norm_mul]
  gcongr
  · calc ‖Complex.cos (xiSpectralPoint q * h) - 1‖
        ≤ ‖Complex.cos (xiSpectralPoint q * h)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.cosh (h / 2) + 1 := by rw [norm_one]; linarith
  · calc ‖Complex.cos (xiSpectralPoint q * h) - (Real.cosh (h / 2) : ℂ)‖
        ≤ ‖Complex.cos (xiSpectralPoint q * h)‖ + ‖(Real.cosh (h / 2) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * Real.cosh (h / 2) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
          linarith

theorem norm_polarSpectralWeight_le {h : ℝ} (hh : 0 ≤ h) (q : XiZeroCopy) :
    ‖polarSpectralWeight h q‖ ≤ polarSymbolBound h ^ (2 : ℕ) := by
  unfold polarSpectralWeight
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_polarMultiplierSpectral_le hh q) 2

/-- The weighted divisor is summable termwise for bounded weights. -/
theorem summable_weighted_xiScrewDivisorTerm {W : XiZeroCopy → ℂ} {C : ℝ}
    (hW : ∀ q, ‖W q‖ ≤ C) (t : ℝ) :
    Summable fun q : XiZeroCopy => W q * xiScrewDivisorTerm t q := by
  refine Summable.of_norm_bounded
    (g := fun q : XiZeroCopy => C * (Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
    ((xiSpectralPoint_inv_sq_summable.mul_left _)) fun q => ?_
  rw [norm_mul]
  have h1 := hW q
  have h2 := norm_xiScrewDivisorTerm_le t q
  have hC : 0 ≤ C := (norm_nonneg _).trans h1
  calc ‖W q‖ * ‖xiScrewDivisorTerm t q‖
      ≤ C * ((Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) hC
    _ = C * (Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

/-- The polar weights are conjugated by the Schwarz copy equivalence. -/
theorem polarSpectralWeight_copyConj (h : ℝ) (q : XiZeroCopy) :
    polarSpectralWeight h (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (polarSpectralWeight h q) := by
  unfold polarSpectralWeight polarMultiplierSpectral
  have hγ : xiSpectralPoint (xiZeroCopyConjEquiv q) = -(starRingEnd ℂ) (xiSpectralPoint q) :=
    xiSpectralPoint_copyConj q
  rw [hγ, map_pow, map_mul, map_sub, map_sub, map_one, Complex.conj_ofReal]
  have hcos : Complex.cos (-(starRingEnd ℂ) (xiSpectralPoint q) * h) =
      (starRingEnd ℂ) (Complex.cos (xiSpectralPoint q * h)) := by
    rw [← Complex.cos_conj, map_mul, Complex.conj_ofReal, neg_mul, Complex.cos_neg]
  rw [hcos]

/-- **The polar weighted divisor is real.** -/
theorem star_weightedXiScrewDivisor_polar (h t : ℝ) :
    (starRingEnd ℂ) (weightedXiScrewDivisor (polarSpectralWeight h) t) =
      weightedXiScrewDivisor (polarSpectralWeight h) t := by
  unfold weightedXiScrewDivisor
  rw [Complex.conj_tsum]
  calc (∑' q : XiZeroCopy, (starRingEnd ℂ) (polarSpectralWeight h q * xiScrewDivisorTerm t q))
      = ∑' q : XiZeroCopy, polarSpectralWeight h (xiZeroCopyConjEquiv q) *
          xiScrewDivisorTerm t (xiZeroCopyConjEquiv q) := by
        refine tsum_congr fun q => ?_
        rw [map_mul, polarSpectralWeight_copyConj, xiScrewDivisorTerm_copyConj]
    _ = ∑' q : XiZeroCopy, polarSpectralWeight h q * xiScrewDivisorTerm t q :=
        xiZeroCopyConjEquiv.tsum_eq (fun b => polarSpectralWeight h b * xiScrewDivisorTerm t b)

theorem weightedXiScrewDivisor_polar_im (h t : ℝ) :
    (weightedXiScrewDivisor (polarSpectralWeight h) t).im = 0 := by
  have := congrArg Complex.im (star_weightedXiScrewDivisor_polar h t)
  rw [Complex.conj_im] at this
  linarith

/-! ## The two-bump sequence -/

/-- `ε_n = 1/(n+2)`. -/
def twoBumpEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem twoBumpEps_pos (n : ℕ) : 0 < twoBumpEps n := by
  unfold twoBumpEps
  positivity

theorem twoBumpEps_lt_one (n : ℕ) : twoBumpEps n < 1 := by
  unfold twoBumpEps
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_twoBumpEps : Tendsto twoBumpEps atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h2 := h1.inv_tendsto_atTop
  unfold twoBumpEps
  simp only [one_div]
  exact h2

/-- The two-bump test at width `ε_n` on the aperture `|t| + 2`. -/
def twoBumpSeq (t : ℝ) (n : ℕ) : SuzukiSmoothZeroMeanTest (|t| + 2) :=
  suzukiTwoBumpTest (twoBumpEps_pos n) (by linarith [twoBumpEps_lt_one n])

theorem twoBumpSeq_apply (t : ℝ) (n : ℕ) (x : ℝ) :
    (twoBumpSeq t n : ℝ → ℂ) x =
      ((suzukiCenteredBump (twoBumpEps_pos n) t x - suzukiCenteredBump (twoBumpEps_pos n) 0 x : ℝ) : ℂ) :=
  rfl

theorem integrable_suzukiCenteredBump' {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (suzukiCenteredBump hε c) :=
  integrable_suzukiCenteredBump hε c

/-- The `L¹` norm of the two-bump test is at most `2`. -/
theorem integral_norm_twoBumpSeq_le (t : ℝ) (n : ℕ) :
    ∫ u : ℝ, ‖(twoBumpSeq t n : ℝ → ℂ) u‖ ≤ 2 := by
  have hb1 := integrable_suzukiCenteredBump' (twoBumpEps_pos n) t
  have hb0 := integrable_suzukiCenteredBump' (twoBumpEps_pos n) 0
  have hle : (fun u : ℝ => ‖(twoBumpSeq t n : ℝ → ℂ) u‖) ≤
      fun u => suzukiCenteredBump (twoBumpEps_pos n) t u + suzukiCenteredBump (twoBumpEps_pos n) 0 u := by
    intro u
    dsimp only
    rw [twoBumpSeq_apply, Complex.norm_real, Real.norm_eq_abs]
    have h1 := suzukiCenteredBump_nonneg (twoBumpEps_pos n) t u
    have h0 := suzukiCenteredBump_nonneg (twoBumpEps_pos n) 0 u
    rw [abs_le]
    constructor <;> linarith
  calc ∫ u : ℝ, ‖(twoBumpSeq t n : ℝ → ℂ) u‖
      ≤ ∫ u : ℝ, (suzukiCenteredBump (twoBumpEps_pos n) t u +
          suzukiCenteredBump (twoBumpEps_pos n) 0 u) :=
        integral_mono (twoBumpSeq t n).integrable.norm (hb1.add hb0) hle
    _ = 2 := by
        rw [integral_add hb1 hb0, integral_suzukiCenteredBump, integral_suzukiCenteredBump]
        norm_num

/-! ## Bump averages of continuous functions -/

theorem integrable_mul_centeredBump {ε : ℝ} (hε : 0 < ε) (c : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun x : ℝ => g x * (suzukiCenteredBump hε c x : ℂ) := by
  have hc : Continuous fun x : ℝ => g x * (suzukiCenteredBump hε c x : ℂ) := by
    have : Continuous (suzukiCenteredBump hε c) := by
      unfold suzukiCenteredBump
      exact (continuous_bumpMollifier hε).comp (continuous_id.sub continuous_const)
    fun_prop
  refine hc.integrable_of_hasCompactSupport ?_
  have hs : HasCompactSupport (suzukiCenteredBump hε c) := by
    unfold suzukiCenteredBump
    exact (hasCompactSupport_bumpMollifier hε).comp_homeomorph (Homeomorph.subRight c)
  refine hs.mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  rw [h0]
  simp

theorem norm_integral_mul_centeredBump_sub_le {ε : ℝ} (hε : 0 < ε) (c : ℝ) {g : ℝ → ℂ}
    (hg : Continuous g) {η : ℝ} (hη : 0 ≤ η)
    (hlocal : ∀ x, |x - c| ≤ ε → ‖g x - g c‖ ≤ η) :
    ‖(∫ x : ℝ, g x * (suzukiCenteredBump hε c x : ℂ)) - g c‖ ≤ η := by
  have hint := integrable_mul_centeredBump hε c hg
  have hconst : Integrable fun x : ℝ => g c * (suzukiCenteredBump hε c x : ℂ) :=
    integrable_mul_centeredBump hε c continuous_const
  have hone : ∫ x : ℝ, (suzukiCenteredBump hε c x : ℂ) = 1 := by
    have := integral_ofReal (𝕜 := ℂ) (f := suzukiCenteredBump hε c) (μ := volume)
    rw [integral_suzukiCenteredBump] at this
    simpa using this
  have hgc : g c = ∫ x : ℝ, g c * (suzukiCenteredBump hε c x : ℂ) := by
    rw [integral_const_mul, hone, mul_one]
  rw [hgc, ← integral_sub hint hconst]
  have hbound : ∀ x : ℝ, ‖g x * (suzukiCenteredBump hε c x : ℂ) -
      g c * (suzukiCenteredBump hε c x : ℂ)‖ ≤ η * suzukiCenteredBump hε c x := by
    intro x
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiCenteredBump_nonneg hε c x)]
    by_cases hx : suzukiCenteredBump hε c x = 0
    · rw [hx]
      simp
    · exact mul_le_mul_of_nonneg_right (hlocal x (abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε hx))
        (suzukiCenteredBump_nonneg hε c x)
  refine (norm_integral_le_of_norm_le ((integrable_suzukiCenteredBump' hε c).const_mul η)
    (Filter.Eventually.of_forall hbound)).trans ?_
  rw [integral_const_mul, integral_suzukiCenteredBump, mul_one]

/-- Bump averages converge to the point value. -/
theorem tendsto_integral_mul_twoBump (c : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x * (suzukiCenteredBump (twoBumpEps_pos n) c x : ℂ))
      atTop (𝓝 (g c)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hg.continuousAt (η / 2) (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp tendsto_twoBumpEps) (δ / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hεδ : twoBumpEps n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (twoBumpEps_pos n)] at this
    linarith
  rw [dist_eq_norm]
  have hbound := norm_integral_mul_centeredBump_sub_le (twoBumpEps_pos n) c hg (η := η / 2)
    (by linarith) (fun x hx => by
      have hxc : dist x c < δ := by
        rw [Real.dist_eq]
        linarith
      have := hclose hxc
      rw [dist_eq_norm] at this
      exact this.le)
  linarith

/-! ## Ray coefficients of the two-bump sequence -/

theorem suzukiTestRayCoef_twoBumpSeq (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    suzukiTestRayCoef (twoBumpSeq t n) q =
      (∫ x : ℝ, (Complex.exp ((-(I * xiSpectralPoint q)) * (x : ℂ)) - 1) *
          (suzukiCenteredBump (twoBumpEps_pos n) t x : ℂ)) -
        ∫ x : ℝ, (Complex.exp ((-(I * xiSpectralPoint q)) * (x : ℂ)) - 1) *
          (suzukiCenteredBump (twoBumpEps_pos n) 0 x : ℂ) := by
  unfold suzukiTestRayCoef
  have hg : Continuous fun x : ℝ => Complex.exp ((-(I * xiSpectralPoint q)) * (x : ℂ)) - 1 := by
    fun_prop
  rw [← integral_sub (integrable_mul_centeredBump _ t hg) (integrable_mul_centeredBump _ 0 hg)]
  congr 1
  funext x
  rw [twoBumpSeq_apply]
  push_cast
  ring_nf

theorem suzukiTestRayCoefBar_twoBumpSeq (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    suzukiTestRayCoefBar (twoBumpSeq t n) q =
      (∫ x : ℝ, (Complex.exp ((I * xiSpectralPoint q) * (x : ℂ)) - 1) *
          (suzukiCenteredBump (twoBumpEps_pos n) t x : ℂ)) -
        ∫ x : ℝ, (Complex.exp ((I * xiSpectralPoint q) * (x : ℂ)) - 1) *
          (suzukiCenteredBump (twoBumpEps_pos n) 0 x : ℂ) := by
  unfold suzukiTestRayCoefBar
  have hg : Continuous fun x : ℝ => Complex.exp ((I * xiSpectralPoint q) * (x : ℂ)) - 1 := by
    fun_prop
  rw [← integral_sub (integrable_mul_centeredBump _ t hg) (integrable_mul_centeredBump _ 0 hg)]
  congr 1
  funext x
  rw [twoBumpSeq_apply, Complex.conj_ofReal]
  push_cast
  ring_nf

theorem tendsto_suzukiTestRayCoef_twoBumpSeq (t : ℝ) (q : XiZeroCopy) :
    Tendsto (fun n => suzukiTestRayCoef (twoBumpSeq t n) q) atTop
      (𝓝 (Complex.exp ((-(I * xiSpectralPoint q)) * (t : ℂ)) - 1)) := by
  have hg : Continuous fun x : ℝ => Complex.exp ((-(I * xiSpectralPoint q)) * (x : ℂ)) - 1 := by
    fun_prop
  have h1 := tendsto_integral_mul_twoBump t hg
  have h0 := tendsto_integral_mul_twoBump 0 hg
  simp_rw [suzukiTestRayCoef_twoBumpSeq]
  have := h1.sub h0
  simpa using this

theorem tendsto_suzukiTestRayCoefBar_twoBumpSeq (t : ℝ) (q : XiZeroCopy) :
    Tendsto (fun n => suzukiTestRayCoefBar (twoBumpSeq t n) q) atTop
      (𝓝 (Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) - 1)) := by
  have hg : Continuous fun x : ℝ => Complex.exp ((I * xiSpectralPoint q) * (x : ℂ)) - 1 := by
    fun_prop
  have h1 := tendsto_integral_mul_twoBump t hg
  have h0 := tendsto_integral_mul_twoBump 0 hg
  simp_rw [suzukiTestRayCoefBar_twoBumpSeq]
  have := h1.sub h0
  simpa using this

/-- `(e^{iγt} − 1)(e^{−iγt} − 1)/γ² = 2 · (1 − cos γt)/γ²`. -/
theorem expSlope_mul_expSlope_div_sq (t : ℝ) (q : XiZeroCopy) :
    (Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) - 1) *
        (Complex.exp ((-(I * xiSpectralPoint q)) * (t : ℂ)) - 1) / xiSpectralPoint q ^ (2 : ℕ) =
      2 * xiScrewDivisorTerm t q := by
  unfold xiScrewDivisorTerm
  have hγ : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hw : (I * xiSpectralPoint q) ^ (2 : ℕ) = -(xiSpectralPoint q ^ (2 : ℕ)) := by
    rw [mul_pow, I_sq]
    ring
  rw [hw, Complex.cosh]
  have hprod : Complex.exp ((t : ℂ) * (I * xiSpectralPoint q)) *
      Complex.exp (-((t : ℂ) * (I * xiSpectralPoint q))) = 1 := by
    rw [← Complex.exp_add]
    simp
  have e1 : Complex.exp ((I * xiSpectralPoint q) * (t : ℂ)) =
      Complex.exp ((t : ℂ) * (I * xiSpectralPoint q)) := by ring_nf
  have e2 : Complex.exp ((-(I * xiSpectralPoint q)) * (t : ℂ)) =
      Complex.exp (-((t : ℂ) * (I * xiSpectralPoint q))) := by ring_nf
  rw [e1, e2]
  set E := Complex.exp ((t : ℂ) * (I * xiSpectralPoint q)) with hE
  set F := Complex.exp (-((t : ℂ) * (I * xiSpectralPoint q))) with hF
  have hEF : (E - 1) * (F - 1) = 2 - E - F := by linear_combination hprod
  rw [hEF]
  have hγ2 : xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hγ
  field_simp
  ring

/-! ## The twisted two-bump limit -/

/-- Suzuki's form on the multiplied two-bump test as a weighted ray energy. -/
theorem suzukiScrewSmoothForm_polarTranslateTest_eq_tsum {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    {h : ℝ} (hh : 0 < h) :
    suzukiScrewSmoothForm (φ.polarTranslateTest hh) (φ.polarTranslateTest hh) =
      ∑' q : XiZeroCopy, polarSpectralWeight h q *
        (suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ)) := by
  rw [suzukiScrewSmoothForm_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [suzukiTestRayCoefBar_polarTranslateTest, suzukiTestRayCoef_polarTranslateTest]
  unfold polarSpectralWeight
  ring

theorem tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq (t : ℝ) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest hh)
        ((twoBumpSeq t n).polarTranslateTest hh)) atTop
      (𝓝 (2 * weightedXiScrewDivisor (polarSpectralWeight h) t)) := by
  simp_rw [suzukiScrewSmoothForm_polarTranslateTest_eq_tsum]
  unfold weightedXiScrewDivisor
  rw [← tsum_mul_left]
  set E : ℝ := Real.exp (|(|t| + 2)| / 2) + 1 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun q : XiZeroCopy => polarSymbolBound h ^ (2 : ℕ) * (E * 2) * (E * 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
    (xiSpectralPoint_inv_sq_summable.mul_left _) (fun q => ?_) (Filter.Eventually.of_forall fun n q => ?_)
  · -- termwise limit
    have hB := tendsto_suzukiTestRayCoef_twoBumpSeq t q
    have hBbar := tendsto_suzukiTestRayCoefBar_twoBumpSeq t q
    have hlim := ((hBbar.mul hB).div_const (xiSpectralPoint q ^ (2 : ℕ))).const_mul (polarSpectralWeight h q)
    rw [expSlope_mul_expSlope_div_sq] at hlim
    refine hlim.congr' (Filter.Eventually.of_forall fun n => ?_) |>.trans ?_
    · rfl
    · rw [show polarSpectralWeight h q * (2 * xiScrewDivisorTerm t q) =
        2 * (polarSpectralWeight h q * xiScrewDivisorTerm t q) by ring]
  · -- uniform bound
    have hW := norm_polarSpectralWeight_le hh.le q
    have hB := norm_suzukiTestRayCoef_le (twoBumpSeq t n) q
    have hBbar := norm_suzukiTestRayCoefBar_le (twoBumpSeq t n) q
    have hL1 := integral_norm_twoBumpSeq_le t n
    have hBn : ‖suzukiTestRayCoef (twoBumpSeq t n) q‖ ≤ E * 2 := by
      refine hB.trans ?_
      rw [hE]
      exact mul_le_mul_of_nonneg_left hL1 (by positivity)
    have hBbarn : ‖suzukiTestRayCoefBar (twoBumpSeq t n) q‖ ≤ E * 2 := by
      refine hBbar.trans ?_
      rw [hE]
      exact mul_le_mul_of_nonneg_left hL1 (by positivity)
    rw [norm_mul, norm_div, norm_mul, norm_pow]
    have hγ : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    calc ‖polarSpectralWeight h q‖ * (‖suzukiTestRayCoefBar (twoBumpSeq t n) q‖ *
          ‖suzukiTestRayCoef (twoBumpSeq t n) q‖ / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
        ≤ polarSymbolBound h ^ (2 : ℕ) * ((E * 2) * (E * 2) / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
          gcongr
      _ = polarSymbolBound h ^ (2 : ℕ) * (E * 2) * (E * 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

/-- **Constrained positivity at all apertures forces the polar weighted divisor to be
nonnegative.** -/
theorem weightedXiScrewDivisor_polar_re_nonneg
    (hμ : ∀ A : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilPolarGroundEnergy A)
    {h : ℝ} (hh : 0 < h) (t : ℝ) :
    0 ≤ (weightedXiScrewDivisor (polarSpectralWeight h) t).re := by
  have hlim := (tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq t hh)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hnonneg : ∀ n : ℕ, 0 ≤ (suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest hh)
      ((twoBumpSeq t n).polarTranslateTest hh)).re := fun n =>
    suzukiScrewSmoothForm_polarTranslateTest_re_nonneg_of_polarGroundEnergy_nonneg
      (twoBumpSeq t n) ⟨|t| + 3, by positivity⟩ (by simp; linarith [abs_nonneg t]) hh (hμ _)
  have h2 : 0 ≤ (2 * weightedXiScrewDivisor (polarSpectralWeight h) t).re :=
    ge_of_tendsto' hre fun n => by simpa [Function.comp] using hnonneg n
  have h3 : (2 * weightedXiScrewDivisor (polarSpectralWeight h) t).re =
      2 * (weightedXiScrewDivisor (polarSpectralWeight h) t).re := by
    simp [Complex.mul_re]
  rw [h3] at h2
  linarith

end

end RHTower
