import GaloisForLFunctions.RHTower.XiOneSidedAtomRigidity
import GaloisForLFunctions.RHTower.XiGaussianOneSidedIdentityLimitRH
import GaloisForLFunctions.HTGeometry.MontelOpenSetSubsequence

/-!
# Localized real-rooted Weil eigenvector transforms force RH

Let `G_j` be holomorphic on the strip `|Im z| < 1/2 + η`, uniformly bounded there, with only real
zeros in the strip and `G_j(0) = 1`. Suppose that for apertures `a_j → ∞` each `G_j` satisfies the
zero-side eigen-equation of a restricted Weil form against every smooth test supported inside the
aperture:

`∑_q G_j(γ_q) ŵ(-γ_q) = κ_j ∫_ℝ G_j(s) ŵ(-s) ds`,

where `ŵ(z) = ∫ w(x) e^{izx} dx` and `γ_q` runs over the centered Xi zeros with multiplicity. Then
the Riemann hypothesis holds. No identification of any limit with `Xi` is assumed.

For eigenvectors `f_j` of the restricted Weil forms, `G_j` is the Fourier–Laplace transform of `f_j`
normalized to unit mass. Uniform boundedness on the strip follows from a uniform bound on
`∫ |f_j(x)| e^{(1/2+η)|x|} dx`: the localization of the eigenvectors.

**Proof.**
* Montel's theorem on the strip extracts a locally uniform limit `G`, with `G(0) = 1`.
* The eigenvalues are bounded. Otherwise, dividing by `κ_j` along a subsequence, the transform
  `s ↦ G(s) b̂(-s)` would vanish identically for a bump `b`, contradicting `G(0) b̂(0) ≠ 0`
  (Fourier inversion).
* Testing against right translates of modulated bumps and passing to the limit gives the one-sided
  identity of `XiOneSidedAtomRigidity` for `A(z) = G(z) b̂(c - z)`, so `G(γ_q) b̂(c - γ_q) = 0`.
  Choosing `c` off the zeros of `b̂` gives `G(γ_q) = 0`.
* Hurwitz on the strip keeps the zeros of `G` real, so every `γ_q` is real.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Smooth compact tests: derivatives, translates and modulations -/

/-- The derivative of a smooth compact test, as a test on the same interval. -/
def SuzukiSmoothCompactTest.derivTest {a : ℝ} (ψ : SuzukiSmoothCompactTest a) :
    SuzukiSmoothCompactTest a where
  toFun := deriv ψ
  smooth := ψ.deriv_smooth
  support_subset := ψ.deriv_support_subset

theorem suzukiSmoothFourier_derivTest {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    suzukiSmoothFourier ψ.derivTest z = -(I * z) * suzukiSmoothFourier ψ z :=
  integral_deriv_mul_cexp ψ z

theorem norm_suzukiSmoothFourier_le_of_abs_im_le {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) {Y : ℝ} (hY : 0 ≤ Y) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖suzukiSmoothFourier ψ z‖ ≤ Real.exp (Y * a) * ∫ x : ℝ, ‖ψ x‖ := by
  rw [suzukiSmoothFourier, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) (ψ.integrable.norm.const_mul _)
    (Eventually.of_forall fun x => ?_))
  show ‖ψ x * cexp (I * z * (x : ℂ))‖ ≤ Real.exp (Y * a) * ‖ψ x‖
  rw [norm_mul, Complex.norm_exp, mul_comm]
  by_cases hx : ψ x = 0
  · rw [hx, norm_zero, mul_zero, mul_zero]
  · have hmem := ψ.support_subset hx
    gcongr
    have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by
      simp [mul_re, mul_im]
    rw [hre]
    have hxa : |x| ≤ a := abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    calc -(z.im * x) ≤ |z.im * x| := neg_le_abs _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ Y * a := mul_le_mul hz hxa (abs_nonneg _) hY

/-- Inverse-square decay of the transform of a smooth compact test on every horizontal strip. -/
theorem norm_suzukiSmoothFourier_le_div {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) {Y : ℝ} (hY : 0 ≤ Y) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖suzukiSmoothFourier ψ z‖ ≤
      Real.exp (Y * a) * ((∫ x : ℝ, ‖ψ x‖) + ∫ x : ℝ, ‖ψ.derivTest.derivTest x‖) /
        (1 + ‖z‖ ^ 2) := by
  have h0 := norm_suzukiSmoothFourier_le_of_abs_im_le ψ hY hz
  have h2 := norm_suzukiSmoothFourier_le_of_abs_im_le ψ.derivTest.derivTest hY hz
  rw [suzukiSmoothFourier_derivTest, suzukiSmoothFourier_derivTest, norm_mul, norm_mul,
    norm_neg, norm_mul, Complex.norm_I, one_mul, ← mul_assoc] at h2
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hsq : ‖z‖ * ‖z‖ = ‖z‖ ^ 2 := by ring
  rw [hsq] at h2
  nlinarith [norm_nonneg (suzukiSmoothFourier ψ z)]

/-- The transform of a smooth compact test is entire. -/
theorem differentiable_suzukiSmoothFourier {a : ℝ} (ha : 0 ≤ a)
    (ψ : SuzukiSmoothCompactTest a) : Differentiable ℂ (suzukiSmoothFourier ψ) := by
  have hsupp : FourierZeroFlip.SupportedIn a (ψ : ℝ → ℂ) := by
    intro x hx
    by_contra hne
    exact hx (ψ.support_subset hne)
  have hdiff := CCMXiStrip.differentiable_unitaryLaplace ha ψ.integrable hsupp
  have heq : suzukiSmoothFourier ψ = fun z => FourierLaplaceDivision.unitaryLaplace ψ
      (-z / (2 * Real.pi)) := by
    funext z
    rw [suzukiSmoothFourier, FourierLaplaceDivision.unitaryLaplace]
    congr 1
    funext x
    rw [mul_comm]
    congr 1
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    field_simp
  rw [heq]
  exact hdiff.comp (by fun_prop)

/-- A right translate of a modulated test: `x ↦ e^{icx} ψ(x - u)`. -/
def SuzukiSmoothCompactTest.shiftMod {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (u c : ℝ) :
    SuzukiSmoothCompactTest (a + |u|) where
  toFun := fun x => cexp (I * (c : ℂ) * (x : ℂ)) * ψ (x - u)
  smooth := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => cexp (I * (c : ℂ) * (x : ℂ)) := by
      have : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => I * (c : ℂ) * (x : ℂ) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact Complex.contDiff_exp.comp this
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => ψ (x - u) :=
      ψ.smooth.comp (contDiff_id.sub contDiff_const)
    exact h1.mul h2
  support_subset := by
    intro x hx
    have hne : ψ (x - u) ≠ 0 := by
      intro h0
      exact hx (by simp [h0])
    have hmem := ψ.support_subset hne
    have hu := abs_nonneg u
    constructor
    · linarith [hmem.1, neg_abs_le u]
    · linarith [hmem.2, le_abs_self u]

theorem suzukiSmoothFourier_shiftMod {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (u c : ℝ)
    (z : ℂ) :
    suzukiSmoothFourier (ψ.shiftMod u c) z =
      cexp (I * (z + c) * (u : ℂ)) * suzukiSmoothFourier ψ (z + c) := by
  rw [suzukiSmoothFourier, suzukiSmoothFourier, ← integral_const_mul]
  have hsub := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => cexp (I * (z + c) * (u : ℂ)) * (ψ x * cexp (I * (z + c) * (x : ℂ)))) u
  rw [← hsub]
  congr 1
  funext x
  show cexp (I * (c : ℂ) * (x : ℂ)) * ψ (x - u) * cexp (I * z * (x : ℂ)) =
    cexp (I * (z + c) * (u : ℂ)) * (ψ (x - u) * cexp (I * (z + c) * ((x - u : ℝ) : ℂ)))
  have hexp : cexp (I * (c : ℂ) * (x : ℂ)) * cexp (I * z * (x : ℂ)) =
      cexp (I * (z + c) * (u : ℂ)) * cexp (I * (z + c) * ((x - u : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc cexp (I * (c : ℂ) * (x : ℂ)) * ψ (x - u) * cexp (I * z * (x : ℂ))
      = (cexp (I * (c : ℂ) * (x : ℂ)) * cexp (I * z * (x : ℂ))) * ψ (x - u) := by ring
    _ = _ := by rw [hexp]; ring

/-! ## A bump with nonzero mass -/

/-- A smooth compact test on `[-1, 1]` whose transform does not vanish at `0`. -/
theorem exists_suzukiSmoothCompactTest_fourier_zero_ne :
    ∃ b : SuzukiSmoothCompactTest 1, suzukiSmoothFourier b 0 ≠ 0 := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let b : SuzukiSmoothCompactTest 1 :=
    { toFun := fun x => ((φ x : ℝ) : ℂ)
      smooth := Complex.ofRealCLM.contDiff.comp φ.contDiff
      support_subset := by
        intro x hx
        have hφ : φ x ≠ 0 := by
          intro h0
          exact hx (by simp [h0])
        have hmem : x ∈ ball (0 : ℝ) 1 := by
          have := φ.support_eq ▸ (Function.mem_support.mpr hφ)
          simpa using this
        rw [mem_ball, Real.dist_eq, sub_zero] at hmem
        exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩ }
  refine ⟨b, ?_⟩
  have hval : suzukiSmoothFourier b 0 = ((∫ x : ℝ, φ x : ℝ) : ℂ) := by
    rw [suzukiSmoothFourier, ← integral_complex_ofReal]
    congr 1
    funext x
    simp [b]
  rw [hval]
  exact ofReal_ne_zero.mpr φ.integral_pos.ne'

/-! ## Decay of shifted transforms -/

/-- The constant controlling the inverse-square decay of a test transform on `|Im| ≤ Y`. -/
def suzukiTestDecayConst {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (Y : ℝ) : ℝ :=
  Real.exp (Y * a) * ((∫ x : ℝ, ‖ψ x‖) + ∫ x : ℝ, ‖ψ.derivTest.derivTest x‖)

theorem suzukiTestDecayConst_nonneg {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (Y : ℝ) :
    0 ≤ suzukiTestDecayConst ψ Y := by
  unfold suzukiTestDecayConst
  have h1 : 0 ≤ ∫ x : ℝ, ‖ψ x‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ ∫ x : ℝ, ‖ψ.derivTest.derivTest x‖ := integral_nonneg fun _ => norm_nonneg _
  positivity

/-- `1 + |z|² ≤ 2 (1 + c²) (1 + |c - z|²)`. -/
theorem one_add_sq_norm_le_mul (c : ℝ) (z : ℂ) :
    1 + ‖z‖ ^ 2 ≤ 2 * (1 + c ^ 2) * (1 + ‖(c : ℂ) - z‖ ^ 2) := by
  have htri : ‖z‖ ≤ ‖(c : ℂ) - z‖ + |c| := by
    have := norm_sub_le ((c : ℂ)) ((c : ℂ) - z)
    rw [sub_sub_cancel] at this
    simp only [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hsq : ‖z‖ ^ 2 ≤ 2 * ‖(c : ℂ) - z‖ ^ 2 + 2 * c ^ 2 := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg _
    have := pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_abs c, sq_nonneg (‖(c : ℂ) - z‖ - |c|)]
  nlinarith [sq_nonneg c, sq_nonneg ‖(c : ℂ) - z‖, mul_nonneg (sq_nonneg c)
    (sq_nonneg ‖(c : ℂ) - z‖)]

/-- The transform at `c - z` decays like `1/(1 + |z|²)` on every horizontal strip. -/
theorem norm_suzukiSmoothFourier_sub_le {a : ℝ} (ψ : SuzukiSmoothCompactTest a) {Y : ℝ}
    (hY : 0 ≤ Y) (c : ℝ) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖suzukiSmoothFourier ψ ((c : ℂ) - z)‖ ≤
      2 * (1 + c ^ 2) * suzukiTestDecayConst ψ Y / (1 + ‖z‖ ^ 2) := by
  have hz' : |((c : ℂ) - z).im| ≤ Y := by simpa using hz
  have hb := norm_suzukiSmoothFourier_le_div ψ hY hz'
  have hK := suzukiTestDecayConst_nonneg ψ Y
  have hpos1 : 0 < 1 + ‖(c : ℂ) - z‖ ^ 2 := by positivity
  have hpos2 : 0 < 1 + ‖z‖ ^ 2 := by positivity
  refine hb.trans ?_
  rw [div_le_div_iff₀ hpos1 hpos2]
  have := one_add_sq_norm_le_mul c z
  unfold suzukiTestDecayConst at hK ⊢
  nlinarith

/-! ## A function with vanishing Fourier transform vanishes -/

theorem eq_zero_of_integral_mul_cexp_eq_zero {H : ℝ → ℂ} (hc : Continuous H) (hi : Integrable H)
    (h0 : ∀ u : ℝ, ∫ s : ℝ, H s * cexp (-(I * (s : ℂ)) * u) = 0) : H = 0 := by
  have hF : 𝓕 H = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply]
    have := h0 (2 * Real.pi * w)
    rw [← this]
    congr 1
    funext s
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

/-! ## The eigen-equation on right translates of modulated bumps -/

theorem shiftMod_fourier_neg (b : SuzukiSmoothCompactTest 1) (u c : ℝ) (z : ℂ) :
    suzukiSmoothFourier (b.shiftMod u c) (-z) =
      cexp (I * (c : ℂ) * (u : ℂ)) *
        (suzukiSmoothFourier b ((c : ℂ) - z) * cexp (-(I * z) * u)) := by
  rw [suzukiSmoothFourier_shiftMod]
  have h1 : -z + (c : ℂ) = (c : ℂ) - z := by ring
  rw [h1]
  have h2 : cexp (I * ((c : ℂ) - z) * (u : ℂ)) =
      cexp (I * (c : ℂ) * (u : ℂ)) * cexp (-(I * z) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h2]
  ring

/-- The eigen-equation tested on `x ↦ e^{icx} b(x - u)`, with the common phase removed. -/
theorem eigen_shiftMod {G : ℂ → ℂ} {κ : ℂ} {a₀ : ℝ}
    (b : SuzukiSmoothCompactTest 1) (u c : ℝ)
    (heigen : ∀ (R : ℝ), 0 ≤ R → R < a₀ → ∀ w : SuzukiSmoothCompactTest R,
      ∑' q : XiZeroCopy, G (xiSpectralPoint q) * suzukiSmoothFourier w (-xiSpectralPoint q) =
        κ * ∫ s : ℝ, G (s : ℂ) * suzukiSmoothFourier w (-(s : ℂ)))
    (hR : 1 + |u| < a₀) :
    ∑' q : XiZeroCopy, G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u)) =
      κ * ∫ s : ℝ, G (s : ℂ) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) := by
  have h := heigen (1 + |u|) (by positivity) hR (b.shiftMod u c)
  simp_rw [shiftMod_fourier_neg] at h
  have hphase : cexp (I * (c : ℂ) * (u : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hl : ∀ q : XiZeroCopy, G (xiSpectralPoint q) * (cexp (I * (c : ℂ) * (u : ℂ)) *
      (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
        cexp (-(I * xiSpectralPoint q) * u))) =
      cexp (I * (c : ℂ) * (u : ℂ)) * (G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))) := fun q => by ring
  have hr : ∀ s : ℝ, G (s : ℂ) * (cexp (I * (c : ℂ) * (u : ℂ)) *
      (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))) =
      cexp (I * (c : ℂ) * (u : ℂ)) * (G (s : ℂ) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))) :=
    fun s => by ring
  simp_rw [hl, hr] at h
  rw [tsum_mul_left, integral_const_mul] at h
  have h' : cexp (I * (c : ℂ) * (u : ℂ)) * (∑' q : XiZeroCopy, G (xiSpectralPoint q) *
        (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))) =
      cexp (I * (c : ℂ) * (u : ℂ)) * (κ * ∫ s : ℝ, G (s : ℂ) *
        (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))) := by
    rw [h]; ring
  exact mul_left_cancel₀ hphase h'

/-! ## The receiver -/

/-- **Localized real-rooted eigenvector transforms force RH.** -/
theorem riemannHypothesis_of_realRootedEigen
    {η C : ℝ} (hη : 0 < η)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {G : ℕ → ℂ → ℂ} {κ : ℕ → ℂ}
    (hGdiff : ∀ j, DifferentiableOn ℂ (G j) (xiOneSidedStrip η))
    (hGbound : ∀ j, ∀ z ∈ xiOneSidedStrip η, ‖G j z‖ ≤ C)
    (hGreal : ∀ j, ∀ z ∈ xiOneSidedStrip η, G j z = 0 → z.im = 0)
    (hG0 : ∀ j, G j 0 = 1)
    (heigen : ∀ j (R : ℝ), 0 ≤ R → R < a j → ∀ w : SuzukiSmoothCompactTest R,
      ∑' q : XiZeroCopy, G j (xiSpectralPoint q) * suzukiSmoothFourier w (-xiSpectralPoint q) =
        κ j * ∫ s : ℝ, G j (s : ℂ) * suzukiSmoothFourier w (-(s : ℂ))) :
    RiemannHypothesis := by
  classical
  set U := xiOneSidedStrip η with hUdef
  have hUopen : IsOpen U := isOpen_xiOneSidedStrip η
  have h0U : (0 : ℂ) ∈ U := by
    show |(0 : ℂ).im| < 1 / 2 + η
    simp; linarith
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hGbound 0 0 h0U)
  set Y : ℝ := 1 / 2 + η with hYdef
  have hY : 0 ≤ Y := by rw [hYdef]; linarith
  have hγhalf : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| < 1 / 2 := by
    intro q
    have := xiSpectralPoint_im_mem_openHalf q
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hγU : ∀ q : XiZeroCopy, xiSpectralPoint q ∈ U := by
    intro q
    show |(xiSpectralPoint q).im| < 1 / 2 + η
    linarith [hγhalf q]
  have hγY : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Y := by
    intro q; rw [hYdef]; linarith [hγhalf q]
  have hsU : ∀ s : ℝ, (s : ℂ) ∈ U := by
    intro s
    show |((s : ℂ)).im| < 1 / 2 + η
    simp; linarith
  obtain ⟨b, hb0⟩ := exists_suzukiSmoothCompactTest_fourier_zero_ne
  set K₀ : ℝ := suzukiTestDecayConst b Y with hK₀
  have hK₀ : 0 ≤ K₀ := suzukiTestDecayConst_nonneg b Y
  have hbdiff : Differentiable ℂ (suzukiSmoothFourier b) :=
    differentiable_suzukiSmoothFourier zero_le_one b
  -- dominations
  have hdomq : ∀ (H : ℂ → ℂ), (∀ z ∈ U, ‖H z‖ ≤ C) → ∀ (c u : ℝ) (q : XiZeroCopy),
      ‖H (xiSpectralPoint q) * (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))‖ ≤
        C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro H hH c u q
    have hq0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
    have hb := norm_suzukiSmoothFourier_sub_le b hY c (hγY q)
    have hexp : ‖cexp (-(I * xiSpectralPoint q) * u)‖ ≤ Real.exp (|u| / 2) := by
      rw [norm_cexp_neg_I_mul_ofReal]
      apply Real.exp_le_exp.mpr
      calc u * (xiSpectralPoint q).im ≤ |u * (xiSpectralPoint q).im| := le_abs_self _
        _ = |u| * |(xiSpectralPoint q).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := by gcongr; exact (hγhalf q).le
        _ = |u| / 2 := by ring
    have hinv : 2 * (1 + c ^ 2) * K₀ / (1 + ‖xiSpectralPoint q‖ ^ 2) ≤
        2 * (1 + c ^ 2) * K₀ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      rw [div_eq_mul_one_div]
      gcongr
      linarith
    rw [norm_mul, norm_mul]
    calc ‖H (xiSpectralPoint q)‖ * (‖suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q)‖ *
          ‖cexp (-(I * xiSpectralPoint q) * u)‖)
        ≤ C * ((2 * (1 + c ^ 2) * K₀ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
            Real.exp (|u| / 2)) := by
          gcongr
          · exact hH _ (hγU q)
          · exact hb.trans hinv
      _ = C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hsumq : ∀ (c u : ℝ), Summable fun q : XiZeroCopy =>
      C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    fun c u => xiSpectralPoint_inv_sq_summable.mul_left _
  have hdoms : ∀ (H : ℂ → ℂ), (∀ z ∈ U, ‖H z‖ ≤ C) → ∀ (c u s : ℝ),
      ‖H (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
        C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ := by
    intro H hH c u s
    have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := (s : ℂ)) (by simpa using hY)
    have hexp : ‖cexp (-(I * (s : ℂ)) * u)‖ = 1 := by
      rw [norm_cexp_neg_I_mul_ofReal]; simp
    rw [norm_mul, norm_mul, hexp, mul_one]
    have hs2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by simp [sq_abs]
    rw [hs2] at hb
    calc ‖H (s : ℂ)‖ * ‖suzukiSmoothFourier b ((c : ℂ) - (s : ℂ))‖
        ≤ C * (2 * (1 + c ^ 2) * K₀ / (1 + s ^ 2)) := by
          gcongr
          exact hH _ (hsU s)
      _ = C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ := by ring
  have hintdom : ∀ c : ℝ, Integrable fun s : ℝ => C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ :=
    fun c => integrable_inv_one_add_sq.const_mul _
  have hcontline : ∀ (H : ℂ → ℂ), DifferentiableOn ℂ H U → ∀ (c u : ℝ),
      Continuous fun s : ℝ =>
        H (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) := by
    intro H hH c u
    rw [continuous_iff_continuousAt]
    intro s
    have hHc : ContinuousAt H (s : ℂ) := (hH.differentiableAt (hUopen.mem_nhds (hsU s))).continuousAt
    have h1 : ContinuousAt (fun s : ℝ => H (s : ℂ)) s :=
      ContinuousAt.comp (g := H) hHc Complex.continuous_ofReal.continuousAt
    have h2 : Continuous fun s : ℝ => suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) :=
      hbdiff.continuous.comp (by fun_prop)
    have h3 : Continuous fun s : ℝ => cexp (-(I * (s : ℂ)) * u) := by fun_prop
    exact h1.mul (h2.mul h3).continuousAt
  -- Montel on the strip
  obtain ⟨φ₁, hφ₁, Glim, hconv⟩ := exists_tendstoLocallyUniformlyOn_subseq_of_bounded hUopen
    (F := G) (C := C) hGdiff (fun n z hz => hGbound n z hz)
  have hpt : ∀ z ∈ U, Tendsto (fun k => G (φ₁ k) z) atTop (𝓝 (Glim z)) :=
    fun z hz => hconv.tendsto_at hz
  have hGlim0 : Glim 0 = 1 := by
    have := hpt 0 h0U
    simp only [hG0] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hGlimdiff : DifferentiableOn ℂ Glim U :=
    hconv.differentiableOn (Eventually.of_forall fun k => hGdiff _) hUopen
  have hGlimbound : ∀ z ∈ U, ‖Glim z‖ ≤ C := by
    intro z hz
    exact le_of_tendsto' ((hpt z hz).norm) fun k => hGbound _ z hz
  have hlarge : ∀ (u : ℝ), ∀ᶠ k in atTop, 1 + |u| < a (φ₁ k) :=
    fun u => (ha.comp hφ₁.tendsto_atTop).eventually_gt_atTop _
  -- limits of the two sides along any further subsequence
  have hlimsum : ∀ (ψ : ℕ → ℕ), Tendsto ψ atTop atTop → ∀ (c u : ℝ),
      Tendsto (fun k => ∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u))) atTop
        (𝓝 (∑' q : XiZeroCopy, Glim (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u)))) := by
    intro ψ hψ c u
    refine tendsto_tsum_of_dominated_convergence (hsumq c u) (fun q => ?_)
      (Eventually.of_forall fun k q => hdomq _ (fun z hz => hGbound _ z hz) c u q)
    exact ((hpt _ (hγU q)).comp hψ).mul_const _
  have hlimint : ∀ (ψ : ℕ → ℕ), Tendsto ψ atTop atTop → ∀ (c u : ℝ),
      Tendsto (fun k => ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))) atTop
        (𝓝 (∫ s : ℝ, Glim (s : ℂ) *
          (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)))) := by
    intro ψ hψ c u
    refine tendsto_integral_of_dominated_convergence _
      (fun k => (hcontline _ (hGdiff _) c u).aestronglyMeasurable) (hintdom c)
      (fun k => ae_of_all _ fun s => hdoms _ (fun z hz => hGbound _ z hz) c u s)
      (ae_of_all _ fun s => ?_)
    exact ((hpt _ (hsU s)).comp hψ).mul_const _
  -- the eigenvalues are bounded
  have hκbdd : ∃ M : ℝ, ∀ k, ‖κ (φ₁ k)‖ ≤ M := by
    by_contra hnot
    push Not at hnot
    have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, (n : ℝ) + 1 < ‖κ (φ₁ k)‖ := by
      intro n
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨k, hk⟩ := hnot ((n : ℝ) + 1 + ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      refine ⟨k, ?_, by linarith⟩
      by_contra hlt
      push Not at hlt
      have hle : ‖κ (φ₁ k)‖ ≤ ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖ :=
        Finset.single_le_sum (f := fun i => ‖κ (φ₁ i)‖) (fun i _ => norm_nonneg _)
          (Finset.mem_range.mpr hlt)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨ψ, hψ, hψk⟩ := extraction_forall_of_frequently hfreq
    have hzero : ∀ u : ℝ, ∫ s : ℝ, Glim (s : ℂ) *
        (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) = 0 := by
      intro u
      set S : ℝ := ∑' q : XiZeroCopy, C * (2 * (1 + (0 : ℝ) ^ 2) * K₀) * Real.exp (|u| / 2) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) with hS
      have hbound : ∀ᶠ k in atTop, ‖∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
            S / ((k : ℝ) + 1) := by
        filter_upwards [hψ.tendsto_atTop.eventually (hlarge u)] with k hk
        have hid := eigen_shiftMod (G := G (φ₁ (ψ k))) (κ := κ (φ₁ (ψ k))) (a₀ := a (φ₁ (ψ k)))
          b u 0 (heigen (φ₁ (ψ k))) hk
        have hκpos : (k : ℝ) + 1 < ‖κ (φ₁ (ψ k))‖ := hψk k
        have hκne : κ (φ₁ (ψ k)) ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hκpos; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
        have hsumbd : ‖∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
            (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
              cexp (-(I * xiSpectralPoint q) * u))‖ ≤ S := by
          refine (norm_tsum_le_tsum_norm ?_).trans ?_
          · exact (hsumq 0 u).of_nonneg_of_le (fun q => norm_nonneg _)
              (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)
          · exact Summable.tsum_le_tsum (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)
              ((hsumq 0 u).of_nonneg_of_le (fun q => norm_nonneg _)
                (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)) (hsumq 0 u)
        rw [hid] at hsumbd
        rw [norm_mul] at hsumbd
        have hS0 : 0 ≤ S := tsum_nonneg fun q => by positivity
        rw [le_div_iff₀ (by positivity)]
        calc ‖∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
              (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ *
              ((k : ℝ) + 1)
            ≤ ‖∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
              (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ *
              ‖κ (φ₁ (ψ k))‖ := by gcongr
          _ = ‖κ (φ₁ (ψ k))‖ * ‖∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
              (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) *
                cexp (-(I * (s : ℂ)) * u))‖ := by ring
          _ ≤ S := hsumbd
      have hto0 : Tendsto (fun k => ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)))
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound ?_
        have : Tendsto (fun k : ℕ => S * ((k : ℝ) + 1)⁻¹) atTop (𝓝 (S * 0)) :=
          tendsto_const_nhds.mul
            (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        simpa [div_eq_mul_inv] using this
      exact tendsto_nhds_unique (hlimint ψ hψ.tendsto_atTop 0 u) hto0
    set Hf : ℝ → ℂ := fun s => Glim (s : ℂ) * suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ))
      with hHf
    have hHcont : Continuous Hf := by
      have := hcontline Glim hGlimdiff 0 0
      simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
      simpa [hHf] using this
    have hHint : Integrable Hf := by
      refine (hintdom 0).mono' hHcont.aestronglyMeasurable (ae_of_all _ fun s => ?_)
      have := hdoms Glim hGlimbound 0 0 s
      simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
      simpa [hHf] using this
    have hH0 : Hf = 0 := eq_zero_of_integral_mul_cexp_eq_zero hHcont hHint (fun u => by
      have := hzero u
      simpa [hHf, mul_assoc] using this)
    have hval := congrFun hH0 0
    simp only [hHf, ofReal_zero, sub_zero, hGlim0, one_mul, Pi.zero_apply] at hval
    exact hb0 hval
  -- a convergent subsequence of eigenvalues
  obtain ⟨M, hM⟩ := hκbdd
  obtain ⟨κlim, -, ψ, hψ, hκlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall
    (x := (0 : ℂ)) (r := M)) (x := fun k => κ (φ₁ k))
    (fun k => by rw [mem_closedBall, dist_zero_right]; exact hM k)
  -- the one-sided limit identity for every modulation
  have hAzero : ∀ (c : ℝ) (q : XiZeroCopy),
      Glim (xiSpectralPoint q) * suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) = 0 := by
    intro c q
    have hlimid : ∀ u : ℝ, 0 < u →
        ∑' q : XiZeroCopy, (fun z => Glim z * suzukiSmoothFourier b ((c : ℂ) - z))
            (xiSpectralPoint q) * cexp (-(I * xiSpectralPoint q) * u) =
          ∫ t : ℝ, (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) (t : ℂ) *
            cexp (-(I * (t : ℂ)) * u) := by
      intro u _
      have hL := hlimsum ψ hψ.tendsto_atTop c u
      have hR := (hκlim.mul (hlimint ψ hψ.tendsto_atTop c u))
      have heq : ∀ᶠ k in atTop, ∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u)) =
          (fun k => κ (φ₁ k)) (ψ k) * ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
            (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) := by
        filter_upwards [hψ.tendsto_atTop.eventually (hlarge u)] with k hk
        exact eigen_shiftMod b u c (heigen (φ₁ (ψ k))) hk
      have hfin := tendsto_nhds_unique (hL.congr' heq) hR
      rw [← integral_const_mul] at hfin
      convert hfin using 1
      · exact tsum_congr fun q => by ring
      · exact integral_congr_ae (ae_of_all _ fun t => by ring)
    have hdiffB : ∀ z : ℂ, |z.im| < 1 / 2 + η →
        DifferentiableAt ℂ (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) z := by
      intro z hz
      have hzU : z ∈ U := hz
      exact ((hGlimdiff.differentiableAt (hUopen.mem_nhds hzU)).mul
        ((hbdiff _).comp z (by fun_prop))).const_mul _
    set Kc : ℝ := (max 1 ‖κlim‖) * (C * (2 * (1 + c ^ 2) * K₀)) with hKc
    have hdomA : StripInvSqDominated η Kc (fun z => Glim z * suzukiSmoothFourier b ((c : ℂ) - z)) := by
      intro z hz
      have hzU : z ∈ U := hz
      have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := z) (by rw [hYdef]; exact hz.le)
      rw [norm_mul]
      calc ‖Glim z‖ * ‖suzukiSmoothFourier b ((c : ℂ) - z)‖
          ≤ C * (2 * (1 + c ^ 2) * K₀ / (1 + ‖z‖ ^ 2)) := by
            gcongr
            exact hGlimbound z hzU
        _ ≤ Kc / (1 + ‖z‖ ^ 2) := by
            have hle : C * (2 * (1 + c ^ 2) * K₀) ≤ Kc := by
              rw [hKc]
              calc C * (2 * (1 + c ^ 2) * K₀) = 1 * (C * (2 * (1 + c ^ 2) * K₀)) := by ring
                _ ≤ max 1 ‖κlim‖ * (C * (2 * (1 + c ^ 2) * K₀)) := by
                    gcongr; exact le_max_left _ _
            rw [← mul_div_assoc]
            gcongr
    have hdomB : StripInvSqDominated η Kc
        (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) := by
      intro z hz
      have hA := hdomA z hz
      have hzU : z ∈ U := hz
      have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := z) (by rw [hYdef]; exact hz.le)
      rw [norm_mul, norm_mul]
      calc ‖κlim‖ * (‖Glim z‖ * ‖suzukiSmoothFourier b ((c : ℂ) - z)‖)
          ≤ max 1 ‖κlim‖ * (C * (2 * (1 + c ^ 2) * K₀ / (1 + ‖z‖ ^ 2))) := by
            gcongr
            · exact le_max_right _ _
            · exact hGlimbound z hzU
        _ = Kc / (1 + ‖z‖ ^ 2) := by rw [hKc]; ring
    exact eq_zero_of_xiOneSidedIdentity hη hdiffB hdomA hdomB hlimid q
  -- choose a modulation off the zeros of the bump transform
  have hGzero : ∀ q : XiZeroCopy, Glim (xiSpectralPoint q) = 0 := by
    intro q
    by_contra hne
    have hvan : ∀ c : ℝ, suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) = 0 := by
      intro c
      exact (mul_eq_zero.mp (hAzero c q)).resolve_left hne
    have han : AnalyticOnNhd ℂ (suzukiSmoothFourier b) univ :=
      hbdiff.differentiableOn.analyticOnNhd isOpen_univ
    set z₀ : ℂ := -xiSpectralPoint q with hz₀
    have hfreq : ∃ᶠ w in 𝓝[≠] z₀, suzukiSmoothFourier b w = 0 := by
      have hseq : Tendsto (fun n : ℕ => z₀ + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h2 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
              (𝓝 ((0 : ℝ) : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp h1
          rw [ofReal_zero] at h2
          simpa using (tendsto_const_nhds (x := z₀)).add h2
        · refine Eventually.of_forall fun n => ?_
          simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero]
          positivity
      refine hseq.frequently (Frequently.of_forall fun n => ?_)
      have := hvan (1 / ((n : ℝ) + 1))
      rw [hz₀]
      convert this using 2
      ring
    have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ z₀) hfreq (mem_univ 0)
    exact hb0 hall
  -- the limit has only real zeros in the strip
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hS : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have him := CCMXiStrip.zero_mem_closed_of_tendstoLocallyUniformlyOn (S := {w : ℂ | w.im = 0})
    hUopen (convex_xiOneSidedStrip η).isPreconnected hconv (hGlimdiff.analyticOnNhd hUopen)
    (Eventually.of_forall fun k => hGdiff _) hS
    (Eventually.of_forall fun k w hw hzero => hGreal _ w hw hzero)
    h0U (by rw [hGlim0]; exact one_ne_zero) (hγU q) (hGzero q)
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using him

end

end RHTower
