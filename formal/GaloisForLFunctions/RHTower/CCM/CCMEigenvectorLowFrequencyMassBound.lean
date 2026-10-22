import GaloisForLFunctions.RHTower.CCM.CCMGroundEnergyZeroSumBound
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarBombieriYoshidaSharp

/-!
# Eigenvectors with low-frequency content have bounded eigenvalues

Let `u` be an eigenvector of the restricted Weil form at aperture `a`, so `Q_a(u, s) = μ ⟨u, s⟩`
on smooth interior sources. Write `f` for its physical function and `F(z) = ∫ conj(f(t)) e^{izt} dt`
for its transform. The *low-frequency content of `F` at width `σ`* is

  `I_σ(F) = ∫ F(s) e^{-σs²} b̂(-s) ds`,

the average of `F` against a Gaussian window of width `σ^{-1/2}` at the origin, where `b` is a
fixed nonnegative bump. In the time domain it is `√(π/σ)` times the conjugate of the mass of `f`
against the positive kernel `b ⋆ e^{-t²/4σ}`.

* `abs_eigenvalue_le_of_lowFrequencyMass`: if `8σ ≤ a - 2` and the Gaussian tail
  `‖f‖₁ e^{a} · 2e^{-(a-2)²/16σ}` is below `|I_σ(F)|/2` (up to a fixed constant), then
  `|μ| ≤ 2π (1 + C ‖f‖₁ e^{a/2 - 165σ/2} / |I_σ(F)|)`.
* `riemannHypothesis_of_fullGrounds_lowFrequencyMass`: if nonzero full ground states at apertures
  `a_j → ∞` satisfy `‖f_j‖₁ ≤ M e^{a_j} |I_{a_j/40}(F_j)|`, the Riemann hypothesis holds.
* `abs_eigenvalue_le_of_windowedMass`, `riemannHypothesis_of_fullGrounds_windowedMass`: the same
  for the window `e^{-σs²} b̂(-s)` of any base test `b`, and any finite family of windows. With the
  derivative test, `riemannHypothesis_of_fullGrounds_evenOrOddWindow` needs no parity hypothesis on
  the ground states.
* `abs_im_xiSpectralPoint_le_of_fullGrounds_lowFrequencyMass`: if at every large aperture `B` some
  nonzero ground state has `‖f‖₁ ≤ M e^{ηB} |I_{cB}(F)|` with `16c(1 + η) < 1`, every zero satisfies
  `|Re ρ - 1/2| ≤ max 0 (η + 1/2 - 165c/2) / 2`. The decay rate of the low-frequency share bounds the
  width of the zero-free strip.

No real-rootedness, parity, zero-sum or mass hypothesis is used. Under ¬RH the ground energies are
unbounded below. So at those apertures the ground states carry exponentially little low-frequency
content: their transforms live at the ordinates of the zeros, all of which have `|Re γ| > 9`.

**Proof.** Smear the exact shift identities against a Gaussian of width `σ`, as in
`abs_eigenvalue_le_of_zeroSum`. The zero side is bounded by the Paley–Wiener growth
`|F(γ)| ≤ ‖f‖₁ e^{a/2}` and the zero-free window `(Re γ)² > 331/4`, which give
`|e^{-σγ²}| = e^{-σ((Re γ)² - (Im γ)²)} ≤ e^{-165σ/2}`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The low-frequency content `∫ F(s) e^{-σs²} b̂(-s) ds` of `F` at width `σ`. -/
def lowFrequencyMass (F : ℂ → ℂ) (σ : ℝ) : ℂ :=
  ∫ s : ℝ, F (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) * suzukiSmoothFourier posBumpTest (-(s : ℂ))

/-- The windowed content `∫ F(s) e^{-σs²} b̂(-s) ds` of `F` at width `σ`, for a base test `b`. -/
def windowedMass (b : SuzukiSmoothCompactTest 1) (F : ℂ → ℂ) (σ : ℝ) : ℂ :=
  ∫ s : ℝ, F (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) * suzukiSmoothFourier b (-(s : ℂ))

theorem lowFrequencyMass_eq_windowedMass (F : ℂ → ℂ) (σ : ℝ) :
    lowFrequencyMass F σ = windowedMass posBumpTest F σ := rfl

/-- The constant of the zero-side bound for the base test `b`. -/
def windowZeroConst (b : SuzukiSmoothCompactTest 1) : ℝ :=
  4 * suzukiTestDecayConst b 1 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)

theorem windowZeroConst_nonneg (b : SuzukiSmoothCompactTest 1) : 0 ≤ windowZeroConst b := by
  unfold windowZeroConst
  have h1 := suzukiTestDecayConst_nonneg b 1
  have h2 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    tsum_nonneg fun q => by positivity
  positivity

/-- The constant of the zero-side bound for the nonnegative bump. -/
def lowFrequencyZeroConst : ℝ := windowZeroConst posBumpTest

theorem lowFrequencyZeroConst_nonneg : 0 ≤ lowFrequencyZeroConst :=
  windowZeroConst_nonneg posBumpTest

theorem eigenDefectConst_nonneg (b : SuzukiSmoothCompactTest 1) :
    0 ≤ eigenDefectConst b (1 / 2) 0 := by
  unfold eigenDefectConst
  have h1 := suzukiTestDecayConst_nonneg b (1 / 2 + 1 / 2)
  have h2 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    tsum_nonneg fun q => by positivity
  have h3 : 0 ≤ ∫ s : ℝ, (1 + s ^ 2)⁻¹ := integral_nonneg fun s => by positivity
  positivity

theorem eigenDefectConst_posBumpTest_nonneg : 0 ≤ eigenDefectConst posBumpTest (1 / 2) 0 :=
  eigenDefectConst_nonneg posBumpTest

/-- **The zero side under a uniform bound.** If `|G(γ_q)| ≤ P` at every Xi zero, the Gaussian
smeared zero sum at width `σ ≥ 0` is at most `P e^{-165σ/2}` times a constant. -/
theorem norm_zeroSide_gauss_le_of_bound (b : SuzukiSmoothCompactTest 1) {G : ℂ → ℂ} {σ P : ℝ}
    (hσ : 0 ≤ σ) (hP : 0 ≤ P)
    (hG : ∀ q : XiZeroCopy, ‖G (xiSpectralPoint q)‖ ≤ P) :
    ‖∑' q : XiZeroCopy, (G (xiSpectralPoint q) * cexp (-(σ : ℂ) * xiSpectralPoint q ^ 2)) *
        (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * ((0 : ℝ) : ℂ)))‖ ≤
      P * Real.exp (-(165 / 2 * σ)) * (2 * suzukiTestDecayConst b 1 *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set K : ℝ := suzukiTestDecayConst b 1 with hK
  have hK0 : 0 ≤ K := suzukiTestDecayConst_nonneg _ _
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((xiSpectralPoint_inv_sq_summable.mul_left (2 * K)).mul_left
    (P * Real.exp (-(165 / 2 * σ)))).hasSum fun q => ?_
  have hGq := hG q
  set γ := xiSpectralPoint q with hγ
  have hy : |γ.im| ≤ 1 / 2 := by
    have := xiSpectralPoint_im_mem_openHalf q
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hx : (331 / 4 : ℝ) < γ.re ^ 2 := xiSpectralPoint_re_sq_gt_floor q
  have hγ0 : γ ≠ 0 := xiSpectralPoint_ne_zero q
  have hpos : 0 < ‖γ‖ ^ 2 := by positivity
  have hb := norm_suzukiSmoothFourier_sub_le b zero_le_one 0 (z := γ)
    (hy.trans (by norm_num))
  have hexp0 : cexp (-(I * γ) * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [hexp0, mul_one, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul_sq]
  have hy2 : γ.im ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs γ.im, abs_nonneg γ.im]
  have hexpo : Real.exp (-(σ * (γ.re ^ 2 - γ.im ^ 2))) ≤ Real.exp (-(165 / 2 * σ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hbinv : 2 * (1 + (0 : ℝ) ^ 2) * K / (1 + ‖γ‖ ^ 2) ≤ 2 * K * (1 / ‖γ‖ ^ (2 : ℕ)) := by
    rw [div_eq_mul_one_div]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one]
    gcongr
    linarith
  exact mul_le_mul (mul_le_mul hGq hexpo (Real.exp_pos _).le hP) (hb.trans hbinv) (norm_nonneg _)
    (by positivity)

section Eigen

open GaloisForLFunctions.HTGeometry
open RHTower.CCMFullGroundEigen RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

/-- **Windowed content bounds the eigenvalue.** Let `u` be an eigenvector of the restricted Weil
form at aperture `a`, with eigenvalue `μ`, physical function `f` and transform `F`, and let `b` be
any base test. Let `σ > 0` with `8σ ≤ a - 2`, and suppose the windowed content `W_b(F)` is nonzero
and dominates the Gaussian tail: `‖f‖₁ e^{a} · 2e^{-(a-2)²/16σ} · D_b ≤ |W_b(F)|/2`. Then
`|μ| ≤ 2π (1 + C_b ‖f‖₁ e^{a/2 - 165σ/2} / |W_b(F)|)`. -/
theorem abs_eigenvalue_le_of_windowedMass (b : SuzukiSmoothCompactTest 1)
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (μ : ℝ)
    (heig : ∀ s : CCMComplexSmoothInteriorSource a, ccmRestrictedWeilForm a u s.toCCMFormVector =
      (μ : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a u t) * s t)
    {σ : ℝ} (hσ : 0 < σ) (hR : 8 * σ ≤ a.1 - 2)
    (hI : windowedMass b (conjTransform (timeRep a u)) σ ≠ 0)
    (hsmall : (∫ t : ℝ, ‖timeRep a u t‖) * Real.exp a.1 *
        (2 * Real.exp (-((a.1 - 2) ^ 2 / (16 * σ)))) * eigenDefectConst b (1 / 2) 0 ≤
      ‖windowedMass b (conjTransform (timeRep a u)) σ‖ / 2) :
    |μ| ≤ 2 * Real.pi * (1 + windowZeroConst b * (∫ t : ℝ, ‖timeRep a u t‖) *
      Real.exp (a.1 / 2 - 165 / 2 * σ) / ‖windowedMass b (conjTransform (timeRep a u)) σ‖) := by
  classical
  set f : ℝ → ℂ := timeRep a u with hf
  set F : ℂ → ℂ := conjTransform f with hFdef
  set N : ℝ := ∫ t : ℝ, ‖f t‖ with hNdef
  have hfi := integrable_timeRep a u
  have hsupp := supportedIn_timeRep a u
  have hs := bound_support_of_supportedIn hsupp
  have hN0 : 0 ≤ N := integral_nonneg fun t => norm_nonneg _
  have hdiff : Differentiable ℂ F := differentiable_conjTransform a.2.le hfi hsupp
  have hFdiff : DifferentiableOn ℂ F (xiOneSidedStrip (1 / 2)) := hdiff.differentiableOn
  set B : ℝ := N * Real.exp a.1 with hBdef
  have hB : ∀ z ∈ xiOneSidedStrip (1 / 2), ‖F z‖ ≤ B := by
    intro z hz
    have hz' : |z.im| ≤ 1 := by
      have : |z.im| < 1 / 2 + 1 / 2 := hz
      linarith
    have h1 := norm_conjTransform_le_mul_exp zero_le_one hfi hs hz'
    rwa [one_mul] at h1
  -- the exact shift identities for `F`
  set κ : ℂ := (μ : ℂ) * (1 / (2 * Real.pi) : ℂ) with hκdef
  have heigen : ∀ (R : ℝ), 0 ≤ R → R < a.1 → ∀ w : SuzukiSmoothCompactTest R,
      ∑' q : XiZeroCopy, F (xiSpectralPoint q) * suzukiSmoothFourier w (-xiSpectralPoint q) =
        κ * ∫ s : ℝ, F (s : ℂ) * suzukiSmoothFourier w (-(s : ℂ)) := by
    intro R hR0 hRa w
    have hid := zeroSide_eigen_of_formEigen a heig (testSource a w hRa)
    have hw : ∀ z, suzukiSmoothFourier (testSource a w hRa).toSuzukiSmoothCompactTest z =
        suzukiSmoothFourier w z := fun z => rfl
    simp only [hw] at hid
    exact hid
  have hid : ∀ v : ℝ, |v| ≤ a.1 - 2 → ∑' q : XiZeroCopy, F (xiSpectralPoint q) *
      (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
        cexp (-(I * xiSpectralPoint q) * v)) =
      κ * ∫ s : ℝ, F (s : ℂ) *
        (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * v)) :=
    fun v hv => eigen_shiftMod b v 0 heigen (by linarith)
  have hdef := norm_gaussWeightedDefect_le (η := 1 / 2) (B := B) (σ := σ) (κ := κ)
    (by norm_num) hσ hFdiff hB b 0 0 (a.1 - 2) hid
  set Z : ℂ := ∑' q : XiZeroCopy, (F (xiSpectralPoint q) *
      cexp (-(σ : ℂ) * xiSpectralPoint q ^ 2)) *
    (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
      cexp (-(I * xiSpectralPoint q) * ((0 : ℝ) : ℂ))) with hZdef
  set Iint : ℂ := ∫ s : ℝ, (F (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2)) *
    (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) *
      cexp (-(I * (s : ℂ)) * ((0 : ℝ) : ℂ))) with hIdef
  have hIeq : Iint = windowedMass b F σ := by
    rw [hIdef, windowedMass]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [ofReal_zero, zero_sub, mul_zero, Complex.exp_zero, mul_one, mul_assoc]
  have hIn : ‖Iint‖ = ‖windowedMass b F σ‖ := by rw [hIeq]
  have hIpos : 0 < ‖Iint‖ := by rw [hIn]; exact norm_pos_iff.mpr hI
  set D : ℝ := eigenDefectConst b (1 / 2) 0 with hDdef
  have hD0 : 0 ≤ D := eigenDefectConst_nonneg b
  set E : ℝ := B * gaussShiftTail σ 0 (a.1 - 2) * D with hEdef
  have hτ := gaussShiftTail_zero_le (σ := σ) (R := a.1 - 2) hσ hR
  have hE : E ≤ ‖Iint‖ / 2 := by
    rw [hIn]
    refine le_trans ?_ hsmall
    rw [hEdef, hBdef]
    gcongr
  -- algebra on `κ`
  have hkey : ‖κ‖ * ‖Iint‖ ≤ ‖Z‖ + (1 + ‖κ‖) * E := by
    have h1 : κ * Iint = Z - (Z - κ * Iint) := by ring
    rw [← norm_mul, h1]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hdef)
  have hκE : ‖κ‖ * E ≤ ‖κ‖ * (‖Iint‖ / 2) := mul_le_mul_of_nonneg_left hE (norm_nonneg _)
  have hκle : ‖κ‖ ≤ 2 * ‖Z‖ / ‖Iint‖ + 1 := by
    rw [div_add_one hIpos.ne', le_div_iff₀ hIpos]
    nlinarith [norm_nonneg κ]
  -- the zero side
  have hFq : ∀ q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ≤ N * Real.exp (a.1 / 2) := by
    intro q
    have hy : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
      have := xiSpectralPoint_im_mem_openHalf q
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have h1 := norm_conjTransform_le_mul_exp (by norm_num : (0 : ℝ) ≤ 1 / 2) hfi hs hy
    rwa [show 1 / 2 * a.1 = a.1 / 2 by ring] at h1
  have hZ := norm_zeroSide_gauss_le_of_bound b hσ.le (by positivity) hFq
  set K₀ : ℝ := suzukiTestDecayConst b 1 with hK₀
  set SX : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hSX
  have hratio : 2 * ‖Z‖ / ‖Iint‖ ≤
      windowZeroConst b * N * Real.exp (a.1 / 2 - 165 / 2 * σ) / ‖Iint‖ := by
    refine div_le_div_of_nonneg_right ?_ hIpos.le
    calc 2 * ‖Z‖ ≤ 2 * (N * Real.exp (a.1 / 2) * Real.exp (-(165 / 2 * σ)) * (2 * K₀ * SX)) := by
          gcongr
      _ = windowZeroConst b * N * Real.exp (a.1 / 2 - 165 / 2 * σ) := by
          rw [windowZeroConst, sub_eq_add_neg, Real.exp_add]
          ring
  have hκnorm : ‖κ‖ = |μ| / (2 * Real.pi) := by
    rw [hκdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this]
    ring
  have hfinal : ‖κ‖ ≤ 1 + windowZeroConst b * N * Real.exp (a.1 / 2 - 165 / 2 * σ) / ‖Iint‖ := by
    linarith
  rw [hκnorm, div_le_iff₀ (by positivity)] at hfinal
  rw [← hIn]
  linarith

/-- **Low-frequency content bounds the eigenvalue.** The case `b = posBumpTest` of
`abs_eigenvalue_le_of_windowedMass`. -/
theorem abs_eigenvalue_le_of_lowFrequencyMass
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (μ : ℝ)
    (heig : ∀ s : CCMComplexSmoothInteriorSource a, ccmRestrictedWeilForm a u s.toCCMFormVector =
      (μ : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a u t) * s t)
    {σ : ℝ} (hσ : 0 < σ) (hR : 8 * σ ≤ a.1 - 2)
    (hI : lowFrequencyMass (conjTransform (timeRep a u)) σ ≠ 0)
    (hsmall : (∫ t : ℝ, ‖timeRep a u t‖) * Real.exp a.1 *
        (2 * Real.exp (-((a.1 - 2) ^ 2 / (16 * σ)))) * eigenDefectConst posBumpTest (1 / 2) 0 ≤
      ‖lowFrequencyMass (conjTransform (timeRep a u)) σ‖ / 2) :
    |μ| ≤ 2 * Real.pi * (1 + lowFrequencyZeroConst * (∫ t : ℝ, ‖timeRep a u t‖) *
      Real.exp (a.1 / 2 - 165 / 2 * σ) / ‖lowFrequencyMass (conjTransform (timeRep a u)) σ‖) :=
  abs_eigenvalue_le_of_windowedMass posBumpTest a u μ heig hσ hR hI hsmall

/-- A vector of the form domain whose physical function vanishes almost everywhere is zero. -/
theorem ccmArchimedeanFormToAperture_eq_zero_of_timeRep_ae_zero {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (h : timeRep a u =ᵐ[volume] 0) :
    ccmArchimedeanFormToAperture a u = 0 := by
  have h2 : ((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact (coeFn_eq_timeRep a u).trans h
  exact ZeroMemClass.coe_eq_zero.mp h2

/-- A nonzero vector of the form domain has positive `L¹` mass. -/
theorem integral_norm_timeRep_pos {a : SuzukiPositiveAperture} {u : CCMArchimedeanFormDomain a}
    (hne : ccmArchimedeanFormToAperture a u ≠ 0) : 0 < ∫ t : ℝ, ‖timeRep a u t‖ := by
  have h0 : (0 : ℝ) ≤ ∫ t : ℝ, ‖timeRep a u t‖ := integral_nonneg fun t => norm_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hae : (fun t => ‖timeRep a u t‖) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => norm_nonneg _) (integrable_timeRep a u).norm).mp
        h.symm
    exact ccmArchimedeanFormToAperture_eq_zero_of_timeRep_ae_zero
      (hae.mono fun t ht => by simpa using ht)

/-- At width `σ = a/40` the Gaussian tail beats `e^{2a}` eventually. -/
theorem eventually_lowFrequency_tail_small {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∀ᶠ j in atTop, M * Real.exp (2 * a j) *
        (2 * Real.exp (-((a j - 2) ^ 2 / (16 * (a j / 40))))) * D ≤ 1 / 2 := by
  have hlim : Tendsto (fun j => 2 * M * D * Real.exp 10 * Real.exp (-(a j / 2))) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (ha.atTop_div_const two_pos)).const_mul
      (2 * M * D * Real.exp 10)
    rw [mul_zero] at h
    exact h
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    ha.eventually_ge_atTop 4] with j hj h4
  set x : ℝ := a j with hx
  have hx0 : 0 < x := by linarith
  have hexp : 2 * x - (x - 2) ^ 2 / (16 * (x / 40)) ≤ 10 + -(x / 2) := by
    have h1 : (x - 2) ^ 2 / (16 * (x / 40)) = 5 / 2 * ((x - 2) ^ 2 / x) := by field_simp; ring
    have h2 : x - 4 ≤ (x - 2) ^ 2 / x := by
      rw [le_div_iff₀ hx0]; nlinarith
    rw [h1]
    nlinarith
  calc M * Real.exp (2 * x) * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (x / 40))))) * D
      = 2 * M * D * Real.exp (2 * x - (x - 2) ^ 2 / (16 * (x / 40))) := by
        rw [show 2 * x - (x - 2) ^ 2 / (16 * (x / 40)) =
          2 * x + -((x - 2) ^ 2 / (16 * (x / 40))) by ring, Real.exp_add]
        ring
    _ ≤ 2 * M * D * Real.exp (10 + -(x / 2)) := by gcongr
    _ = 2 * M * D * Real.exp 10 * Real.exp (-(x / 2)) := by rw [Real.exp_add]; ring
    _ ≤ 1 / 2 := hj.le

/-- **Ground states with windowed content force RH.** Let `b` be a finite family of base tests,
and let `u_j` be nonzero full ground states at apertures `a_j → ∞`. If for each `j` some member
`b_i` satisfies `‖f_j‖₁ ≤ M e^{a_j} |W_{b_i}(F_j)|` at width `a_j/40`, then the ground energies stay
bounded and the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fullGrounds_windowedMass {k : ℕ}
    (b : Fin k → SuzukiSmoothCompactTest 1) {M : ℝ}
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hne : ∀ j, ccmArchimedeanFormToAperture (a j) (u j) ≠ 0)
    (hlow : ∀ j, ∃ i, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 *
        ‖windowedMass (b i) (conjTransform (timeRep (a j) (u j))) ((a j).1 / 40)‖) :
    RiemannHypothesis := by
  by_contra hRH
  have hN : ∀ j, 0 < ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ := fun j => integral_norm_timeRep_pos (hne j)
  have hM : 0 < M := by
    obtain ⟨i, hi⟩ := hlow 0
    have h1 := lt_of_lt_of_le (hN 0) hi
    by_contra h
    push Not at h
    have : M * Real.exp (a 0).1 *
        ‖windowedMass (b i) (conjTransform (timeRep (a 0) (u 0))) ((a 0).1 / 40)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le) (norm_nonneg _)
    linarith
  set C : ℝ := ∑ i, windowZeroConst (b i) with hC
  set D : ℝ := ∑ i, eigenDefectConst (b i) (1 / 2) 0 with hD
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => windowZeroConst_nonneg (b i)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => eigenDefectConst_nonneg (b i)
  have hCi : ∀ i, windowZeroConst (b i) ≤ C := fun i =>
    Finset.single_le_sum (fun i _ => windowZeroConst_nonneg (b i)) (Finset.mem_univ i)
  have hDi : ∀ i, eigenDefectConst (b i) (1 / 2) 0 ≤ D := fun i =>
    Finset.single_le_sum (fun i _ => eigenDefectConst_nonneg (b i)) (Finset.mem_univ i)
  set μ₀ : ℝ := 2 * Real.pi * (1 + C * M) with hμ₀
  have hμ₀0 : 0 ≤ μ₀ := by positivity
  obtain ⟨B, hB⟩ :=
    RHTower.WeilDeletion.exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis hRH hμ₀0
  have hsmall := eventually_lowFrequency_tail_small hM.le hD0 ha
  obtain ⟨j, hjsmall, hjlarge⟩ :=
    (hsmall.and (ha.eventually_ge_atTop (max 4 B.1))).exists
  have hj4 : 4 ≤ (a j).1 := le_trans (le_max_left _ _) hjlarge
  have hjb : B.1 ≤ (a j).1 := le_trans (le_max_right _ _) hjlarge
  obtain ⟨i, hi⟩ := hlow j
  set x : ℝ := (a j).1 with hx
  set N : ℝ := ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ with hNdef
  set Iv : ℝ := ‖windowedMass (b i) (conjTransform (timeRep (a j) (u j))) (x / 40)‖ with hIv
  have hNle : N ≤ M * Real.exp x * Iv := hi
  have hNj := hN j
  have hIv0 : 0 < Iv := by
    by_contra h
    have h0 : Iv = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0, mul_zero] at hNle
    linarith
  have hσ : 0 < x / 40 := by positivity
  have hR : 8 * (x / 40) ≤ x - 2 := by linarith
  have hI : windowedMass (b i) (conjTransform (timeRep (a j) (u j))) (x / 40) ≠ 0 :=
    norm_pos_iff.mp hIv0
  have hDi0 := eigenDefectConst_nonneg (b i)
  have hDii := hDi i
  have hsm : N * Real.exp x * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (x / 40))))) *
      eigenDefectConst (b i) (1 / 2) 0 ≤ Iv / 2 := by
    calc N * Real.exp x * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (x / 40))))) *
          eigenDefectConst (b i) (1 / 2) 0
        ≤ (M * Real.exp x * Iv) * Real.exp x * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (x / 40))))) *
          D := by gcongr
      _ = Iv * (M * Real.exp (2 * x) * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (x / 40))))) * D) := by
          rw [show 2 * x = x + x by ring, Real.exp_add]; ring
      _ ≤ Iv * (1 / 2) := by gcongr
      _ = Iv / 2 := by ring
  have hbound := abs_eigenvalue_le_of_windowedMass (b i) (a j) (u j) _
    (formEigen_of_isFullGround (a j) (hground j)) hσ hR hI hsm
  have hCi0 := windowZeroConst_nonneg (b i)
  have hCii := hCi i
  have hratio : windowZeroConst (b i) * N * Real.exp (x / 2 - 165 / 2 * (x / 40)) / Iv ≤
      C * M := by
    rw [div_le_iff₀ hIv0]
    have hexp : Real.exp (x / 2 - 165 / 2 * (x / 40)) * Real.exp x ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by linarith)
    calc windowZeroConst (b i) * N * Real.exp (x / 2 - 165 / 2 * (x / 40))
        ≤ windowZeroConst (b i) * (M * Real.exp x * Iv) *
          Real.exp (x / 2 - 165 / 2 * (x / 40)) := by gcongr
      _ = windowZeroConst (b i) * M * Iv *
          (Real.exp (x / 2 - 165 / 2 * (x / 40)) * Real.exp x) := by ring
      _ ≤ windowZeroConst (b i) * M * Iv * 1 := by gcongr
      _ ≤ C * M * Iv := by rw [mul_one]; gcongr
  have hbound' : |ccmRestrictedWeilGroundEnergy (a j)| ≤ μ₀ := by
    refine hbound.trans ?_
    rw [hμ₀]
    gcongr
  have hanti := ccmRestrictedWeilGroundEnergy_antitone hjb
  have := neg_abs_le (ccmRestrictedWeilGroundEnergy (a j))
  linarith

/-- **Ground states with low-frequency content force RH.** Let `u_j` be nonzero full ground
states at apertures `a_j → ∞`, with physical functions `f_j` and transforms `F_j`. If
`‖f_j‖₁ ≤ M e^{a_j} |I_{a_j/40}(F_j)|`, that is, the transforms keep an `e^{-a_j}` share of their
Paley–Wiener size in a window of width `≍ a_j^{-1/2}` at frequency zero, then the ground energies
stay bounded and the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fullGrounds_lowFrequencyMass {M : ℝ}
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hne : ∀ j, ccmArchimedeanFormToAperture (a j) (u j) ≠ 0)
    (hlow : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 *
        ‖lowFrequencyMass (conjTransform (timeRep (a j) (u j))) ((a j).1 / 40)‖) :
    RiemannHypothesis :=
  riemannHypothesis_of_fullGrounds_windowedMass (fun _ : Fin 1 => posBumpTest) a ha u hground hne
    fun j => ⟨0, hlow j⟩

/-- **Parity-free version.** If every nonzero full ground state has even or odd low-frequency
content of size `e^{-a_j} ‖f_j‖₁`, the Riemann hypothesis holds. The odd window uses the derivative
test, whose transform is `-iz b̂(z)`. -/
theorem riemannHypothesis_of_fullGrounds_evenOrOddWindow {M : ℝ}
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hne : ∀ j, ccmArchimedeanFormToAperture (a j) (u j) ≠ 0)
    (hlow : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤ M * Real.exp (a j).1 *
        ‖windowedMass posBumpTest (conjTransform (timeRep (a j) (u j))) ((a j).1 / 40)‖ ∨
      ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤ M * Real.exp (a j).1 *
        ‖windowedMass posBumpTest.derivTest (conjTransform (timeRep (a j) (u j))) ((a j).1 / 40)‖) :
    RiemannHypothesis :=
  riemannHypothesis_of_fullGrounds_windowedMass ![posBumpTest, posBumpTest.derivTest] a ha u
    hground hne fun j => (hlow j).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)

/-- At width `σ = cB` with `16c(1 + η) < 1`, the Gaussian tail beats `e^{(1+η)B}` for all large
apertures. -/
theorem eventually_lowFrequency_tail_small_rate {M D η c : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hc : 0 < c) (hcη : 16 * c * (1 + η) < 1) :
    ∃ B₁ : ℝ, 4 ≤ B₁ ∧ ∀ B : ℝ, B₁ ≤ B → M * Real.exp ((1 + η) * B) *
        (2 * Real.exp (-((B - 2) ^ 2 / (16 * (c * B))))) * D ≤ 1 / 2 := by
  set κ : ℝ := 1 / (16 * c) - (1 + η) with hκ
  have hκpos : 0 < κ := by
    rw [hκ, sub_pos, lt_div_iff₀ (by positivity)]
    linarith
  have hlim : Tendsto (fun B : ℝ => 2 * M * D * Real.exp (1 / (4 * c)) * Real.exp (-(κ * B)))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκpos)).const_mul (2 * M * D * Real.exp (1 / (4 * c)))
    rw [mul_zero] at h
    exact h
  obtain ⟨B₂, hB₂⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max 4 B₂, le_max_left _ _, fun B hB => ?_⟩
  have hB4 : 4 ≤ B := le_trans (le_max_left _ _) hB
  have hB0 : 0 < B := by linarith
  have hlt := hB₂ B (le_trans (le_max_right _ _) hB)
  have hexp : (1 + η) * B - (B - 2) ^ 2 / (16 * (c * B)) ≤ 1 / (4 * c) + -(κ * B) := by
    have h1 : (B - 2) ^ 2 / (16 * (c * B)) = 1 / (16 * c) * ((B - 2) ^ 2 / B) := by
      field_simp
    have h2 : B - 4 ≤ (B - 2) ^ 2 / B := by
      rw [le_div_iff₀ hB0]; nlinarith
    have h3 : 1 / (16 * c) * (B - 4) ≤ 1 / (16 * c) * ((B - 2) ^ 2 / B) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 1 / (16 * c) * 4 = 1 / (4 * c) := by field_simp; ring
    rw [h1, hκ]
    nlinarith
  calc M * Real.exp ((1 + η) * B) * (2 * Real.exp (-((B - 2) ^ 2 / (16 * (c * B))))) * D
      = 2 * M * D * Real.exp ((1 + η) * B + -((B - 2) ^ 2 / (16 * (c * B)))) := by
        rw [Real.exp_add]; ring
    _ ≤ 2 * M * D * Real.exp (1 / (4 * c) + -(κ * B)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = 2 * M * D * Real.exp (1 / (4 * c)) * Real.exp (-(κ * B)) := by rw [Real.exp_add]; ring
    _ ≤ 1 / 2 := hlt.le

/-- **The decay rate of the low-frequency share bounds the real parts of the zeros.** Suppose
that at every aperture `B ≥ B₀` some nonzero full ground state has
`‖f‖₁ ≤ M e^{ηB} |I_{cB}(F)|`, with `η ≥ 0`, `c > 0` and `16c(1 + η) < 1`. Then every Xi zero
satisfies `|Re ρ - 1/2| ≤ max 0 (η + 1/2 - 165c/2) / 2`. When `η + 1/2 < 165c/2`, this is RH.

The ground energies satisfy `μ_B ≥ -C e^{εB}`, `ε = max 0 (η + 1/2 - 165c/2)`, and the sharp
Bombieri–Yoshida cap converts exponential lower bounds of rate `ε` into the strip `ε/2`. -/
theorem abs_im_xiSpectralPoint_le_of_fullGrounds_lowFrequencyMass {M η c B₀ : ℝ}
    (hη : 0 ≤ η) (hc : 0 < c) (hcη : 16 * c * (1 + η) < 1)
    (hlow : ∀ B : SuzukiPositiveAperture, B₀ ≤ B.1 → ∃ u : CCMArchimedeanFormDomain B,
      IsFullGround B u ∧ ccmArchimedeanFormToAperture B u ≠ 0 ∧
        ∫ t : ℝ, ‖timeRep B u t‖ ≤
          M * Real.exp (η * B.1) * ‖lowFrequencyMass (conjTransform (timeRep B u)) (c * B.1)‖)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ max 0 (η + 1 / 2 - 165 / 2 * c) / 2 := by
  set ε : ℝ := max 0 (η + 1 / 2 - 165 / 2 * c) with hεdef
  have hε0 : 0 ≤ ε := le_max_left _ _
  have hεge : η + 1 / 2 - 165 / 2 * c ≤ ε := le_max_right _ _
  -- `M ≥ 0`, read off at one aperture
  set A₀ : SuzukiPositiveAperture := ⟨max 1 B₀, lt_of_lt_of_le one_pos (le_max_left _ _)⟩
    with hA₀
  have hM : 0 ≤ M := by
    obtain ⟨u, -, hne, hle⟩ := hlow A₀ (le_max_right _ _)
    have hN := integral_norm_timeRep_pos hne
    have h1 := lt_of_lt_of_le hN hle
    by_contra h
    push Not at h
    have : M * Real.exp (η * A₀.1) *
        ‖lowFrequencyMass (conjTransform (timeRep A₀ u)) (c * A₀.1)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg h.le (Real.exp_pos _).le) (norm_nonneg _)
    linarith
  have hD0 := eigenDefectConst_posBumpTest_nonneg
  have hC0 := lowFrequencyZeroConst_nonneg
  obtain ⟨B₁, hB₁4, hB₁⟩ := eventually_lowFrequency_tail_small_rate hM hD0 hc hcη
  set K₁ : ℝ := 2 * Real.pi * (1 + lowFrequencyZeroConst * M) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- the bound at every large aperture
  have hlarge : ∀ B : SuzukiPositiveAperture, max B₀ B₁ ≤ B.1 →
      -(K₁ * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilGroundEnergy B := by
    intro B hB
    have hBB₀ : B₀ ≤ B.1 := le_trans (le_max_left _ _) hB
    have hBB₁ : B₁ ≤ B.1 := le_trans (le_max_right _ _) hB
    have hB4 : 4 ≤ B.1 := le_trans hB₁4 hBB₁
    obtain ⟨u, hground, hne, hle⟩ := hlow B hBB₀
    set x : ℝ := B.1 with hx
    set N : ℝ := ∫ t : ℝ, ‖timeRep B u t‖ with hNdef
    set Iv : ℝ := ‖lowFrequencyMass (conjTransform (timeRep B u)) (c * x)‖ with hIv
    have hN := integral_norm_timeRep_pos hne
    have hIv0 : 0 < Iv := by
      by_contra h
      have h0 : Iv = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [h0, mul_zero] at hle
      linarith
    have hσ : 0 < c * x := by positivity
    have hc16 : c < 1 / 16 := by nlinarith
    have hR : 8 * (c * x) ≤ x - 2 := by nlinarith
    have hI : lowFrequencyMass (conjTransform (timeRep B u)) (c * x) ≠ 0 := norm_pos_iff.mp hIv0
    have hsm : N * Real.exp x * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (c * x))))) *
        eigenDefectConst posBumpTest (1 / 2) 0 ≤ Iv / 2 := by
      have htail := hB₁ x hBB₁
      calc N * Real.exp x * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (c * x))))) *
            eigenDefectConst posBumpTest (1 / 2) 0
          ≤ (M * Real.exp (η * x) * Iv) * Real.exp x *
            (2 * Real.exp (-((x - 2) ^ 2 / (16 * (c * x))))) *
            eigenDefectConst posBumpTest (1 / 2) 0 := by gcongr
        _ = Iv * (M * Real.exp ((1 + η) * x) * (2 * Real.exp (-((x - 2) ^ 2 / (16 * (c * x))))) *
            eigenDefectConst posBumpTest (1 / 2) 0) := by
            rw [show (1 + η) * x = η * x + x by ring, Real.exp_add]; ring
        _ ≤ Iv * (1 / 2) := by gcongr
        _ = Iv / 2 := by ring
    have hbound := abs_eigenvalue_le_of_lowFrequencyMass B u _
      (formEigen_of_isFullGround B hground) hσ hR hI hsm
    have hratio : lowFrequencyZeroConst * N * Real.exp (x / 2 - 165 / 2 * (c * x)) / Iv ≤
        lowFrequencyZeroConst * M * Real.exp (ε * x) := by
      rw [div_le_iff₀ hIv0]
      have hexp : Real.exp (x / 2 - 165 / 2 * (c * x)) * Real.exp (η * x) ≤ Real.exp (ε * x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hx0 : 0 ≤ x := by linarith
        nlinarith
      calc lowFrequencyZeroConst * N * Real.exp (x / 2 - 165 / 2 * (c * x))
          ≤ lowFrequencyZeroConst * (M * Real.exp (η * x) * Iv) *
            Real.exp (x / 2 - 165 / 2 * (c * x)) := by gcongr
        _ = lowFrequencyZeroConst * M * Iv *
            (Real.exp (x / 2 - 165 / 2 * (c * x)) * Real.exp (η * x)) := by ring
        _ ≤ lowFrequencyZeroConst * M * Iv * Real.exp (ε * x) := by gcongr
        _ = lowFrequencyZeroConst * M * Real.exp (ε * x) * Iv := by ring
    have hone : 1 ≤ Real.exp (ε * x) := Real.one_le_exp (by positivity)
    have hfin : |ccmRestrictedWeilGroundEnergy B| ≤ K₁ * Real.exp (ε * x) := by
      refine hbound.trans ?_
      rw [hK₁]
      have hCM : 0 ≤ lowFrequencyZeroConst * M := by positivity
      nlinarith
    have := neg_abs_le (ccmRestrictedWeilGroundEnergy B)
    linarith
  -- every aperture, through antitonicity
  set A₁ : SuzukiPositiveAperture := ⟨max B₀ B₁, lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
    with hA₁
  set C : ℝ := K₁ * Real.exp (ε * A₁.1) with hC
  have hC0 : 0 ≤ C := by positivity
  apply abs_im_xiSpectralPoint_le_half_of_polarGroundEnergy_ge hC0 hε0 _ q
  intro B
  refine le_trans ?_ (ccmRestrictedWeilGroundEnergy_le_polar B)
  have hexpB : 1 ≤ Real.exp (ε * B.1) := Real.one_le_exp (mul_nonneg hε0 B.2.le)
  rcases le_or_gt A₁.1 B.1 with hB | hB
  · have h1 := hlarge B hB
    have hA1 : 1 ≤ Real.exp (ε * A₁.1) := Real.one_le_exp (mul_nonneg hε0 A₁.2.le)
    have : K₁ * Real.exp (ε * B.1) ≤ C * Real.exp (ε * B.1) := by
      rw [hC]
      calc K₁ * Real.exp (ε * B.1) = K₁ * 1 * Real.exp (ε * B.1) := by ring
        _ ≤ K₁ * Real.exp (ε * A₁.1) * Real.exp (ε * B.1) := by gcongr
    linarith
  · have h1 := hlarge A₁ le_rfl
    have hanti := ccmRestrictedWeilGroundEnergy_antitone (a := B) (b := A₁) hB.le
    have : C ≤ C * Real.exp (ε * B.1) := le_mul_of_one_le_right hC0 hexpB
    linarith

end Eigen

end

end RHTower
