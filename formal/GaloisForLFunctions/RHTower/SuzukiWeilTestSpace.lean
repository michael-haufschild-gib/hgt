import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity
import GaloisForLFunctions.RHTower.SuzukiWeilNormDefiniteness
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv

noncomputable section

/-!
# The test space and the Weil hermitian form

The corpus's test functions are indexed by an aperture, so they do not form a vector space.  Here
they are collected into the submodule of all smooth compactly supported functions, on which the Weil
hermitian form of the source becomes a genuine sesquilinear form.

Under the Riemann hypothesis every Xi zero is real, so the form is the spectral sum
`⟪ψ, φ⟫_W = Σ_q conj(ψ̂(-γ_q)) φ̂(-γ_q)`, which makes positivity immediate.  Definiteness is the
source's Lemma 3.2 in its sharpest form: `ψ̂` is entire of exponential type — the Paley--Wiener bound
for a compactly supported amplitude — and vanishes at every Xi zero, so Suzuki's uniqueness lemma
makes it identically zero, and the compact Fourier transform is injective.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The space of smooth compactly supported test functions on the line, as a submodule of all
functions.  Unlike the aperture-indexed `SuzukiSmoothCompactTest`, this is a vector space. -/
def suzukiTestSubmodule : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contDiff_const, by simpa using HasCompactSupport.zero (α := ℝ) (β := ℂ)⟩
  smul_mem' := fun c _ hf => ⟨hf.1.const_smul c, hf.2.smul_left⟩

/-- Smooth compactly supported test functions on the line. -/
abbrev SuzukiTest := ↥suzukiTestSubmodule

theorem SuzukiTest.smooth (ψ : SuzukiTest) : ContDiff ℝ (⊤ : ℕ∞) (ψ : ℝ → ℂ) := ψ.2.1

theorem SuzukiTest.hasCompactSupport (ψ : SuzukiTest) :
    HasCompactSupport (ψ : ℝ → ℂ) := ψ.2.2

theorem SuzukiTest.continuous (ψ : SuzukiTest) : Continuous (ψ : ℝ → ℂ) :=
  ψ.smooth.continuous

/-- Every test function has an aperture. -/
theorem SuzukiTest.exists_aperture (ψ : SuzukiTest) :
    ∃ a : ℝ, 0 < a ∧ Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a := by
  have hcomp := ψ.hasCompactSupport
  have hbdd : Bornology.IsBounded (tsupport (ψ : ℝ → ℂ)) := hcomp.isBounded
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, ?_⟩
  intro x hx
  have hxt : x ∈ tsupport (ψ : ℝ → ℂ) := subset_tsupport _ hx
  have hxb := hR hxt
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxb
  have h1 : |x| ≤ |R| := le_trans hxb (le_abs_self R)
  constructor
  · have := abs_le.mp h1
    linarith [this.1]
  · have := abs_le.mp h1
    linarith [this.2]

/-- A test function realized at a given aperture. -/
def SuzukiTest.toCompactTest (ψ : SuzukiTest) {a : ℝ}
    (h : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a) : SuzukiSmoothCompactTest a where
  toFun := (ψ : ℝ → ℂ)
  smooth := ψ.smooth
  support_subset := h

@[simp] theorem SuzukiTest.coe_toCompactTest (ψ : SuzukiTest) {a : ℝ}
    (h : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a) :
    ((ψ.toCompactTest h : SuzukiSmoothCompactTest a) : ℝ → ℂ) = (ψ : ℝ → ℂ) := rfl

/-! ## The Weil hermitian form on the test space -/

/-- Suzuki's Hermitian convolution written on raw functions. -/
def suzukiRawHermitianConvolution (ψ₁ ψ₂ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, ψ₁ y * (starRingEnd ℂ) (ψ₂ (-(x - y)))

theorem suzukiRawHermitianConvolution_eq {a : ℝ} (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    suzukiRawHermitianConvolution (ψ₁ : ℝ → ℂ) (ψ₂ : ℝ → ℂ)
      = suzukiHermitianConvolution ψ₁ ψ₂ := rfl

/-- **The Weil hermitian form**, conjugate-linear in the first slot. -/
def suzukiWeilInner (ψ φ : SuzukiTest) : ℂ :=
  suzukiWeilDistribution (suzukiRawHermitianConvolution (φ : ℝ → ℂ) (ψ : ℝ → ℂ))

/-- The value of the Fourier transform of a test function at a spectral point. -/
def suzukiTestFourier (ψ : SuzukiTest) (q : XiZeroCopy) : ℂ :=
  suzukiEntireFourier (ψ : ℝ → ℂ) (-xiSpectralPoint q)

theorem exists_common_aperture (ψ φ : SuzukiTest) :
    ∃ c : ℝ, 0 ≤ c ∧ Function.support (ψ : ℝ → ℂ) ⊆ Icc (-c) c
      ∧ Function.support (φ : ℝ → ℂ) ⊆ Icc (-c) c := by
  obtain ⟨a, ha, hψ⟩ := ψ.exists_aperture
  obtain ⟨b, hb, hφ⟩ := φ.exists_aperture
  refine ⟨max a b, le_trans ha.le (le_max_left a b), ?_, ?_⟩
  · exact hψ.trans (Icc_subset_Icc (neg_le_neg (le_max_left a b)) (le_max_left a b))
  · exact hφ.trans (Icc_subset_Icc (neg_le_neg (le_max_right a b)) (le_max_right a b))

theorem suzukiEntireFourier_hermitianConvolution_spectral (hRH : RiemannHypothesis) {c : ℝ}
    (hc : 0 ≤ c) (Φ Ψ : SuzukiSmoothCompactTest c) (q : XiZeroCopy) :
    suzukiEntireFourier (suzukiHermitianConvolution Φ Ψ) (-xiSpectralPoint q)
      = (starRingEnd ℂ) (suzukiEntireFourier (Ψ : ℝ → ℂ) (-xiSpectralPoint q))
        * suzukiEntireFourier (Φ : ℝ → ℂ) (-xiSpectralPoint q) := by
  have hreal : xiSpectralPoint q = ((xiRealSpectralPoint q : ℝ) : ℂ) :=
    xiSpectralPoint_eq_ofReal_of_rh hRH q
  rw [suzukiEntireFourier_hermitianConvolution hc]
  have hconj : suzukiSmoothFourier Ψ.conjugate (xiSpectralPoint q)
      = (starRingEnd ℂ) (suzukiEntireFourier (Ψ : ℝ → ℂ) (-xiSpectralPoint q)) := by
    rw [suzukiEntireFourier, suzukiSmoothFourier, ← integral_conj]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [map_mul, ← Complex.exp_conj]
    have hexp : (starRingEnd ℂ) (I * (-xiSpectralPoint q) * (x : ℂ))
        = I * xiSpectralPoint q * (x : ℂ) := by
      rw [hreal]
      simp
    rw [hexp]
    rfl
  rw [neg_neg, hconj]
  show suzukiEntireFourier (Φ : ℝ → ℂ) (-xiSpectralPoint q)
      * (starRingEnd ℂ) (suzukiEntireFourier (Ψ : ℝ → ℂ) (-xiSpectralPoint q))
    = (starRingEnd ℂ) (suzukiEntireFourier (Ψ : ℝ → ℂ) (-xiSpectralPoint q))
      * suzukiEntireFourier (Φ : ℝ → ℂ) (-xiSpectralPoint q)
  ring

theorem suzukiWeilInner_eq_tsum (hRH : RiemannHypothesis) (ψ φ : SuzukiTest) :
    suzukiWeilInner ψ φ
      = ∑' q : XiZeroCopy, (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier φ q := by
  obtain ⟨c, hc, hψc, hφc⟩ := exists_common_aperture ψ φ
  have hval : suzukiWeilInner ψ φ
      = suzukiWeilDistribution
        (suzukiHermitianConvolution (φ.toCompactTest hφc) (ψ.toCompactTest hψc)) := rfl
  rw [hval, suzukiWeilDistribution]
  refine tsum_congr fun q => ?_
  exact suzukiEntireFourier_hermitianConvolution_spectral hRH hc _ _ q

theorem summable_suzukiWeilInner (hRH : RiemannHypothesis) (ψ φ : SuzukiTest) :
    Summable (fun q : XiZeroCopy =>
      (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier φ q) := by
  obtain ⟨c, hc, hψc, hφc⟩ := exists_common_aperture ψ φ
  have hbase := summable_suzukiWeilDistribution_hermitianConvolution hc
    (φ.toCompactTest hφc) (ψ.toCompactTest hψc)
  refine hbase.congr fun q => ?_
  exact suzukiEntireFourier_hermitianConvolution_spectral hRH hc _ _ q

theorem hasSum_suzukiWeilInner (hRH : RiemannHypothesis) (ψ φ : SuzukiTest) :
    HasSum (fun q : XiZeroCopy =>
        (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier φ q)
      (suzukiWeilInner ψ φ) := by
  rw [suzukiWeilInner_eq_tsum hRH]
  exact (summable_suzukiWeilInner hRH ψ φ).hasSum


/-! ## Definiteness of the Weil form -/

open GaloisForLFunctions.HTGeometry in
theorem suzukiEntireFourier_eq_compactFourier {a : ℝ} (ha : 0 ≤ a) {ψ : ℝ → ℂ}
    (_hcont : Continuous ψ) (hsupp : Function.support ψ ⊆ Icc (-a) a) (z : ℂ) :
    suzukiEntireFourier ψ z = compactFourier ψ (-a) a z := by
  have hab : -a ≤ a := by linarith
  rw [compactFourier, intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, suzukiEntireFourier]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-a) a) (f := fun x : ℝ => ψ x * Complex.exp (I * z * (x : ℂ)))
    (fun x hx => by
      have hz : ψ x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [hz, zero_mul])]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [mul_assoc]

theorem xi_eq_XiC_neg (z : ℂ) : xi (1 / 2 - I * z) = XiC (-z) := by
  rw [xi_eq_XiC_comp]
  congr 1
  linear_combination z * Complex.I_sq

open GaloisForLFunctions.HTGeometry in
/-- **Definiteness of the Weil form.**  A test function whose Fourier transform vanishes at every
Xi zero vanishes: the transform is entire of exponential type, so Suzuki's uniqueness lemma makes
it identically zero, and the compact Fourier transform is injective. -/
theorem eq_zero_of_suzukiTestFourier_eq_zero {ψ : SuzukiTest}
    (h : ∀ q : XiZeroCopy, suzukiTestFourier ψ q = 0) : ψ = 0 := by
  obtain ⟨a, ha, hsupp⟩ := ψ.exists_aperture
  have hcont : Continuous (ψ : ℝ → ℂ) := ψ.continuous
  have hab : -a ≤ a := by linarith
  have hint : IntervalIntegrable (ψ : ℝ → ℂ) volume (-a) a := hcont.intervalIntegrable _ _
  have hFdiff : Differentiable ℂ (suzukiEntireFourier (ψ : ℝ → ℂ)) := by
    have hd := differentiable_compactFourier_of_integrable hint
    intro z
    refine (hd z).congr_of_eventuallyEq ?_
    filter_upwards with w
    exact suzukiEntireFourier_eq_compactFourier ha.le hcont hsupp w
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := -a) (b := a)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hMbound : ∀ x ∈ Set.uIoc (-a) a, ‖(ψ : ℝ → ℂ) x‖ ≤ M := by
    intro x hx
    exact hM x (Set.uIoc_subset_uIcc hx)
  have hM0 : 0 ≤ M := by
    have := hMbound 0 (by
      rw [Set.uIoc_of_le hab]
      exact ⟨by linarith, by linarith⟩)
    exact le_trans (norm_nonneg _) this
  have hgrow : ∀ z : ℂ, ‖suzukiEntireFourier (ψ : ℝ → ℂ) z‖
      ≤ (M * (a - -a) + 1) * Real.exp (max |(-a)| |a| * ‖z‖) := by
    intro z
    rw [suzukiEntireFourier_eq_compactFourier ha.le hcont hsupp]
    have hbase := norm_compactFourier_le hab hMbound z
    have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hmax : (0 : ℝ) ≤ max |(-a)| |a| := le_trans (abs_nonneg _) (le_max_left _ _)
    have hexp : Real.exp (max |(-a)| |a| * |z.im|)
        ≤ Real.exp (max |(-a)| |a| * ‖z‖) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_left hzim hmax
    calc ‖compactFourier (ψ : ℝ → ℂ) (-a) a z‖
        ≤ M * Real.exp (max |(-a)| |a| * |z.im|) * (a - -a) := hbase
      _ = (M * (a - -a)) * Real.exp (max |(-a)| |a| * |z.im|) := by ring
      _ ≤ (M * (a - -a) + 1) * Real.exp (max |(-a)| |a| * ‖z‖) := by
          have h1 : (0 : ℝ) ≤ M * (a - -a) := by nlinarith
          have h2 := Real.exp_pos (max |(-a)| |a| * |z.im|)
          nlinarith [Real.exp_pos (max |(-a)| |a| * ‖z‖)]
  have hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 → suzukiEntireFourier (ψ : ℝ → ℂ) z = 0 := by
    intro z hz
    rw [xi_eq_XiC_neg] at hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (-z)).mp hz
    have hzq : z = -xiSpectralPoint q := by
      rw [hq]
      ring
    rw [hzq]
    exact h q
  have hzero := suzuki_lemma_two_one hFdiff 0
    ⟨max |(-a)| |a|, M * (a - -a) + 1, le_trans (abs_nonneg _) (le_max_left _ _),
      by nlinarith, hgrow⟩ hvalues
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))),
      compactFourier (ψ : ℝ → ℂ) (-a) a ((t : ℝ) : ℂ) = 0 := by
    filter_upwards with t
    rw [← suzukiEntireFourier_eq_compactFourier ha.le hcont hsupp]
    exact congrFun hzero _
  have hpsi : (ψ : ℝ → ℂ) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_compactFourier_vanishing hab ?_ ?_ one_pos hae
    · exact hcont.integrable_of_hasCompactSupport ψ.hasCompactSupport
    · intro x hx
      by_contra hne
      exact hx (hsupp hne)
  have hfun : (ψ : ℝ → ℂ) = 0 := by
    funext x
    have hax : ∀ᵐ y : ℝ, (ψ : ℝ → ℂ) y = 0 := by
      filter_upwards [hpsi] with y hy
      exact hy
    exact eq_zero_of_ae_zero_of_continuousAt hax hcont.continuousAt
  exact Subtype.ext hfun


/-! ## Linearity, symmetry, positivity -/

theorem integrable_suzukiTestIntegrand (ψ : SuzukiTest) (z : ℂ) :
    Integrable (fun x : ℝ => (ψ : ℝ → ℂ) x * Complex.exp (I * z * (x : ℂ))) := by
  have hcont : Continuous fun x : ℝ => (ψ : ℝ → ℂ) x * Complex.exp (I * z * (x : ℂ)) := by
    exact ψ.continuous.mul (Complex.continuous_exp.comp (by fun_prop))
  refine hcont.integrable_of_hasCompactSupport ?_
  exact ψ.hasCompactSupport.mul_right

theorem suzukiTestFourier_add (ψ φ : SuzukiTest) (q : XiZeroCopy) :
    suzukiTestFourier (ψ + φ) q = suzukiTestFourier ψ q + suzukiTestFourier φ q := by
  simp only [suzukiTestFourier, suzukiEntireFourier]
  rw [← MeasureTheory.integral_add (integrable_suzukiTestIntegrand ψ _)
    (integrable_suzukiTestIntegrand φ _)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show ((ψ : ℝ → ℂ) x + (φ : ℝ → ℂ) x) * Complex.exp (I * (-xiSpectralPoint q) * (x : ℂ))
    = (ψ : ℝ → ℂ) x * Complex.exp (I * (-xiSpectralPoint q) * (x : ℂ))
      + (φ : ℝ → ℂ) x * Complex.exp (I * (-xiSpectralPoint q) * (x : ℂ))
  ring

theorem suzukiTestFourier_smul (c : ℂ) (ψ : SuzukiTest) (q : XiZeroCopy) :
    suzukiTestFourier (c • ψ) q = c * suzukiTestFourier ψ q := by
  simp only [suzukiTestFourier, suzukiEntireFourier]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  show c * (ψ : ℝ → ℂ) x * Complex.exp (I * (-xiSpectralPoint q) * (x : ℂ))
    = c * ((ψ : ℝ → ℂ) x * Complex.exp (I * (-xiSpectralPoint q) * (x : ℂ)))
  ring

theorem suzukiWeilInner_add_left (hRH : RiemannHypothesis) (ψ φ χ : SuzukiTest) :
    suzukiWeilInner (ψ + φ) χ = suzukiWeilInner ψ χ + suzukiWeilInner φ χ := by
  have h1 := hasSum_suzukiWeilInner hRH ψ χ
  have h2 := hasSum_suzukiWeilInner hRH φ χ
  have hsum := h1.add h2
  refine (HasSum.unique ?_ hsum)
  refine (hasSum_suzukiWeilInner hRH (ψ + φ) χ).congr_fun ?_
  intro q
  rw [suzukiTestFourier_add, map_add]
  ring

theorem suzukiWeilInner_smul_left (hRH : RiemannHypothesis) (c : ℂ) (ψ φ : SuzukiTest) :
    suzukiWeilInner (c • ψ) φ = (starRingEnd ℂ) c * suzukiWeilInner ψ φ := by
  have h1 := (hasSum_suzukiWeilInner hRH ψ φ).mul_left ((starRingEnd ℂ) c)
  refine (HasSum.unique ?_ h1)
  refine (hasSum_suzukiWeilInner hRH (c • ψ) φ).congr_fun ?_
  intro q
  rw [suzukiTestFourier_smul, map_mul]
  ring

theorem suzukiWeilInner_conj_symm (hRH : RiemannHypothesis) (ψ φ : SuzukiTest) :
    (starRingEnd ℂ) (suzukiWeilInner φ ψ) = suzukiWeilInner ψ φ := by
  have h1 := (hasSum_suzukiWeilInner hRH φ ψ).map (starRingEnd ℂ)
    Complex.continuous_conj
  have h2 : HasSum (fun q : XiZeroCopy =>
      (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier φ q)
      ((starRingEnd ℂ) (suzukiWeilInner φ ψ)) := by
    refine h1.congr_fun ?_
    intro q
    show (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier φ q
      = (starRingEnd ℂ) ((starRingEnd ℂ) (suzukiTestFourier φ q) * suzukiTestFourier ψ q)
    rw [map_mul, Complex.conj_conj]
    ring
  exact HasSum.unique h2 (hasSum_suzukiWeilInner hRH ψ φ)

theorem hasSum_normSq_suzukiTestFourier (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    HasSum (fun q : XiZeroCopy => ‖suzukiTestFourier ψ q‖ ^ 2)
      ((suzukiWeilInner ψ ψ).re) := by
  have h := hasSum_suzukiWeilInner hRH ψ ψ
  have hre := Complex.hasSum_re h
  refine hre.congr_fun ?_
  intro q
  rw [show (starRingEnd ℂ) (suzukiTestFourier ψ q) * suzukiTestFourier ψ q
      = ((‖suzukiTestFourier ψ q‖ ^ 2 : ℝ) : ℂ) by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
  exact (Complex.ofReal_re _).symm

theorem re_suzukiWeilInner_self_nonneg (hRH : RiemannHypothesis) (ψ : SuzukiTest) :
    0 ≤ (suzukiWeilInner ψ ψ).re :=
  (hasSum_normSq_suzukiTestFourier hRH ψ).nonneg fun q => by positivity

theorem suzukiWeilInner_self_eq_zero (hRH : RiemannHypothesis) {ψ : SuzukiTest}
    (h : suzukiWeilInner ψ ψ = 0) : ψ = 0 := by
  have hsum := hasSum_normSq_suzukiTestFourier hRH ψ
  rw [h] at hsum
  simp only [Complex.zero_re] at hsum
  refine eq_zero_of_suzukiTestFourier_eq_zero ?_
  intro q
  have h0 : ‖suzukiTestFourier ψ q‖ ^ 2 ≤ 0 :=
    le_hasSum hsum q (fun r _ => by positivity)
  have : ‖suzukiTestFourier ψ q‖ = 0 := by nlinarith [norm_nonneg (suzukiTestFourier ψ q)]
  exact norm_eq_zero.mp this


end RHTower
