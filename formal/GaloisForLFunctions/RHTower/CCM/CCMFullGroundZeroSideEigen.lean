import GaloisForLFunctions.RHTower.XiRealRootedEigenLimitRH
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFullFormRealRootedGround
import Zeta23.ExplicitFormula
import GaloisForLFunctions.RHTower.ChronologicalLeastNormMomentRepair

/-!
# The zero-side Euler–Lagrange equation of the full restricted Weil form

A ground state `u` of the unconstrained restricted Weil form at aperture `a` satisfies, for every
smooth interior source `v`,

`∑_q G_u(γ_q) v̂(-γ_q) = (μ_a / 2π) ∫_ℝ G_u(σ) v̂(-σ) dσ`,

where `μ_a` is the ground energy, `G_u(z) = ∫ conj(u(t)) e^{izt} dt` is the transform of the conjugate
physical function, `v̂(z) = ∫ v(t) e^{izt} dt`, and `γ_q` are the centered Xi zeros with multiplicity.

**Proof.**
* Euler–Lagrange: the form `Q - μ_a ⟨J·, J·⟩` is Hermitian and nonnegative, and vanishes on the
  diagonal at `u`, so `Q(u, v) = μ_a ⟨Ju, Jv⟩` for every `v`.
* The explicit formula on smooth sources (Suzuki's Proposition 3.1 through the CCM bridge) extends
  to every form-domain vector. Both sides are inner products of `Ju` with fixed `L²` vectors (a
  Plancherel representation of the archimedean term and a convergent sum of exponentials). Their
  difference is orthogonal to every smooth real test inside the aperture, hence vanishes there.
* Parseval in the convention `ĥ(z) = ∫ h(t) e^{izt} dt` converts `⟨Ju, Jv⟩` into the right side.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped InnerProduct FourierTransform ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower.CCMFullGroundEigen

open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

variable (a : SuzukiPositiveAperture)

/-! ## Euler–Lagrange for full ground states -/

/-- The ground-energy-shifted restricted Weil form. -/
def shiftedForm (u v : CCMArchimedeanFormDomain a) : ℂ :=
  ccmRestrictedWeilForm a u v -
    (ccmRestrictedWeilGroundEnergy a : ℂ) *
      inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)

theorem shiftedForm_add_right (u v w : CCMArchimedeanFormDomain a) :
    shiftedForm a u (v + w) = shiftedForm a u v + shiftedForm a u w := by
  simp only [shiftedForm, ccmRestrictedWeilForm, map_add, inner_add_right]
  ring

theorem shiftedForm_add_left (u v w : CCMArchimedeanFormDomain a) :
    shiftedForm a (u + v) w = shiftedForm a u w + shiftedForm a v w := by
  simp only [shiftedForm, ccmRestrictedWeilForm, map_add, inner_add_left]
  ring

theorem shiftedForm_smul_right (u v : CCMArchimedeanFormDomain a) (c : ℂ) :
    shiftedForm a u (c • v) = c * shiftedForm a u v := by
  simp [shiftedForm, ccmRestrictedWeilForm, map_smul]
  ring

theorem shiftedForm_smul_left (u v : CCMArchimedeanFormDomain a) (c : ℂ) :
    shiftedForm a (c • u) v = (starRingEnd ℂ) c * shiftedForm a u v := by
  simp [shiftedForm, ccmRestrictedWeilForm, map_smul]
  ring

theorem shiftedForm_conj (u v : CCMArchimedeanFormDomain a) :
    shiftedForm a v u = (starRingEnd ℂ) (shiftedForm a u v) := by
  simp only [shiftedForm, ccmRestrictedWeilForm, map_sub, map_add, map_mul, Complex.conj_ofReal]
  have h1 : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have h2 : inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a v))
      (ccmArchimedeanFormToAperture a u) =
      (starRingEnd ℂ) (inner ℂ (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v)) := by
    rw [inner_conj_symm (ccmArchimedeanFormToAperture a v)
      (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))]
    exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric _ _
  have h3 : inner ℂ (ccmArchimedeanFormToAperture a v) (ccmArchimedeanFormToAperture a u) =
      (starRingEnd ℂ) (inner ℂ (ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a v)) :=
    (inner_conj_symm (ccmArchimedeanFormToAperture a v) (ccmArchimedeanFormToAperture a u)).symm
  rw [h1, h2, h3]

theorem shiftedForm_self_re_nonneg (v : CCMArchimedeanFormDomain a) :
    0 ≤ (shiftedForm a v v).re := by
  have hlow := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v
  rw [← ccmRestrictedWeilForm_self_re_eq_source] at hlow
  have hJ : (inner ℂ (ccmArchimedeanFormToAperture a v) (ccmArchimedeanFormToAperture a v)).re =
      ‖ccmArchimedeanFormToAperture a v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a v)]
    norm_cast
  simp only [shiftedForm, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hJ]
  linarith

theorem shiftedForm_self_re_eq_zero {u : CCMArchimedeanFormDomain a} (hu : IsFullGround a u) :
    (shiftedForm a u u).re = 0 := by
  unfold IsFullGround at hu
  have hJ : (inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a u)).re =
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a u)]
    norm_cast
  simp only [shiftedForm, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hJ,
    ccmRestrictedWeilForm_self_re_eq_source, hu]
  ring

/-- **Euler–Lagrange equation of a full ground state.** -/
theorem shiftedForm_eq_zero_of_isFullGround {u : CCMArchimedeanFormDomain a}
    (hu : IsFullGround a u) (v : CCMArchimedeanFormDomain a) : shiftedForm a u v = 0 := by
  have hu0 := shiftedForm_self_re_eq_zero a hu
  -- expansion along a complex direction
  have hexp : ∀ (w : CCMArchimedeanFormDomain a) (t : ℝ),
      (shiftedForm a (u + (t : ℂ) • w) (u + (t : ℂ) • w)).re =
        2 * t * (shiftedForm a u w).re + t ^ 2 * (shiftedForm a w w).re := by
    intro w t
    rw [shiftedForm_add_left, shiftedForm_add_right, shiftedForm_add_right,
      shiftedForm_smul_left, shiftedForm_smul_left, shiftedForm_smul_right,
      shiftedForm_smul_right, shiftedForm_conj a u w]
    simp only [add_re, mul_re, Complex.conj_ofReal, ofReal_re, ofReal_im, zero_mul, sub_zero,
      conj_re, conj_im, hu0]
    ring
  have hre : ∀ w : CCMArchimedeanFormDomain a, (shiftedForm a u w).re = 0 := by
    intro w
    apply RHTower.eq_zero_of_forall_quadratic_nonneg (shiftedForm_self_re_nonneg a w)
    intro t
    rw [← hexp]
    exact shiftedForm_self_re_nonneg a _
  apply Complex.ext
  · exact hre v
  · have h := hre (I • v)
    rw [shiftedForm_smul_right] at h
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_eq_zero] at h
    simpa using h

/-! ## The zero kernel of a smooth test -/

/-- The zero kernel `t ↦ ∑_q ŵ(-γ_q) e^{iγ_q t}` of a smooth compact test. -/
def zeroKernel {b : ℝ} (w : SuzukiSmoothCompactTest b) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, suzukiSmoothFourier w (-xiSpectralPoint q) *
    cexp (I * xiSpectralPoint q * (t : ℂ))

theorem norm_cexp_I_mul_xiSpectralPoint_le (q : XiZeroCopy) (t : ℝ) :
    ‖cexp (I * xiSpectralPoint q * (t : ℂ))‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (I * xiSpectralPoint q * (t : ℂ)).re = -((xiSpectralPoint q).im * t) := by
    simp [mul_re, mul_im]
  rw [hre]
  have him := xiSpectralPoint_im_mem_openHalf q
  have habs : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [him.1, him.2]
  calc -((xiSpectralPoint q).im * t) ≤ |(xiSpectralPoint q).im * t| := neg_le_abs _
    _ = |(xiSpectralPoint q).im| * |t| := abs_mul _ _
    _ ≤ (1 / 2) * |t| := by gcongr
    _ = |t| / 2 := by ring

/-- The test coefficients at the zeros are absolutely summable. -/
theorem summable_norm_suzukiSmoothFourier_neg {b : ℝ} (w : SuzukiSmoothCompactTest b) :
    Summable fun q : XiZeroCopy => ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (suzukiTestDecayConst w (1 / 2) * 2))
  have him := xiSpectralPoint_im_mem_openHalf q
  have habs : |(-xiSpectralPoint q).im| ≤ 1 / 2 := by
    rw [neg_im, abs_neg, abs_le]; constructor <;> linarith [him.1, him.2]
  have hb := norm_suzukiSmoothFourier_le_div w (by norm_num : (0 : ℝ) ≤ 1 / 2) habs
  have hq0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
  have hK := suzukiTestDecayConst_nonneg w (1 / 2)
  rw [norm_neg] at hb
  calc ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖
      ≤ suzukiTestDecayConst w (1 / 2) / (1 + ‖xiSpectralPoint q‖ ^ 2) := hb
    _ ≤ suzukiTestDecayConst w (1 / 2) * 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * (1 + ‖xiSpectralPoint q‖ ^ 2) ≥ 1 := by
          rw [one_div, ← div_eq_inv_mul, ge_iff_le, le_div_iff₀ hpos]
          linarith
        nlinarith

/-- **Interchange.** For an integrable `f` supported in `[-A, A]`, the zero sum of its conjugate
transform against a test is the integral of `conj f` against the zero kernel. -/
theorem tsum_mul_integral_eq_integral_zeroKernel {b A : ℝ} (w : SuzukiSmoothCompactTest b)
    {f : ℝ → ℂ} (hf : Integrable f) (hsupp : ∀ t, f t ≠ 0 → |t| ≤ A) :
    ∑' q : XiZeroCopy, suzukiSmoothFourier w (-xiSpectralPoint q) *
        ∫ t : ℝ, (starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)) =
      ∫ t : ℝ, (starRingEnd ℂ) (f t) * zeroKernel w t := by
  have hterm : ∀ (q : XiZeroCopy) (t : ℝ),
      ‖suzukiSmoothFourier w (-xiSpectralPoint q) *
          ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)))‖ ≤
        ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ * Real.exp (|A| / 2) * ‖f t‖ := by
    intro q t
    rw [norm_mul, norm_mul, Complex.norm_conj]
    by_cases ht : f t = 0
    · rw [ht, norm_zero]; simp
    · have htA : |t| ≤ |A| := le_trans (hsupp t ht) (le_abs_self A)
      have hexp := norm_cexp_I_mul_xiSpectralPoint_le q t
      have hexp' : Real.exp (|t| / 2) ≤ Real.exp (|A| / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      calc ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ *
            (‖f t‖ * ‖cexp (I * xiSpectralPoint q * (t : ℂ))‖)
          ≤ ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ * (‖f t‖ * Real.exp (|A| / 2)) := by
            gcongr
            exact hexp.trans hexp'
        _ = _ := by ring
  have hmeas : ∀ q : XiZeroCopy, AEStronglyMeasurable (fun t : ℝ =>
      suzukiSmoothFourier w (-xiSpectralPoint q) *
        ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)))) volume := by
    intro q
    exact aestronglyMeasurable_const.mul
      ((hf.aestronglyMeasurable.star).mul (by fun_prop : Continuous fun t : ℝ =>
        cexp (I * xiSpectralPoint q * (t : ℂ))).aestronglyMeasurable)
  have hint : ∀ q : XiZeroCopy, Integrable (fun t : ℝ =>
      suzukiSmoothFourier w (-xiSpectralPoint q) *
        ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)))) := by
    intro q
    refine (hf.norm.const_mul (‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ *
      Real.exp (|A| / 2))).mono' (hmeas q) (ae_of_all _ fun t => ?_)
    exact hterm q t
  have hsum : Summable fun q : XiZeroCopy => ∫ t : ℝ,
      ‖suzukiSmoothFourier w (-xiSpectralPoint q) *
        ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)))‖ := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun t => norm_nonneg _)
      (fun q => ?_)
      ((summable_norm_suzukiSmoothFourier_neg w).mul_right
        (Real.exp (|A| / 2) * ∫ t : ℝ, ‖f t‖))
    calc (∫ t : ℝ, ‖suzukiSmoothFourier w (-xiSpectralPoint q) *
          ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ)))‖)
        ≤ ∫ t : ℝ, ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ *
            Real.exp (|A| / 2) * ‖f t‖ :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hf.norm.const_mul _) (Eventually.of_forall (hterm q))
      _ = ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ *
            (Real.exp (|A| / 2) * ∫ t : ℝ, ‖f t‖) := by
          rw [integral_const_mul]; ring
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  calc ∑' q : XiZeroCopy, suzukiSmoothFourier w (-xiSpectralPoint q) *
        ∫ t : ℝ, (starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ))
      = ∑' q : XiZeroCopy, ∫ t : ℝ, suzukiSmoothFourier w (-xiSpectralPoint q) *
          ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ))) :=
        tsum_congr fun q => (integral_const_mul _ _).symm
    _ = ∫ t : ℝ, ∑' q : XiZeroCopy, suzukiSmoothFourier w (-xiSpectralPoint q) *
          ((starRingEnd ℂ) (f t) * cexp (I * xiSpectralPoint q * (t : ℂ))) := hswap
    _ = ∫ t : ℝ, (starRingEnd ℂ) (f t) * zeroKernel w t := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [zeroKernel]
        rw [← tsum_mul_left]
        exact tsum_congr fun q => by ring

/-! ## Plancherel representation of the form against a smooth source -/

/-- The weighted Fourier transform `W · 𝓕 s` of a smooth interior source, as an `L²` vector. -/
def weightedSourceL2 (s : CCMComplexSmoothInteriorSource a) : SoninL2 :=
  (SchwartzMap.smulLeftCLM ℂ (fun xi : ℝ => (ccmArchimedeanFormWeight xi : ℂ))
    (𝓕 s.toSchwartz)).toLp 2 volume

theorem inner_toCCMFormVector_eq (x : CCMArchimedeanFormDomain a)
    (s : CCMComplexSmoothInteriorSource a) :
    inner ℂ x s.toCCMFormVector =
      inner ℂ ((ccmArchimedeanFormToAperture a x : suzukiApertureHilbert a) : SoninL2)
        (fourierUnitary.symm (weightedSourceL2 a s)) := by
  have hJ : ((ccmArchimedeanFormToAperture a x : suzukiApertureHilbert a) : SoninL2) =
      fourierUnitary.symm (ccmArchimedeanWeightedToL2 x.1) := rfl
  rw [hJ, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, L2.inner_def, L2.inner_def]
  have hwd := integral_withDensity_eq_integral_smul (μ := (volume : Measure ℝ))
    measurable_ccmArchimedeanFormWeightNNReal
    (fun xi => inner ℂ ((x.1 : ℝ → ℂ) xi) (((s.toCCMFormVector).1 : ℝ → ℂ) xi))
  refine Eq.trans hwd ?_
  refine integral_congr_ae ?_
  have hS := SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ
    (fun xi : ℝ => (ccmArchimedeanFormWeight xi : ℂ)) (𝓕 s.toSchwartz)) 2 volume
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn x.1, hS,
    s.toCCMFormVector_fourier_coeFn] with xi h1 h2 h3
  change Real.toNNReal (ccmArchimedeanFormWeight xi) •
      inner ℂ ((x.1 : ℝ → ℂ) xi) (((s.toCCMFormVector).1 : ℝ → ℂ) xi) =
    inner ℂ ((ccmArchimedeanWeightedToL2 x.1 : ℝ → ℂ) xi) ((weightedSourceL2 a s : ℝ → ℂ) xi)
  rw [h1, show (weightedSourceL2 a s : ℝ → ℂ) xi = _ from h2, h3,
    SchwartzMap.smulLeftCLM_apply_apply ccmArchimedeanFormWeight_complex_hasTemperateGrowth,
    SchwartzMap.fourier_coe, inner_smul_right, NNReal.smul_def, coe_ccmArchimedeanFormWeightNNReal,
    Complex.real_smul]

/-- The `L²` representer of `Q(·, v_s)` on the physical aperture. -/
def formRepresenter (s : CCMComplexSmoothInteriorSource a) : SoninL2 :=
  fourierUnitary.symm (weightedSourceL2 a s) +
    ((ccmRestrictedWeilBoundedRemainder a
      (ccmArchimedeanFormToAperture a s.toCCMFormVector) : suzukiApertureHilbert a) : SoninL2)

theorem ccmRestrictedWeilForm_toCCMFormVector_eq (x : CCMArchimedeanFormDomain a)
    (s : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a x s.toCCMFormVector =
      inner ℂ ((ccmArchimedeanFormToAperture a x : suzukiApertureHilbert a) : SoninL2)
        (formRepresenter a s) := by
  rw [ccmRestrictedWeilForm, inner_toCCMFormVector_eq, formRepresenter, inner_add_right]
  congr 1
  rw [← Submodule.coe_inner]
  exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric _ _

/-! ## Extension of the explicit formula to the form domain -/

theorem continuous_zeroKernel {b : ℝ} (w : SuzukiSmoothCompactTest b) :
    Continuous (zeroKernel w) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hon : ContinuousOn (zeroKernel w) (Icc (t₀ - 1) (t₀ + 1)) := by
    refine continuousOn_tsum (u := fun q : XiZeroCopy =>
        ‖suzukiSmoothFourier w (-xiSpectralPoint q)‖ * Real.exp ((|t₀| + 1) / 2))
      (fun q => (by fun_prop : Continuous fun t : ℝ =>
        suzukiSmoothFourier w (-xiSpectralPoint q) *
          cexp (I * xiSpectralPoint q * (t : ℂ))).continuousOn)
      ((summable_norm_suzukiSmoothFourier_neg w).mul_right _) (fun q t ht => ?_)
    rw [norm_mul]
    gcongr
    refine (norm_cexp_I_mul_xiSpectralPoint_le q t).trans (Real.exp_le_exp.mpr ?_)
    have : |t| ≤ |t₀| + 1 := by
      rw [abs_le] at *
      constructor <;> linarith [ht.1, ht.2, abs_nonneg t₀, neg_abs_le t₀, le_abs_self t₀]
    linarith
  exact hon.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- A smooth real test inside the aperture, as a complex smooth interior source. -/
def realSource (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    (hga : tsupport g ⊆ Ioo (-a.1) a.1) : CCMComplexSmoothInteriorSource a where
  toFun t := (g t : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp hg
  hasCompactSupport := hgs.comp_left Complex.ofReal_zero
  tsupport_subset := by
    have hsupp : Function.support (fun t => (g t : ℂ)) = Function.support g := by
      ext t; simp [Function.mem_support]
    rw [tsupport, hsupp]
    exact hga

theorem bound_support_of_supportedIn {A : ℝ} {f : ℝ → ℂ} (hf : FourierZeroFlip.SupportedIn A f) :
    ∀ t, f t ≠ 0 → |t| ≤ A := by
  intro t ht
  by_contra hlt
  apply ht
  apply hf
  intro hmem
  exact hlt (abs_le.mpr hmem)

/-- On smooth sources the representer integral is the zero-kernel integral. -/
theorem integral_conj_source_formRepresenter (u s : CCMComplexSmoothInteriorSource a) :
    ∫ t : ℝ, (starRingEnd ℂ) (u t) * (formRepresenter a s : ℝ → ℂ) t =
      ∫ t : ℝ, (starRingEnd ℂ) (u t) * zeroKernel s.toSuzukiSmoothCompactTest t := by
  have h1 : ccmRestrictedWeilForm a u.toCCMFormVector s.toCCMFormVector =
      ∫ t : ℝ, (starRingEnd ℂ) (u t) * (formRepresenter a s : ℝ → ℂ) t := by
    rw [ccmRestrictedWeilForm_toCCMFormVector_eq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [u.toCCMFormVector_physical_coeFn] with t ht
    rw [RCLike.inner_apply, ht]
    exact mul_comm _ _
  have h2 := ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution u s
  rw [suzukiWeilDistribution_hermitianConvolution a.2.le] at h2
  have hsuppu : ∀ t, (u : ℝ → ℂ) t ≠ 0 → |t| ≤ a.1 := by
    intro t ht
    have hmem := u.support_subset ht
    exact abs_le.mpr ⟨hmem.1.le, hmem.2.le⟩
  have h3 := tsum_mul_integral_eq_integral_zeroKernel s.toSuzukiSmoothCompactTest
    u.integrable hsuppu
  rw [← h1, h2]
  exact h3

/-- The difference between the representer and the zero kernel. -/
def representerDefect (s : CCMComplexSmoothInteriorSource a) (t : ℝ) : ℂ :=
  (formRepresenter a s : ℝ → ℂ) t - zeroKernel s.toSuzukiSmoothCompactTest t

theorem integral_smul_representerDefect_eq_zero (s : CCMComplexSmoothInteriorSource a)
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    (hga : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∫ t : ℝ, g t • representerDefect a s t = 0 := by
  have hid := integral_conj_source_formRepresenter a (realSource a g hg hgs hga) s
  have hfun : ∀ t, (starRingEnd ℂ) ((realSource a g hg hgs hga) t) = (g t : ℂ) := by
    intro t
    exact Complex.conj_ofReal (g t)
  simp only [hfun] at hid
  have hint1 : Integrable fun t : ℝ => (g t : ℂ) * (formRepresenter a s : ℝ → ℂ) t := by
    have hgL2 : MemLp (fun t : ℝ => (g t : ℂ)) 2 volume :=
      ((Complex.continuous_ofReal.comp hg.continuous).memLp_of_hasCompactSupport
        (hgs.comp_left Complex.ofReal_zero))
    have := L2.integrable_inner (𝕜 := ℂ) (hgL2.toLp _) (formRepresenter a s)
    refine this.congr ?_
    filter_upwards [hgL2.coeFn_toLp] with t ht
    rw [RCLike.inner_apply, ht, Complex.conj_ofReal]
    exact mul_comm _ _
  have hint2 : Integrable fun t : ℝ => (g t : ℂ) * zeroKernel s.toSuzukiSmoothCompactTest t :=
    ((Complex.continuous_ofReal.comp hg.continuous).mul
      (continuous_zeroKernel _)).integrable_of_hasCompactSupport
      ((hgs.comp_left Complex.ofReal_zero).mul_right)
  have hsub := integral_sub hint1 hint2
  rw [hid, sub_self] at hsub
  have hfun2 : (fun t : ℝ => g t • representerDefect a s t) = fun t : ℝ =>
      (g t : ℂ) * (formRepresenter a s : ℝ → ℂ) t -
        (g t : ℂ) * zeroKernel s.toSuzukiSmoothCompactTest t := by
    funext t
    rw [representerDefect, Complex.real_smul, mul_sub]
  rw [hfun2]
  exact hsub

theorem representerDefect_ae_eq_zero (s : CCMComplexSmoothInteriorSource a) :
    ∀ᵐ t : ℝ, t ∈ Ioo (-a.1) a.1 → representerDefect a s t = 0 := by
  have hloc : LocallyIntegrableOn (representerDefect a s) (Ioo (-a.1) a.1) := by
    have h1 : LocallyIntegrable (formRepresenter a s : ℝ → ℂ) :=
      (Lp.memLp (formRepresenter a s)).locallyIntegrable (by norm_num)
    have h2 : LocallyIntegrable (zeroKernel s.toSuzukiSmoothCompactTest) :=
      (continuous_zeroKernel _).locallyIntegrable
    exact (h1.sub h2).locallyIntegrableOn _
  exact isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgs hga => integral_smul_representerDefect_eq_zero a s g hg hgs hga)

/-- **The representer agrees with the zero kernel against every form-domain vector.** -/
theorem integral_timeRep_formRepresenter_eq (x : CCMArchimedeanFormDomain a)
    (s : CCMComplexSmoothInteriorSource a) :
    ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * (formRepresenter a s : ℝ → ℂ) t =
      ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * zeroKernel s.toSuzukiSmoothCompactTest t := by
  have hKc := continuous_zeroKernel s.toSuzukiSmoothCompactTest
  have hsuppx := bound_support_of_supportedIn (supportedIn_timeRep a x)
  have hne : ∀ c : ℝ, ∀ᵐ t : ℝ, t ≠ c := by
    intro c
    rw [ae_iff]
    simp
  have hend : ∀ᵐ t : ℝ, t ≠ a.1 ∧ t ≠ -a.1 := by
    filter_upwards [hne a.1, hne (-a.1)] with t h1 h2 using ⟨h1, h2⟩
  have hcut : ∀ᵐ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * representerDefect a s t = 0 := by
    filter_upwards [representerDefect_ae_eq_zero a s, hend] with t ht hne
    by_cases hx : timeRep a x t = 0
    · rw [hx, map_zero, zero_mul]
    · have hta := abs_le.mp (hsuppx t hx)
      rw [ht ⟨lt_of_le_of_ne hta.1 (Ne.symm hne.2), lt_of_le_of_ne hta.2 hne.1⟩, mul_zero]
  have hint1 : Integrable fun t : ℝ =>
      (starRingEnd ℂ) (timeRep a x t) * (formRepresenter a s : ℝ → ℂ) t := by
    have := L2.integrable_inner (𝕜 := ℂ)
      ((ccmArchimedeanFormToAperture a x : suzukiApertureHilbert a) : SoninL2)
      (formRepresenter a s)
    refine this.congr ?_
    filter_upwards [coeFn_eq_timeRep a x] with t ht
    rw [RCLike.inner_apply, ht]
    exact mul_comm _ _
  have hint2 : Integrable fun t : ℝ =>
      (starRingEnd ℂ) (timeRep a x t) * zeroKernel s.toSuzukiSmoothCompactTest t := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -a.1) (b := a.1)).exists_bound_of_continuousOn
      hKc.continuousOn
    refine ((integrable_timeRep a x).norm.mul_const M).mono'
      (((integrable_timeRep a x).aestronglyMeasurable.star).mul hKc.aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [norm_mul, Complex.norm_conj]
    by_cases hx : timeRep a x t = 0
    · rw [hx, norm_zero, zero_mul, zero_mul]
    · gcongr
      exact hM t (abs_le.mp (hsuppx t hx))
  have hdiff := integral_sub hint1 hint2
  have hD0 : ∫ t : ℝ, ((starRingEnd ℂ) (timeRep a x t) * (formRepresenter a s : ℝ → ℂ) t -
      (starRingEnd ℂ) (timeRep a x t) * zeroKernel s.toSuzukiSmoothCompactTest t) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hcut] with t ht
    rw [← mul_sub]
    exact ht
  rw [hD0] at hdiff
  exact sub_eq_zero.mp hdiff.symm

/-! ## Parseval in the convention `ĥ(z) = ∫ h(t) e^{izt} dt` -/

/-- The transform of the conjugate of `f`: `z ↦ ∫ conj(f t) e^{izt} dt`. -/
def conjTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (starRingEnd ℂ) (f t) * cexp (I * z * (t : ℂ))

theorem integrable_suzukiSmoothFourier_ofReal {b : ℝ} (hb : 0 ≤ b)
    (w : SuzukiSmoothCompactTest b) :
    Integrable fun r : ℝ => suzukiSmoothFourier w (r : ℂ) := by
  have hc : Continuous fun r : ℝ => suzukiSmoothFourier w (r : ℂ) :=
    (differentiable_suzukiSmoothFourier hb w).continuous.comp Complex.continuous_ofReal
  refine (integrable_inv_one_add_sq.const_mul (suzukiTestDecayConst w 0)).mono'
    hc.aestronglyMeasurable (ae_of_all _ fun r => ?_)
  have hb := norm_suzukiSmoothFourier_le_div w le_rfl (z := (r : ℂ)) (by simp)
  have hr : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by simp [sq_abs]
  rw [hr, div_eq_mul_inv] at hb
  exact hb

/-- **Parseval.** For integrable `f` and a smooth compact test `w`,
`∫ conj(f) w = (1/2π) ∫ conjTransform f (σ) · ŵ(-σ) dσ`. -/
theorem integral_conj_mul_eq_parseval {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ} (hf : Integrable f)
    (w : SuzukiSmoothCompactTest b) :
    ∫ t : ℝ, (starRingEnd ℂ) (f t) * w t =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ σ : ℝ, conjTransform f (σ : ℂ) * suzukiSmoothFourier w (-(σ : ℂ)) := by
  have hwc : Continuous (w : ℝ → ℂ) := w.continuous
  have hwi : Integrable (w : ℝ → ℂ) := w.integrable
  have hF : Integrable (𝓕 (w : ℝ → ℂ)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two (w.smooth.of_le (by norm_cast))
      w.hasCompactSupport
  have hinv : ∀ t : ℝ, w t = (1 / (2 * Real.pi) : ℂ) *
      ∫ r : ℝ, suzukiSmoothFourier w (r : ℂ) * cexp (-I * r * t) := by
    intro t
    exact Zeta23.EF.paper_inversion hwc hwi hF t
  -- Fubini
  have hprod : Integrable (Function.uncurry fun (t r : ℝ) =>
      (starRingEnd ℂ) (f t) * (suzukiSmoothFourier w (r : ℂ) * cexp (-I * r * t)))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖f p.1‖ * ‖suzukiSmoothFourier w (p.2 : ℂ)‖)
        (volume.prod volume) :=
      hf.norm.mul_prod (integrable_suzukiSmoothFourier_ofReal hb w).norm
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.1))
          (volume.prod volume) := hf.aestronglyMeasurable.star.comp_fst
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          suzukiSmoothFourier w (p.2 : ℂ) * cexp (-I * p.2 * p.1)) (volume.prod volume) := by
        have hc : Continuous fun p : ℝ × ℝ =>
            suzukiSmoothFourier w (p.2 : ℂ) * cexp (-I * p.2 * p.1) :=
          ((differentiable_suzukiSmoothFourier hb w).continuous.comp
            (Complex.continuous_ofReal.comp continuous_snd)).mul (by fun_prop)
        exact hc.aestronglyMeasurable
      exact h1.mul h2
    · obtain ⟨t, r⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj]
      have he : ‖cexp (-I * (r : ℂ) * (t : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [he, mul_one]
  have hswap := integral_integral_swap hprod
  calc ∫ t : ℝ, (starRingEnd ℂ) (f t) * w t
      = ∫ t : ℝ, (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, (starRingEnd ℂ) (f t) *
          (suzukiSmoothFourier w (r : ℂ) * cexp (-I * r * t)) := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        dsimp only
        rw [show w t = w.toFun t from rfl, hinv t, integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∫ r : ℝ, (starRingEnd ℂ) (f t) *
          (suzukiSmoothFourier w (r : ℂ) * cexp (-I * r * t)) := integral_const_mul _ _
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, ∫ t : ℝ, (starRingEnd ℂ) (f t) *
          (suzukiSmoothFourier w (r : ℂ) * cexp (-I * r * t)) := by rw [hswap]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, conjTransform f (-(r : ℂ)) *
          suzukiSmoothFourier w (r : ℂ) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        simp only [conjTransform]
        rw [← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        have : cexp (-I * (r : ℂ) * (t : ℂ)) = cexp (I * -(r : ℂ) * (t : ℂ)) := by ring_nf
        dsimp only
        rw [this]
        ring
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ σ : ℝ, conjTransform f (σ : ℂ) *
          suzukiSmoothFourier w (-(σ : ℂ)) := by
        congr 1
        rw [← integral_neg_eq_self]
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        simp only [ofReal_neg, neg_neg]

/-! ## The zero-side Euler–Lagrange equation -/

theorem ccmRestrictedWeilForm_eq_integral_representer (x : CCMArchimedeanFormDomain a)
    (s : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a x s.toCCMFormVector =
      ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * (formRepresenter a s : ℝ → ℂ) t := by
  rw [ccmRestrictedWeilForm_toCCMFormVector_eq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_eq_timeRep a x] with t ht
  rw [RCLike.inner_apply, ht]
  exact mul_comm _ _

theorem inner_aperture_eq_integral (x : CCMArchimedeanFormDomain a)
    (s : CCMComplexSmoothInteriorSource a) :
    inner ℂ (ccmArchimedeanFormToAperture a x) (ccmArchimedeanFormToAperture a s.toCCMFormVector) =
      ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * s t := by
  rw [Submodule.coe_inner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_eq_timeRep a x, s.toCCMFormVector_physical_coeFn] with t ht hs
  rw [RCLike.inner_apply, ht, hs]
  exact mul_comm _ _

/-- **Zero-side Euler–Lagrange equation of a full ground state.** -/
theorem zeroSide_eigen_of_isFullGround {x : CCMArchimedeanFormDomain a} (hx : IsFullGround a x)
    (s : CCMComplexSmoothInteriorSource a) :
    ∑' q : XiZeroCopy, conjTransform (timeRep a x) (xiSpectralPoint q) *
        suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-xiSpectralPoint q) =
      ((ccmRestrictedWeilGroundEnergy a : ℂ) * (1 / (2 * Real.pi) : ℂ)) *
        ∫ σ : ℝ, conjTransform (timeRep a x) (σ : ℂ) *
          suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-(σ : ℂ)) := by
  have hsupp := bound_support_of_supportedIn (supportedIn_timeRep a x)
  have h1 := tsum_mul_integral_eq_integral_zeroKernel s.toSuzukiSmoothCompactTest
    (integrable_timeRep a x) hsupp
  have h2 := integral_timeRep_formRepresenter_eq a x s
  have h3 := ccmRestrictedWeilForm_eq_integral_representer a x s
  have h4 := shiftedForm_eq_zero_of_isFullGround a hx s.toCCMFormVector
  rw [shiftedForm, sub_eq_zero, inner_aperture_eq_integral] at h4
  have h6 := integral_conj_mul_eq_parseval a.2.le (integrable_timeRep a x)
    s.toSuzukiSmoothCompactTest
  have hs : ∀ t, s.toSuzukiSmoothCompactTest t = s t := fun t => rfl
  simp only [hs] at h6
  calc ∑' q : XiZeroCopy, conjTransform (timeRep a x) (xiSpectralPoint q) *
        suzukiSmoothFourier s.toSuzukiSmoothCompactTest (-xiSpectralPoint q)
      = ∑' q : XiZeroCopy, suzukiSmoothFourier s.toSuzukiSmoothCompactTest
          (-xiSpectralPoint q) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) *
            cexp (I * xiSpectralPoint q * (t : ℂ)) :=
        tsum_congr fun q => by rw [conjTransform, mul_comm]
    _ = ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) *
          zeroKernel s.toSuzukiSmoothCompactTest t := h1
    _ = ccmRestrictedWeilForm a x s.toCCMFormVector := by rw [h3, h2]
    _ = (ccmRestrictedWeilGroundEnergy a : ℂ) *
          ∫ t : ℝ, (starRingEnd ℂ) (timeRep a x t) * s t := h4
    _ = _ := by rw [h6]; ring

/-! ## The capstone: localized real-rooted full ground states force RH -/

theorem conjTransform_eq_conj_unitaryLaplace (f : ℝ → ℂ) (z : ℂ) :
    conjTransform f z = (starRingEnd ℂ)
      (FourierLaplaceDivision.unitaryLaplace f ((starRingEnd ℂ) z / (2 * Real.pi))) := by
  rw [conjTransform, FourierLaplaceDivision.unitaryLaplace, ← integral_conj]
  congr 1
  funext t
  rw [map_mul, ← Complex.exp_conj, mul_comm]
  congr 2
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [map_neg, map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  field_simp

theorem differentiable_conjTransform {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : FourierZeroFlip.SupportedIn A f) : Differentiable ℂ (conjTransform f) := by
  have hcs : FourierZeroFlip.SupportedIn A (fun t => (starRingEnd ℂ) (f t)) := by
    intro t ht
    show (starRingEnd ℂ) (f t) = 0
    rw [hs t ht, map_zero]
  have hfs : Integrable (fun t => (starRingEnd ℂ) (f t)) :=
    hf.norm.mono' hf.aestronglyMeasurable.star
      (ae_of_all _ fun t => le_of_eq (Complex.norm_conj (f t)))
  have hdiff := CCMXiStrip.differentiable_unitaryLaplace hA hfs hcs
  have heq : conjTransform f = fun z => FourierLaplaceDivision.unitaryLaplace
      (fun t => (starRingEnd ℂ) (f t)) (-z / (2 * Real.pi)) := by
    funext z
    rw [conjTransform, FourierLaplaceDivision.unitaryLaplace]
    congr 1
    funext t
    rw [mul_comm]
    congr 1
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    field_simp
  rw [heq]
  exact hdiff.comp (by fun_prop)

theorem norm_conjTransform_le {f : ℝ → ℂ} {Y : ℝ} {z : ℂ} (hz : |z.im| ≤ Y)
    (hint : Integrable fun t : ℝ => ‖f t‖ * Real.exp (Y * |t|)) :
    ‖conjTransform f z‖ ≤ ∫ t : ℝ, ‖f t‖ * Real.exp (Y * |t|) := by
  rw [conjTransform]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) hint (Eventually.of_forall fun t => ?_))
  show ‖(starRingEnd ℂ) (f t) * cexp (I * z * (t : ℂ))‖ ≤ ‖f t‖ * Real.exp (Y * |t|)
  rw [norm_mul, Complex.norm_conj, Complex.norm_exp]
  gcongr
  have hre : (I * z * (t : ℂ)).re = -(z.im * t) := by simp [mul_re, mul_im]
  rw [hre]
  calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
    _ = |z.im| * |t| := abs_mul _ _
    _ ≤ Y * |t| := mul_le_mul_of_nonneg_right hz (abs_nonneg t)

/-- A smooth compact test on `[-R, R]`, `R < a`, as a smooth interior source at aperture `a`. -/
def testSource {R : ℝ} (w : SuzukiSmoothCompactTest R) (hR : R < a.1) :
    CCMComplexSmoothInteriorSource a where
  toFun := w
  smooth := w.smooth
  hasCompactSupport := w.hasCompactSupport
  tsupport_subset := w.tsupport_subset.trans (Icc_subset_Ioo (by linarith) hR)

/-- **Strip-bounded real-rooted full ground states force RH.** Let `u_j` be ground states of the
unconstrained restricted Weil forms at apertures `a_j → ∞`, with real-rooted Fourier–Laplace
transforms and nonzero mass. If their transforms are bounded on the strip `|Im z| < 1/2 + η`
uniformly relative to their mass, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_stripBoundedFullGrounds {η C : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (hstrip : ∀ j (z : ℂ), |z.im| < 1 / 2 + η →
      ‖conjTransform (timeRep (a j) (u j)) z‖ ≤ C * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis := by
  set f : ℕ → ℝ → ℂ := fun j => timeRep (a j) (u j) with hf
  set CT0 : ℕ → ℂ := fun j => conjTransform (f j) 0 with hCT0
  have hCT0eq : ∀ j, CT0 j = (starRingEnd ℂ) (∫ t : ℝ, f j t) := by
    intro j
    simp only [hCT0, conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_conj
  have hCT0ne : ∀ j, CT0 j ≠ 0 := by
    intro j
    rw [hCT0eq, map_ne_zero]
    exact hmass j
  set G : ℕ → ℂ → ℂ := fun j z => conjTransform (f j) z / CT0 j with hG
  have hsupp : ∀ j, FourierZeroFlip.SupportedIn (a j).1 (f j) :=
    fun j => supportedIn_timeRep (a j) (u j)
  refine RHTower.riemannHypothesis_of_realRootedEigen (η := η) (C := C) hη ha
    (G := G) (κ := fun j => (ccmRestrictedWeilGroundEnergy (a j) : ℂ) * (1 / (2 * Real.pi) : ℂ))
    ?_ ?_ ?_ ?_ ?_
  · intro j
    exact ((differentiable_conjTransform (a j).2.le (integrable_timeRep (a j) (u j)) (hsupp j)).div_const
      _).differentiableOn
  · intro j z hz
    have hpos : 0 < ‖CT0 j‖ := norm_pos_iff.mpr (hCT0ne j)
    have hnorm : ‖CT0 j‖ = ‖∫ t : ℝ, f j t‖ := by rw [hCT0eq, Complex.norm_conj]
    rw [hG, norm_div, div_le_iff₀ hpos, hnorm]
    exact hstrip j z hz
  · intro j z _ hz
    have hc : conjTransform (f j) z = 0 := by
      have := hz
      simp only [hG, div_eq_zero_iff] at this
      exact this.resolve_right (hCT0ne j)
    rw [conjTransform_eq_conj_unitaryLaplace, map_eq_zero] at hc
    have him := hreal j _ hc
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have : ((starRingEnd ℂ) z / (2 * Real.pi : ℂ)).im = -z.im / (2 * Real.pi) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
        Complex.conj_im]
    rw [this] at him
    have := div_eq_zero_iff.mp him
    rcases this with h | h
    · linarith
    · linarith
  · intro j
    simp only [hG]
    exact div_self (hCT0ne j)
  · intro j R hR0 hRa w
    have hid := zeroSide_eigen_of_isFullGround (a j) (hground j) (testSource (a j) w hRa)
    have hw : ∀ z, suzukiSmoothFourier (testSource (a j) w hRa).toSuzukiSmoothCompactTest z =
        suzukiSmoothFourier w z := fun z => rfl
    simp only [hw] at hid
    simp only [hG, div_mul_eq_mul_div]
    rw [tsum_div_const, integral_div, hid]
    ring

/-- **Localized real-rooted full ground states force RH.** Let `u_j` be ground states of the
unconstrained restricted Weil forms at apertures `a_j → ∞`, with real-rooted Fourier–Laplace
transforms and nonzero mass. If their physical functions are localized at the exponential rate
`1/2 + η` uniformly relative to their mass, then the Riemann hypothesis holds. Real-rooted ground
states exist at every aperture (`exists_realRooted_fullGround`); the localization is the only
remaining input. -/
theorem riemannHypothesis_of_localizedFullGrounds {η C : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (hloc : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ * Real.exp ((1 / 2 + η) * |t|) ≤
      C * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_stripBoundedFullGrounds (C := C) hη a ha u hground hreal hmass
    fun j z hz => ?_
  set f : ℝ → ℂ := timeRep (a j) (u j) with hf
  have hsuppb := bound_support_of_supportedIn (supportedIn_timeRep (a j) (u j))
  have hmomint : Integrable fun t : ℝ => ‖f t‖ * Real.exp ((1 / 2 + η) * |t|) := by
    refine ((integrable_timeRep (a j) (u j)).norm.mul_const
      (Real.exp ((1 / 2 + η) * (a j).1))).mono' ?_ (ae_of_all _ fun t => ?_)
    · exact ((integrable_timeRep (a j) (u j)).norm.aestronglyMeasurable).mul
        (by fun_prop : Continuous fun t : ℝ => Real.exp ((1 / 2 + η) * |t|)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      by_cases hx : f t = 0
      · have hx' : timeRep (a j) (u j) t = 0 := hx
        simp [hx, hx']
      · gcongr
        exact hsuppb t hx
  exact (norm_conjTransform_le hz.le hmomint).trans (hloc j)

end

end RHTower.CCMFullGroundEigen
