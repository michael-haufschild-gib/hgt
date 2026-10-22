import GaloisForLFunctions.RHTower.CCM.CCMParityQuartetEvenFloor
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily

/-!
# The odd test of the isolated off-line quartet

Let `g(x) = 2 cos(tx) sinh(δx)` and `g_a = g · 1_{[−a,a]}`.  Smooth cutoffs
`χ(x) = ∫_{x−b}^{x+b} ρ` built from a mollifier `ρ` of width `ε` give smooth interior sources
`v = g χ` with `v → g_a` pointwise, `|v| ≤ |g_a|`, and `∫ |v'| ≤ 4(a(t+δ) + 1) cosh(δa)`
uniformly.  The last bound controls the critical-line part of the zero sum uniformly:
`|v̂(w)| ≤ K/|w|` for real `w`.

**The exact top-quartet value** (`testTransform_oddModel_top`):
`ĝ_a(σ) = −D⁻(a)/2 + i I(a)` for `σ = t + iδ`, and `conj ĝ_a(σ̄) = −ĝ_a(σ)` because `g_a` is real and
odd.  Hence the quartet contributes `−(M/4)(D⁻² − 4I²)`.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityQuartet

noncomputable section

/-! ## Smooth cutoffs -/

/-- The smooth cutoff `χ(x) = ∫_{x−b}^{x+b} ρ_ε`. -/
def cutoff {ε : ℝ} (hε : 0 < ε) (b x : ℝ) : ℝ := ∫ s in (x - b)..(x + b), bumpMollifier hε s

/-- The primitive of the mollifier. -/
def mollifierPrimitive {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, bumpMollifier hε s

theorem contDiff_bumpMollifier {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (bumpMollifier hε) :=
  (widthBump hε).contDiff_normed

theorem hasDerivAt_mollifierPrimitive {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (mollifierPrimitive hε) (bumpMollifier hε x) x :=
  ((continuous_bumpMollifier hε).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem contDiff_mollifierPrimitive {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierPrimitive hε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_mollifierPrimitive hε x).differentiableAt, ?_⟩
  have : deriv (mollifierPrimitive hε) = bumpMollifier hε :=
    funext fun x => (hasDerivAt_mollifierPrimitive hε x).deriv
  rw [this]
  exact contDiff_bumpMollifier hε

theorem cutoff_eq_primitive {ε : ℝ} (hε : 0 < ε) (b x : ℝ) :
    cutoff hε b x = mollifierPrimitive hε (x + b) - mollifierPrimitive hε (x - b) := by
  unfold cutoff mollifierPrimitive
  have hi : ∀ u v : ℝ, IntervalIntegrable (bumpMollifier hε) volume u v :=
    fun u v => (continuous_bumpMollifier hε).intervalIntegrable u v
  rw [intervalIntegral.integral_interval_sub_left (hi 0 (x + b)) (hi 0 (x - b))]

theorem contDiff_cutoff {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoff hε b) := by
  have : cutoff hε b = fun x => mollifierPrimitive hε (x + b) - mollifierPrimitive hε (x - b) :=
    funext (cutoff_eq_primitive hε b)
  rw [this]
  exact ((contDiff_mollifierPrimitive hε).comp (contDiff_id.add contDiff_const)).sub
    ((contDiff_mollifierPrimitive hε).comp (contDiff_id.sub contDiff_const))

theorem hasDerivAt_cutoff {ε : ℝ} (hε : 0 < ε) (b x : ℝ) :
    HasDerivAt (cutoff hε b) (bumpMollifier hε (x + b) - bumpMollifier hε (x - b)) x := by
  have h1 := (hasDerivAt_mollifierPrimitive hε (x + b)).comp x
    ((hasDerivAt_id x).add_const b)
  have h2 := (hasDerivAt_mollifierPrimitive hε (x - b)).comp x
    ((hasDerivAt_id x).sub_const b)
  have h := h1.sub h2
  simp only [mul_one, id] at h
  have hfun : cutoff hε b = fun x => mollifierPrimitive hε (x + b) - mollifierPrimitive hε (x - b) :=
    funext (cutoff_eq_primitive hε b)
  rw [hfun]
  exact h

theorem cutoff_nonneg {ε : ℝ} (hε : 0 < ε) {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : 0 ≤ cutoff hε b x :=
  intervalIntegral.integral_nonneg (by linarith) fun s _ => nonneg_bumpMollifier hε s

theorem cutoff_le_one {ε : ℝ} (hε : 0 < ε) {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : cutoff hε b x ≤ 1 := by
  unfold cutoff
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_bumpMollifier hε]
  exact setIntegral_le_integral (integrable_bumpMollifier hε)
    (Filter.Eventually.of_forall fun s => nonneg_bumpMollifier hε s)

theorem cutoff_eq_one {ε : ℝ} (hε : 0 < ε) {b x : ℝ} (hx : |x| ≤ b - 2 * ε) :
    cutoff hε b x = 1 := by
  unfold cutoff
  have hle : x - b ≤ x + b := by
    have := abs_nonneg x
    linarith
  rw [intervalIntegral.integral_of_le hle, ← integral_bumpMollifier hε]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  apply bumpMollifier_eq_zero hε
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
  have hx' := abs_le.mp hx
  rcases hs with hs | hs
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

theorem cutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {b x : ℝ} (hb : 0 ≤ b) (hx : b + 2 * ε ≤ |x|) :
    cutoff hε b x = 0 := by
  unfold cutoff
  apply intervalIntegral.integral_zero_ae
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [Set.uIoc_of_le (by linarith)] at hs
  apply bumpMollifier_eq_zero hε
  rcases le_abs'.mp hx with hx | hx
  · rw [abs_of_neg (by linarith [hs.2])]
    linarith [hs.2]
  · rw [abs_of_pos (by linarith [hs.1])]
    linarith [hs.1]

theorem integral_abs_deriv_cutoff_le {ε : ℝ} (hε : 0 < ε) (b : ℝ) :
    ∫ x, |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| ≤ 2 := by
  have hint1 : Integrable fun x => bumpMollifier hε (x + b) :=
    (integrable_bumpMollifier hε).comp_add_right b
  have hint2 : Integrable fun x => bumpMollifier hε (x - b) :=
    (integrable_bumpMollifier hε).comp_sub_right b
  calc ∫ x, |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)|
      ≤ ∫ x, (bumpMollifier hε (x + b) + bumpMollifier hε (x - b)) := by
        apply integral_mono (hint1.sub hint2).abs (hint1.add hint2)
        intro x
        have h1 := nonneg_bumpMollifier hε (x + b)
        have h2 := nonneg_bumpMollifier hε (x - b)
        simp only [Pi.sub_apply, Pi.add_apply]
        rw [abs_le]
        constructor <;> linarith
    _ = 2 := by
        rw [integral_add hint1 hint2, integral_add_right_eq_self (fun x => bumpMollifier hε x) b,
          integral_sub_right_eq_self (fun x => bumpMollifier hε x) b, integral_bumpMollifier]
        norm_num

/-! ## The odd model and its smooth truncations -/

/-- The odd model `g(x) = 2 cos(tx) sinh(δx)`. -/
def oddModel (t δ x : ℝ) : ℝ := 2 * Real.cos (t * x) * Real.sinh (δ * x)

/-- Its derivative. -/
def oddModelDeriv (t δ x : ℝ) : ℝ :=
  -(2 * (Real.sin (t * x) * t) * Real.sinh (δ * x)) +
    2 * Real.cos (t * x) * (Real.cosh (δ * x) * δ)

theorem hasDerivAt_oddModel (t δ x : ℝ) :
    HasDerivAt (oddModel t δ) (oddModelDeriv t δ x) x := by
  have h := ((hasDerivAt_cos_mul t x).const_mul 2).mul (hasDerivAt_sinh_mul δ x)
  have h' := h.congr_deriv (show _ = oddModelDeriv t δ x by unfold oddModelDeriv; ring)
  exact h'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp only [oddModel, Pi.mul_apply])

theorem contDiff_oddModel (t δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (oddModel t δ) := by
  unfold oddModel
  fun_prop

theorem abs_sinh_le_cosh (y : ℝ) : |Real.sinh y| ≤ Real.cosh y := by
  rw [Real.abs_sinh, ← Real.cosh_abs]
  exact (Real.sinh_lt_cosh _).le

theorem cosh_mul_le {δ a x : ℝ} (hδ : 0 ≤ δ) (hx : |x| ≤ a) :
    Real.cosh (δ * x) ≤ Real.cosh (δ * a) := by
  rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg hδ]
  have ha : 0 ≤ a := le_trans (abs_nonneg x) hx
  rw [abs_of_nonneg (mul_nonneg hδ ha)]
  exact mul_le_mul_of_nonneg_left hx hδ

theorem abs_oddModel_le {t δ a x : ℝ} (hδ : 0 ≤ δ) (hx : |x| ≤ a) :
    |oddModel t δ x| ≤ 2 * Real.cosh (δ * a) := by
  unfold oddModel
  rw [abs_mul, abs_mul, abs_two]
  have h1 := Real.abs_cos_le_one (t * x)
  have h2 := (abs_sinh_le_cosh (δ * x)).trans (cosh_mul_le hδ hx)
  have h3 := abs_nonneg (Real.sinh (δ * x))
  nlinarith [abs_nonneg (Real.cos (t * x))]

theorem abs_oddModelDeriv_le {t δ a x : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hx : |x| ≤ a) :
    |oddModelDeriv t δ x| ≤ 2 * (t + δ) * Real.cosh (δ * a) := by
  unfold oddModelDeriv
  have hs := Real.abs_sin_le_one (t * x)
  have hc := Real.abs_cos_le_one (t * x)
  have hsh := (abs_sinh_le_cosh (δ * x)).trans (cosh_mul_le hδ hx)
  have hch : |Real.cosh (δ * x)| ≤ Real.cosh (δ * a) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact cosh_mul_le hδ hx
  have hC := Real.cosh_pos (δ * a)
  calc |-(2 * (Real.sin (t * x) * t) * Real.sinh (δ * x)) +
        2 * Real.cos (t * x) * (Real.cosh (δ * x) * δ)|
      ≤ |2 * (Real.sin (t * x) * t) * Real.sinh (δ * x)| +
          |2 * Real.cos (t * x) * (Real.cosh (δ * x) * δ)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ = 2 * t * (|Real.sin (t * x)| * |Real.sinh (δ * x)|) +
          2 * δ * (|Real.cos (t * x)| * |Real.cosh (δ * x)|) := by
        simp only [abs_mul, abs_two, abs_of_nonneg ht, abs_of_nonneg hδ]
        ring
    _ ≤ 2 * t * (1 * Real.cosh (δ * a)) + 2 * δ * (1 * Real.cosh (δ * a)) := by
        gcongr
    _ = 2 * (t + δ) * Real.cosh (δ * a) := by ring

/-- The smooth odd test source `v(x) = g(x) χ(x)` with cutoff radius `b = a − 3ε`. -/
def oddTestSource (t δ : ℝ) (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε)
    (hεa : 4 * ε < a.1) : CCMComplexSmoothInteriorSource a where
  toFun x := ((oddModel t δ x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    ((contDiff_oddModel t δ).mul (contDiff_cutoff hε _))
  hasCompactSupport := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -a.1) (b := a.1)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hK
    apply hx
    have hxa : a.1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hK
      rcases hK with h | h
      · rw [abs_of_neg (by linarith [a.2])]; linarith
      · rw [abs_of_pos (by linarith [a.2])]; exact h
    rw [cutoff_eq_zero hε (by linarith) (by linarith)]
    simp
  tsupport_subset := by
    have hsupp : Function.support (fun x => ((oddModel t δ x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ))
        ⊆ Icc (-(a.1 - ε)) (a.1 - ε) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hK
      apply hx
      have hxa : a.1 - ε < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hK
        rcases hK with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      rw [cutoff_eq_zero hε (by linarith) (by linarith)]
      simp
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem oddTestSource_apply (t δ : ℝ) (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε)
    (hεa : 4 * ε < a.1) (x : ℝ) :
    (oddTestSource t δ a hε hεa : ℝ → ℂ) x =
      ((oddModel t δ x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ) := rfl

/-- The derivative of the odd test source. -/
theorem deriv_oddTestSource (t δ : ℝ) (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε)
    (hεa : 4 * ε < a.1) (x : ℝ) :
    deriv (oddTestSource t δ a hε hεa : ℝ → ℂ) x =
      ((oddModelDeriv t δ x * cutoff hε (a.1 - 3 * ε) x +
        oddModel t δ x * (bumpMollifier hε (x + (a.1 - 3 * ε)) -
          bumpMollifier hε (x - (a.1 - 3 * ε))) : ℝ) : ℂ) := by
  have h := ((hasDerivAt_oddModel t δ x).mul (hasDerivAt_cutoff hε (a.1 - 3 * ε) x)).ofReal_comp
  exact h.deriv

/-- `∫ |v'| ≤ 4(a(t+δ) + 1) cosh(δa)`, uniformly in `ε`. -/
theorem integral_norm_deriv_oddTestSource_le {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε) (hεa : 4 * ε < a.1) :
    ∫ x, ‖deriv (oddTestSource t δ a hε hεa : ℝ → ℂ) x‖ ≤
      4 * (a.1 * (t + δ) + 1) * Real.cosh (δ * a.1) := by
  set b := a.1 - 3 * ε with hb
  set C := Real.cosh (δ * a.1) with hC
  have hC0 : 0 < C := Real.cosh_pos _
  have ha : 0 < a.1 := a.2
  set B : ℝ → ℝ := fun x => (Icc (-a.1) a.1).indicator (fun _ => 2 * (t + δ) * C) x +
    2 * C * |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| with hB
  have hint2 : Integrable fun x => |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| :=
    ((integrable_bumpMollifier hε).comp_add_right b).sub
      ((integrable_bumpMollifier hε).comp_sub_right b) |>.abs
  have hint1 : Integrable fun x => (Icc (-a.1) a.1).indicator (fun _ => 2 * (t + δ) * C) x :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hBint : Integrable B := hint1.add (hint2.const_mul _)
  have hpt : ∀ x, ‖deriv (oddTestSource t δ a hε hεa : ℝ → ℂ) x‖ ≤ B x := by
    intro x
    rw [deriv_oddTestSource, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    simp only [hB]
    gcongr ?_ + ?_
    · by_cases hx : x ∈ Icc (-a.1) a.1
      · rw [Set.indicator_of_mem hx, abs_mul,
          abs_of_nonneg (cutoff_nonneg hε (by linarith) x)]
        have hxa : |x| ≤ a.1 := abs_le.mpr ⟨hx.1, hx.2⟩
        calc |oddModelDeriv t δ x| * cutoff hε b x ≤ (2 * (t + δ) * C) * 1 :=
              mul_le_mul (abs_oddModelDeriv_le ht hδ hxa) (cutoff_le_one hε (by linarith) x)
                (cutoff_nonneg hε (by linarith) x) (by positivity)
          _ = 2 * (t + δ) * C := mul_one _
      · rw [Set.indicator_of_notMem hx]
        have hxa : a.1 < |x| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
          rcases hx with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; exact h
        rw [cutoff_eq_zero hε (by linarith) (by linarith)]
        simp
    · rw [abs_mul]
      by_cases hxa : |x| ≤ a.1
      · exact mul_le_mul_of_nonneg_right (abs_oddModel_le hδ hxa) (abs_nonneg _)
      · push Not at hxa
        have h1 : bumpMollifier hε (x + b) = 0 := by
          apply bumpMollifier_eq_zero hε
          rcases le_abs'.mp hxa.le with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have h2 : bumpMollifier hε (x - b) = 0 := by
          apply bumpMollifier_eq_zero hε
          rcases le_abs'.mp hxa.le with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        rw [h1, h2]
        simp
  calc ∫ x, ‖deriv (oddTestSource t δ a hε hεa : ℝ → ℂ) x‖ ≤ ∫ x, B x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hBint
          (Filter.Eventually.of_forall hpt)
    _ = 2 * (t + δ) * C * (2 * a.1) +
          2 * C * ∫ x, |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| := by
        rw [integral_add hint1 (hint2.const_mul _), integral_const_mul,
          integral_indicator measurableSet_Icc, setIntegral_const]
        rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring
    _ ≤ 2 * (t + δ) * C * (2 * a.1) + 2 * C * 2 := by
        gcongr
        exact integral_abs_deriv_cutoff_le hε b
    _ = 4 * (a.1 * (t + δ) + 1) * C := by ring

/-! ## The critical-line part of the zero sum -/

/-- For real `w`, `|ψ̂(w)| · |w| ≤ ∫ |ψ'|`. -/
theorem norm_testTransform_mul_norm_le {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    {w : ℂ} (hw : w.im = 0) :
    ‖testTransform ψ w‖ * ‖w‖ ≤ ∫ x, ‖deriv ψ x‖ := by
  have hibp := testTransform_ibp hψ hs w
  have h1 : ‖testTransform ψ w‖ * ‖w‖ = ‖testTransform (deriv ψ) w‖ := by
    rw [← norm_neg (testTransform (deriv ψ) w), ← hibp, norm_mul, norm_mul, Complex.norm_I, one_mul]
  rw [h1]
  unfold testTransform
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext x
  rw [norm_mul, Complex.norm_exp]
  have : (Complex.I * w * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, hw]
  rw [this, Real.exp_zero, mul_one]

/-- On a real spectral point the term is at most `K²/|z|²`, with `K = ∫ |ψ'|`. -/
theorem re_zeroSumTerm_le_of_im_eq_zero {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport ψ) {z : ℂ} (hz : z.im = 0) (hz0 : z ≠ 0) :
    (zeroSumTerm ψ z).re ≤ (∫ x, ‖deriv ψ x‖) ^ 2 * (1 / ‖z‖ ^ 2) := by
  have hconj : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr hz
  unfold zeroSumTerm
  rw [hconj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hb := norm_testTransform_mul_norm_le hψ hs (w := -z) (by simp [hz])
  rw [norm_neg] at hb
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hK : 0 ≤ ∫ x, ‖deriv ψ x‖ := integral_nonneg fun _ => norm_nonneg _
  have hle : ‖testTransform ψ (-z)‖ ≤ (∫ x, ‖deriv ψ x‖) / ‖z‖ := by
    rw [le_div_iff₀ hzpos]
    exact hb
  calc ‖testTransform ψ (-z)‖ ^ 2 ≤ ((∫ x, ‖deriv ψ x‖) / ‖z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = (∫ x, ‖deriv ψ x‖) ^ 2 * (1 / ‖z‖ ^ 2) := by ring

/-- **Upper bound for the zero sum.**  Under the finite off-line hypothesis, the source quadratic
of a smooth source is at most its off-line part plus `K² Σ_q |z_q|^{−2}`. -/
theorem sourceQuadratic_le_offLine_add {σ : ℂ} (h : IsolatedTopQuartet σ)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      ∑ q ∈ h.offLine, (zeroSumTerm u (xiSpectralPoint q)).re +
        (∫ x, ‖deriv (u : ℝ → ℂ) x‖) ^ 2 *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  classical
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  set K := ∫ x, ‖deriv (u : ℝ → ℂ) x‖ with hK
  set T : XiZeroCopy → ℂ := fun q => zeroSumTerm u (xiSpectralPoint q) with hT
  have hsumm : Summable T := summable_zeroSumTerm u
  have hsumm_re : Summable fun q => (T q).re := Complex.reCLM.summable hsumm
  set g : XiZeroCopy → ℝ := fun q => if q ∈ h.offLine then (T q).re else 0 with hg
  have hgsupp : ∀ q ∉ h.offLine, g q = 0 := fun q hq => by simp [hg, hq]
  have hgsum : Summable g := summable_of_ne_finset_zero hgsupp
  have hS : Summable fun q : XiZeroCopy => K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hle : ∀ q, (T q).re ≤ g q + K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q
    simp only [hg]
    split_ifs with hq
    · have : 0 ≤ K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by positivity
      linarith
    · have him : (xiSpectralPoint q).im = 0 := by
        by_contra hne
        exact hq (h.mem_offLine.mpr hne)
      rw [zero_add]
      exact re_zeroSumTerm_le_of_im_eq_zero hu1 u.hasCompactSupport him
        (xiSpectralPoint_ne_zero q)
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum hsumm]
  calc ∑' q, (T q).re ≤ ∑' q, (g q + K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
        hsumm_re.tsum_le_tsum hle (hgsum.add hS)
    _ = ∑' q, g q + ∑' q, K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := hgsum.tsum_add hS
    _ = ∑ q ∈ h.offLine, (T q).re +
          K ^ 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        rw [tsum_eq_sum hgsupp, tsum_mul_left]
        congr 1
        exact Finset.sum_congr rfl fun q hq => by simp [hg, hq]

/-! ## The truncated odd model -/

/-- The truncated odd model `g_a = g · 1_{[−a,a]}`. -/
def gTrunc (t δ a : ℝ) (x : ℝ) : ℂ :=
  (Icc (-a) a).indicator (fun x => ((oddModel t δ x : ℝ) : ℂ)) x

theorem oddModel_neg (t δ x : ℝ) : oddModel t δ (-x) = -oddModel t δ x := by
  unfold oddModel
  rw [mul_neg, mul_neg, Real.cos_neg, Real.sinh_neg]
  ring

theorem gTrunc_neg (t δ a x : ℝ) : gTrunc t δ a (-x) = -1 * gTrunc t δ a x := by
  unfold gTrunc
  by_cases hx : x ∈ Icc (-a) a
  · have hx' : -x ∈ Icc (-a) a := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, oddModel_neg]
    push_cast
    ring
  · have hx' : -x ∉ Icc (-a) a := fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
    ring

theorem gTrunc_conj (t δ a x : ℝ) : (starRingEnd ℂ) (gTrunc t δ a x) = gTrunc t δ a x := by
  unfold gTrunc
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx, Complex.conj_ofReal]
  · rw [Set.indicator_of_notMem hx, map_zero]

theorem memLp_gTrunc (t δ a : ℝ) : MemLp (gTrunc t δ a) 2 :=
  memLp_indicator_Icc (by unfold oddModel; fun_prop) a

theorem integral_norm_sq_gTrunc (t δ : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ x, ‖gTrunc t δ a x‖ ^ 2 = oddTestMass t δ a := by
  unfold gTrunc
  rw [integral_norm_sq_indicator_Icc ha, oddTestMass]
  congr 1
  funext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, oddModel]
  ring

theorem gTrunc_mul_eq (t δ a : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    gTrunc t δ a x * f x = gTrunc t δ a x * (Icc (-a) a).indicator f x := by
  unfold gTrunc
  by_cases hx : x ∈ Icc (-a) a <;> simp [hx]

theorem norm_testTransform_gTrunc_sq_le (t δ : ℝ) {a : ℝ} (ha : 0 ≤ a) (w : ℂ) :
    ‖testTransform (gTrunc t δ a) w‖ ^ 2 ≤
      oddTestMass t δ a * (2 * a * Real.exp (2 * a * |w.im|)) := by
  have hexp : Continuous fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ)) := by fun_prop
  have heq : testTransform (gTrunc t δ a) w = ∫ x, gTrunc t δ a x *
      (Icc (-a) a).indicator (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x := by
    unfold testTransform
    congr 1
    funext x
    exact gTrunc_mul_eq t δ a (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x
  rw [heq, ← integral_norm_sq_gTrunc t δ ha]
  refine (norm_integral_mul_sq_le (memLp_gTrunc t δ a) (memLp_indicator_Icc hexp a)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => by positivity)
  apply integral_norm_sq_indicator_le ha
  intro x hx
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * w * (x : ℂ)).re = -(w.im * x) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hx' : |x| ≤ a := abs_le.mpr ⟨hx.1, hx.2⟩
  have : -(w.im * x) ≤ |w.im| * a := by
    have h1 : -(w.im * x) ≤ |w.im * x| := neg_le_abs _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg w.im]
  push_cast
  linarith

/-- The interval integral of an odd continuous function over `[−a, a]` vanishes. -/
theorem intervalIntegral_odd_eq_zero {f : ℝ → ℂ} (hf : ∀ x, f (-x) = -f x) (a : ℝ) :
    ∫ x in (-a)..a, f x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) f
  rw [neg_neg] at h
  have h2 : ∫ x in (-a)..a, f (-x) = -∫ x in (-a)..a, f x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => hf x
  rw [h2] at h
  have : (2 : ℂ) * ∫ x in (-a)..a, f x = 0 := by linear_combination -h
  simpa using this

theorem oddModel_mul_exp (t δ x : ℝ) :
    ((oddModel t δ x : ℝ) : ℂ) * Complex.exp (Complex.I * (⟨t, δ⟩ : ℂ) * (x : ℂ)) =
      ((((-(2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2)) : ℝ) : ℂ) +
        Complex.I * (((2 * Real.cos (t * x) * Real.sinh (δ * x) *
          (Real.sin (t * x) * Real.cosh (δ * x))) : ℝ) : ℂ)) +
      ((((2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) * Real.cosh (δ * x)) : ℝ) : ℂ) +
        Complex.I * (((-(2 * Real.cos (t * x) * Real.sin (t * x) * Real.sinh (δ * x) ^ 2)) :
          ℝ) : ℂ)) := by
  have hexp : Complex.I * (⟨t, δ⟩ : ℂ) * (x : ℂ) =
      ((-(δ * x) : ℝ) : ℂ) + ((t * x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hch : Real.exp (-(δ * x)) = Real.cosh (δ * x) - Real.sinh (δ * x) :=
    (Real.cosh_sub_sinh _).symm
  rw [hexp, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, hch, oddModel]
  push_cast
  ring

/-- **The top transform of the truncated odd model:** `ĝ_a(t+iδ) = −D⁻/2 + i I`. -/
theorem testTransform_gTrunc_top (t δ : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    testTransform (gTrunc t δ a) ⟨t, δ⟩ =
      -((oddTestMass t δ a : ℂ) / 2) + Complex.I * (oddTestCross t δ a : ℂ) := by
  have hcongr : testTransform (gTrunc t δ a) ⟨t, δ⟩ =
      ∫ x in (-a)..a, ((oddModel t δ x : ℝ) : ℂ) *
        Complex.exp (Complex.I * (⟨t, δ⟩ : ℂ) * (x : ℂ)) := by
    unfold testTransform gTrunc
    have hfun : (fun x : ℝ => (Icc (-a) a).indicator (fun x => ((oddModel t δ x : ℝ) : ℂ)) x *
        Complex.exp (Complex.I * (⟨t, δ⟩ : ℂ) * (x : ℂ))) =
        (Icc (-a) a).indicator (fun x : ℝ => ((oddModel t δ x : ℝ) : ℂ) *
          Complex.exp (Complex.I * (⟨t, δ⟩ : ℂ) * (x : ℂ))) := by
      funext x
      by_cases hx : x ∈ Icc (-a) a <;> simp [hx]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith)]
  rw [hcongr]
  have hpt := oddModel_mul_exp t δ
  simp_rw [hpt]
  have hc : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable (fun x => ((f x : ℝ) : ℂ)) volume (-a) a :=
    fun f hf => (Complex.continuous_ofReal.comp hf).intervalIntegrable _ _
  have hA : Continuous fun x : ℝ => -(2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2) := by
    fun_prop
  have hB : Continuous fun x : ℝ => 2 * Real.cos (t * x) * Real.sinh (δ * x) *
      (Real.sin (t * x) * Real.cosh (δ * x)) := by fun_prop
  have hC : Continuous fun x : ℝ => 2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) *
      Real.cosh (δ * x) := by fun_prop
  have hD : Continuous fun x : ℝ =>
      -(2 * Real.cos (t * x) * Real.sin (t * x) * Real.sinh (δ * x) ^ 2) := by fun_prop
  have hodd : ∫ x in (-a)..a,
      ((((2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) * Real.cosh (δ * x)) : ℝ) : ℂ) +
        Complex.I * ((-(2 * Real.cos (t * x) * Real.sin (t * x) * Real.sinh (δ * x) ^ 2) :
          ℝ) : ℂ)) = 0 := by
    apply intervalIntegral_odd_eq_zero
    intro x
    push_cast
    simp only [mul_neg, Complex.cos_neg, Complex.sin_neg, Complex.sinh_neg, Complex.cosh_neg]
    ring
  rw [intervalIntegral.integral_add ((hc _ hA).add ((hc _ hB).const_mul _))
      ((hc _ hC).add ((hc _ hD).const_mul _)), hodd, add_zero,
    intervalIntegral.integral_add (hc _ hA) ((hc _ hB).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  have hmass : (∫ x in (-a)..a, -(2 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2)) =
      -(oddTestMass t δ a / 2) := by
    rw [oddTestMass, intervalIntegral.integral_neg, ← intervalIntegral.integral_div]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hmass, oddTestCross]
  push_cast
  ring

/-- `conj ĝ_a(σ̄) = −ĝ_a(σ)`. -/
theorem conj_testTransform_gTrunc_conj (t δ a : ℝ) (σ : ℂ) :
    (starRingEnd ℂ) (testTransform (gTrunc t δ a) ((starRingEnd ℂ) σ)) =
      -testTransform (gTrunc t δ a) σ := by
  have hconj := testTransform_conj (gTrunc t δ a) (-σ)
  have hfun : (fun x => (starRingEnd ℂ) (gTrunc t δ a x)) = gTrunc t δ a :=
    funext (gTrunc_conj t δ a)
  rw [hfun, map_neg, neg_neg] at hconj
  rw [← hconj, testTransform_neg_of_reflect (s := -1) (gTrunc_neg t δ a)]
  ring

/-- The top quartet of the truncated odd model contributes `−(D⁻²/4 − I²)` per copy. -/
theorem re_top_gTrunc (t δ : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (testTransform (gTrunc t δ a) ⟨t, δ⟩ *
        (starRingEnd ℂ) (testTransform (gTrunc t δ a) ((starRingEnd ℂ) ⟨t, δ⟩))).re =
      -(oddTestMass t δ a ^ 2 / 4 - oddTestCross t δ a ^ 2) := by
  rw [conj_testTransform_gTrunc_conj, testTransform_gTrunc_top t δ ha]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  ring

/-! ## The approximating sequence -/

theorem seqWidth_pos (a : SuzukiPositiveAperture) (n : ℕ) : 0 < a.1 / ((n : ℝ) + 6) :=
  div_pos a.2 (by positivity)

theorem four_mul_seqWidth_lt (a : SuzukiPositiveAperture) (n : ℕ) :
    4 * (a.1 / ((n : ℝ) + 6)) < a.1 := by
  have ha := a.2
  have hn : (0 : ℝ) < (n : ℝ) + 6 := by positivity
  rw [mul_div_assoc', div_lt_iff₀ hn]
  nlinarith

/-- The smooth odd tests `v_n` with cutoff width `a/(n+6)`. -/
def oddTestSeq (t δ : ℝ) (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMComplexSmoothInteriorSource a :=
  oddTestSource t δ a (seqWidth_pos a n) (four_mul_seqWidth_lt a n)

theorem norm_oddTestSeq_le (t δ : ℝ) (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) :
    ‖(oddTestSeq t δ a n : ℝ → ℂ) x‖ ≤ ‖gTrunc t δ a.1 x‖ := by
  set ε := a.1 / ((n : ℝ) + 6) with hε_def
  have hε := seqWidth_pos a n
  have h4 := four_mul_seqWidth_lt a n
  rw [oddTestSeq, oddTestSource_apply, Complex.norm_real, Real.norm_eq_abs, gTrunc]
  by_cases hx : x ∈ Icc (-a.1) a.1
  · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (cutoff_nonneg hε (by linarith) x)]
    exact mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one hε (by linarith) x)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    have hxa : a.1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith [a.2])]; linarith
      · rw [abs_of_pos (by linarith [a.2])]; exact h
    rw [cutoff_eq_zero hε (by linarith) (by linarith)]
    simp

theorem tendsto_oddTestSeq (t δ : ℝ) (a : SuzukiPositiveAperture) {x : ℝ} (hx : |x| ≠ a.1) :
    Tendsto (fun n => (oddTestSeq t δ a n : ℝ → ℂ) x) atTop (𝓝 (gTrunc t δ a.1 x)) := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · -- interior point: eventually the cutoff is one
    have hgap : 0 < a.1 - |x| := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (5 * a.1 / (a.1 - |x|))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hε := seqWidth_pos a n
    have hn' : (5 * a.1 / (a.1 - |x|)) < (n : ℝ) + 6 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcut : |x| ≤ a.1 - 3 * (a.1 / ((n : ℝ) + 6)) - 2 * (a.1 / ((n : ℝ) + 6)) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 6 := by positivity
      rw [div_lt_iff₀ hgap] at hn'
      have : 5 * (a.1 / ((n : ℝ) + 6)) ≤ a.1 - |x| := by
        rw [mul_div_assoc', div_le_iff₀ hpos]
        nlinarith
      linarith
    have hxI : x ∈ Icc (-a.1) a.1 := abs_le.mp hlt.le
    rw [oddTestSeq, oddTestSource_apply, cutoff_eq_one hε hcut, mul_one, gTrunc,
      Set.indicator_of_mem hxI]
  · -- exterior point: everything vanishes
    have hxI : x ∉ Icc (-a.1) a.1 := fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    have hε := seqWidth_pos a n
    have h4 := four_mul_seqWidth_lt a n
    rw [oddTestSeq, oddTestSource_apply, gTrunc, Set.indicator_of_notMem hxI,
      cutoff_eq_zero hε (by linarith) (by linarith)]
    simp

theorem ae_ne_abs (A : ℝ) : ∀ᵐ x : ℝ, |x| ≠ A := by
  have hfin : ({A, -A} : Set ℝ).Countable := (Set.toFinite _).countable
  have hnull : volume ({A, -A} : Set ℝ) = 0 := hfin.measure_zero volume
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_setOf_eq, not_not] at hx
  rcases abs_eq (show 0 ≤ A from hx ▸ abs_nonneg x) |>.mp hx with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem abs_gTrunc_le (t δ : ℝ) {a : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    ‖gTrunc t δ a x‖ ≤ (Icc (-a) a).indicator (fun _ => 2 * Real.cosh (δ * a)) x := by
  unfold gTrunc
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
    exact abs_oddModel_le hδ (abs_le.mpr ⟨hx.1, hx.2⟩)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]

/-- The transforms of `v_n` converge to the transform of the truncated model. -/
theorem tendsto_testTransform_oddTestSeq (t δ : ℝ) (hδ : 0 ≤ δ) (a : SuzukiPositiveAperture)
    (w : ℂ) :
    Tendsto (fun n => testTransform (oddTestSeq t δ a n) w) atTop
      (𝓝 (testTransform (gTrunc t δ a.1) w)) := by
  unfold testTransform
  set E : ℝ := Real.exp (a.1 * |w.im|) with hE
  apply tendsto_integral_of_dominated_convergence
    (fun x => (Icc (-a.1) a.1).indicator (fun _ => 2 * Real.cosh (δ * a.1) * E) x)
  · intro n
    exact ((oddTestSeq t δ a n).continuous.mul (by fun_prop)).aestronglyMeasurable
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    by_cases hx : x ∈ Icc (-a.1) a.1
    · rw [Set.indicator_of_mem hx]
      have h1 := (norm_oddTestSeq_le t δ a n x).trans (abs_gTrunc_le t δ hδ x)
      rw [Set.indicator_of_mem hx] at h1
      have h2 : ‖Complex.exp (Complex.I * w * (x : ℂ))‖ ≤ E := by
        rw [Complex.norm_exp, hE]
        apply Real.exp_le_exp.mpr
        have hre : (Complex.I * w * (x : ℂ)).re = -(w.im * x) := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        have hx' : |x| ≤ a.1 := abs_le.mpr ⟨hx.1, hx.2⟩
        have h1 : -(w.im * x) ≤ |w.im * x| := neg_le_abs _
        rw [abs_mul] at h1
        nlinarith [abs_nonneg w.im]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hx]
      have h1 := (norm_oddTestSeq_le t δ a n x).trans (abs_gTrunc_le t δ hδ x)
      rw [Set.indicator_of_notMem hx] at h1
      have : ‖(oddTestSeq t δ a n : ℝ → ℂ) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [this, zero_mul]
  · filter_upwards [ae_ne_abs a.1] with x hx
    exact (tendsto_oddTestSeq t δ a hx).mul_const _

/-- The physical masses of `v_n` converge to `D⁻(a)`. -/
theorem tendsto_integral_norm_sq_oddTestSeq (t δ : ℝ) (hδ : 0 ≤ δ) (a : SuzukiPositiveAperture) :
    Tendsto (fun n => ∫ x, ‖(oddTestSeq t δ a n : ℝ → ℂ) x‖ ^ 2) atTop
      (𝓝 (oddTestMass t δ a.1)) := by
  rw [← integral_norm_sq_gTrunc t δ a.2.le]
  apply tendsto_integral_of_dominated_convergence
    (fun x => (Icc (-a.1) a.1).indicator (fun _ => (2 * Real.cosh (δ * a.1)) ^ 2) x)
  · intro n
    exact ((oddTestSeq t δ a n).continuous.norm.pow 2).aestronglyMeasurable
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := (norm_oddTestSeq_le t δ a n x).trans (abs_gTrunc_le t δ hδ x)
    by_cases hx : x ∈ Icc (-a.1) a.1
    · rw [Set.indicator_of_mem hx] at h1 ⊢
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hx] at h1 ⊢
      have : ‖(oddTestSeq t δ a n : ℝ → ℂ) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [this]
      norm_num
  · filter_upwards [ae_ne_abs a.1] with x hx
    exact ((tendsto_oddTestSeq t δ a hx).norm).pow 2

end

end RHTower.CCMParityQuartet
