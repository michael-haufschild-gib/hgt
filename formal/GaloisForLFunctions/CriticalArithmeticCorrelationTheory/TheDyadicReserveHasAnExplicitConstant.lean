import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The dyadic seventh-power reserve has an explicit constant

The reserve `exists_top_archForm_dyadic_seventh_reserve` localizes with a classically chosen bump, so
its constant carries no value. Here the plateau bump is the concrete smooth transition
`B(t) = S(2 − |t|)`, whose slope is at most `8`:

`S′(x) = ab (1/x² + 1/(1−x)²)/(a+b)²` with `a = e^{−1/x}`, `b = e^{−1/(1−x)}`, and for `x ≤ 1/2` this is
at most `(2/x²) e² e^{−1/x} ≤ 8`, because `t² e^{−t} ≤ 4 e^{−2}`.

The tilted spline has the explicit bounds `|φ| ≤ e⁴/2`, `|φ′| ≤ 6 e⁴`. The IMS localization then runs
unchanged and gives `dyadicArchConstant`, a closed expression in `G₀`, `θ′(0)` and these bounds.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix CompactlySupported

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory BiScaleUncertainty.ChebyshevGauge

/-! ### The slope of the smooth transition -/

private theorem sq_mul_exp_neg_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t) ≤ 4 * Real.exp (-2) := by
  have h := Real.add_one_le_exp (t / 2 - 1)
  have hle : t / 2 ≤ Real.exp (t / 2 - 1) := by linarith only [h]
  have hsq := pow_le_pow_left₀ (by positivity) hle 2
  have he : Real.exp (t / 2 - 1) ^ 2 = Real.exp (t - 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he] at hsq
  have hne : Real.exp (t - 2) * Real.exp (-t) = Real.exp (-2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hm := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-t)).le
  rw [hne] at hm
  nlinarith only [hm]

/-- The derivative of the transition in the open unit interval. -/
private theorem hasDerivAt_smoothTransition {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt Real.smoothTransition
      (Real.exp (-x⁻¹) * Real.exp (-(1 - x)⁻¹) * ((x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹) /
        (Real.exp (-x⁻¹) + Real.exp (-(1 - x)⁻¹)) ^ 2) x := by
  have hx1 : 0 < 1 - x := by linarith only [h1]
  have ha : HasDerivAt (fun y : ℝ => Real.exp (-y⁻¹)) (Real.exp (-x⁻¹) * (x ^ 2)⁻¹) x := by
    have hi : HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
      have h := (hasDerivAt_inv h0.ne').neg
      rw [neg_neg] at h
      exact h
    exact hi.exp
  have hb : HasDerivAt (fun y : ℝ => Real.exp (-(1 - y)⁻¹))
      (-(Real.exp (-(1 - x)⁻¹) * ((1 - x) ^ 2)⁻¹)) x := by
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
    have hi : HasDerivAt (fun y : ℝ => -(1 - y)⁻¹) (-((1 - x) ^ 2)⁻¹) x := by
      refine HasDerivAt.congr_deriv
        (show HasDerivAt (fun y : ℝ => -(1 - y)⁻¹) _ x from (hsub.inv hx1.ne').neg) ?_
      ring
    refine hi.exp.congr_deriv ?_
    ring
  have hsum := ha.add hb
  have hne : Real.exp (-x⁻¹) + Real.exp (-(1 - x)⁻¹) ≠ 0 := by positivity
  have hdiv := ha.div hsum hne
  have hev : Real.smoothTransition =ᶠ[𝓝 x] fun y : ℝ =>
      Real.exp (-y⁻¹) / (Real.exp (-y⁻¹) + Real.exp (-(1 - y)⁻¹)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    have hy1 : 0 < 1 - y := by linarith only [hy.2]
    simp only [Real.smoothTransition, expNegInvGlue, if_neg (not_le.mpr hy.1),
      if_neg (not_le.mpr hy1)]
  refine (hdiv.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [Pi.add_apply]
  congr 1
  ring

private theorem abs_deriv_smoothTransition_le_of_half {x : ℝ} (h0 : 0 < x) (hx : x ≤ 1 / 2) :
    Real.exp (-x⁻¹) * Real.exp (-(1 - x)⁻¹) * ((x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹) /
      (Real.exp (-x⁻¹) + Real.exp (-(1 - x)⁻¹)) ^ 2 ≤ 8 := by
  obtain ⟨a, ha⟩ : ∃ a, a = Real.exp (-x⁻¹) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.exp (-(1 - x)⁻¹) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha0 : 0 < a := ha ▸ Real.exp_pos _
  have hb0 : 0 < b := hb ▸ Real.exp_pos _
  have hx1 : 0 < 1 - x := by linarith only [hx]
  have hxx : x ≤ 1 - x := by linarith only [hx]
  have hinv : ((1 - x) ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le hxx 2)
  have hsum : (x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹ ≤ 2 * (x ^ 2)⁻¹ := by linarith only [hinv]
  have hratio : a / b ≤ Real.exp 2 * Real.exp (-x⁻¹) := by
    have hle2 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx1 (by norm_num)]
      linarith only [hx]
    rw [ha, hb, ← Real.exp_sub, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hle2])
  have hquot : a * b / (a + b) ^ 2 ≤ a / b := by
    rw [div_le_div_iff₀ (by positivity) hb0]
    nlinarith only [mul_pos ha0 ha0, mul_pos ha0 hb0, mul_pos hb0 hb0,
      mul_pos (mul_pos ha0 ha0) hb0, mul_pos ha0 (mul_pos ha0 hb0), mul_pos ha0 (mul_pos hb0 hb0)]
  have ht : (x⁻¹) ^ 2 * Real.exp (-x⁻¹) ≤ 4 * Real.exp (-2) :=
    sq_mul_exp_neg_le _ (inv_nonneg.mpr h0.le)
  have hee : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
  have hstep : a * b * ((x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹) / (a + b) ^ 2 ≤
      (Real.exp 2 * Real.exp (-x⁻¹)) * (2 * (x ^ 2)⁻¹) := by
    calc a * b * ((x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹) / (a + b) ^ 2
        = (a * b / (a + b) ^ 2) * ((x ^ 2)⁻¹ + ((1 - x) ^ 2)⁻¹) := by ring
      _ ≤ _ := mul_le_mul (hquot.trans hratio) hsum (by positivity) (by positivity)
  refine hstep.trans ?_
  have hinvsq : (x ^ 2)⁻¹ = (x⁻¹) ^ 2 := by rw [inv_pow]
  rw [hinvsq]
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * Real.exp 2)
  calc Real.exp 2 * Real.exp (-x⁻¹) * (2 * (x⁻¹) ^ 2)
      = 2 * Real.exp 2 * ((x⁻¹) ^ 2 * Real.exp (-x⁻¹)) := by ring
    _ ≤ 2 * Real.exp 2 * (4 * Real.exp (-2)) := hm
    _ = 8 * (Real.exp 2 * Real.exp (-2)) := by ring
    _ = 8 := by rw [hee, mul_one]

/-- **The smooth transition has slope at most `8`.** -/
theorem abs_deriv_smoothTransition_le (x : ℝ) : |deriv Real.smoothTransition x| ≤ 8 := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  have hclosed : IsClosed {x : ℝ | |deriv Real.smoothTransition x| ≤ 8} :=
    isClosed_le hcont.abs continuous_const
  have hdense : Dense (({0, 1} : Set ℝ)ᶜ) :=
    (Set.Countable.dense_compl ℝ (Set.toFinite _).countable)
  have hsub : ({0, 1} : Set ℝ)ᶜ ⊆ {x : ℝ | |deriv Real.smoothTransition x| ≤ 8} := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (by simp [h])
    have hy1 : y ≠ 1 := fun h => hy (by simp [h])
    change |deriv Real.smoothTransition y| ≤ 8
    rcases lt_or_gt_of_ne hy0 with h | h
    · have hev : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with z hz
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
      rw [hev.deriv_eq, deriv_const]
      norm_num
    · rcases lt_or_gt_of_ne hy1 with h' | h'
      · rw [(hasDerivAt_smoothTransition h h').deriv]
        have hval : 0 ≤ Real.exp (-y⁻¹) * Real.exp (-(1 - y)⁻¹) * ((y ^ 2)⁻¹ + ((1 - y) ^ 2)⁻¹) /
            (Real.exp (-y⁻¹) + Real.exp (-(1 - y)⁻¹)) ^ 2 := by positivity
        rw [abs_of_nonneg hval]
        by_cases hhalf : y ≤ 1 / 2
        · exact abs_deriv_smoothTransition_le_of_half h hhalf
        · have hz0 : 0 < 1 - y := by linarith only [h']
          have hz : 1 - y ≤ 1 / 2 := by linarith only [hhalf, not_le.mp hhalf]
          have hsym := abs_deriv_smoothTransition_le_of_half hz0 hz
          rw [show 1 - (1 - y) = y by ring] at hsym
          refine le_trans (le_of_eq ?_) hsym
          ring
      · have hev : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds h'] with z hz
          exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
        rw [hev.deriv_eq, deriv_const]
        norm_num
  have hall := hclosed.closure_subset_iff.mpr hsub
  rw [hdense.closure_eq] at hall
  exact hall (Set.mem_univ x)

/-- The smooth transition is `8`-Lipschitz. -/
theorem abs_smoothTransition_sub_le (a b : ℝ) :
    |Real.smoothTransition a - Real.smoothTransition b| ≤ 8 * |a - b| := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun x _ => hdiff.differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_deriv_smoothTransition_le x)
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa only [Real.norm_eq_abs] using hmvt

/-! ### The explicit plateau bump -/

/-- The explicit plateau bump: equal to `1` on `[-1, 1]`, supported in `[-2, 2]`. -/
def baseShellBump (t : ℝ) : ℝ := Real.smoothTransition (2 - |t|)

/-- The Lipschitz constant of the plateau bump. -/
def shellBumpSlope : ℝ := 8

theorem baseShellBump_nonneg (t : ℝ) : 0 ≤ (baseShellBump : ℝ → ℝ) t :=
  Real.smoothTransition.nonneg _

theorem baseShellBump_le_one (t : ℝ) : (baseShellBump : ℝ → ℝ) t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem contDiff_baseShellBump {n : ℕ∞} : ContDiff ℝ n (baseShellBump : ℝ → ℝ) := by
  have hsm := (ContDiffBumpBase.ofInnerProductSpace ℝ).smooth
  have hmap : ContDiff ℝ n (fun t : ℝ => ((2 : ℝ), t)) := contDiff_const.prodMk contDiff_id
  have hOn := (hsm.of_le (by exact_mod_cast le_top)).comp_contDiff (n := n) hmap
    (fun t => by simp)
  have hfun : (baseShellBump : ℝ → ℝ) =
      Function.uncurry (ContDiffBumpBase.ofInnerProductSpace ℝ).toFun ∘ fun t : ℝ => ((2 : ℝ), t) := by
    funext t
    simp only [baseShellBump, Function.comp, Function.uncurry, ContDiffBumpBase.ofInnerProductSpace,
      Real.norm_eq_abs]
    norm_num
  rw [hfun]
  exact hOn

theorem baseShellBump_eq_one {t : ℝ} (ht : |t| ≤ 1) : (baseShellBump : ℝ → ℝ) t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [ht])

theorem baseShellBump_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : (baseShellBump : ℝ → ℝ) t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [ht])

theorem hasCompactSupport_baseShellBump : HasCompactSupport (baseShellBump : ℝ → ℝ) :=
  HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun t ht => by
    refine baseShellBump_eq_zero ?_
    by_contra h
    exact ht (abs_le.mp (not_le.mp h).le)

theorem exists_baseShellBump_deriv_bound :
    ∃ L_B : ℝ, L_B = shellBumpSlope ∧ 0 ≤ L_B ∧
      (∀ t, |deriv (baseShellBump : ℝ → ℝ) t| ≤ L_B) ∧
      ∀ a b, |(baseShellBump : ℝ → ℝ) a - (baseShellBump : ℝ → ℝ) b| ≤ L_B * |a - b| := by
  have hlip : ∀ a b, |(baseShellBump : ℝ → ℝ) a - (baseShellBump : ℝ → ℝ) b| ≤ 8 * |a - b| := by
    intro a b
    refine (abs_smoothTransition_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    rw [show 2 - |a| - (2 - |b|) = -(|a| - |b|) by ring, abs_neg]
    exact abs_abs_sub_abs_le a b
  refine ⟨8, rfl, by norm_num, fun t => ?_, hlip⟩
  have hL : LipschitzWith 8 (baseShellBump : ℝ → ℝ) := LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using hlip a b
  simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using norm_deriv_le_of_lipschitz (x₀ := t) hL

/-! ### Sup bounds of the tilted spline -/

/-- The explicit sup bound of the tilted spline. -/
def splineSupBound : ℝ := Real.exp 4 / 2

/-- The explicit sup bound of the derivative of the tilted spline. -/
def splineDerivSupBound : ℝ := 6 * Real.exp 4

theorem splineSupBound_nonneg : 0 ≤ splineSupBound := by unfold splineSupBound; positivity

theorem splineDerivSupBound_nonneg : 0 ≤ splineDerivSupBound := by
  unfold splineDerivSupBound; positivity

private theorem abs_cubicSpline_le (v : ℝ) :
    |cubicSpline v| ≤ 1 / 2 := by
  rw [abs_of_nonneg (cubicSpline_nonneg v)]
  exact cubicSpline_le_half v

private theorem abs_deriv_cubicSpline_le (v : ℝ) :
    |deriv cubicSpline v| ≤ 1 / 4 :=
  abs_deriv_cubicSpline_le_quarter v

private theorem deriv_cubicSpline_eq_zero {v : ℝ} (hv : 4 < |v|) :
    deriv cubicSpline v = 0 := by
  have hev : cubicSpline =ᶠ[𝓝 v] fun _ => 0 := by
    have hopen : IsOpen {w : ℝ | 4 < |w|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hv] with w hw
    exact cubicSpline_eq_zero hw
  rw [hev.deriv_eq, deriv_const]

theorem abs_tiltedUnitSpline_le (t : ℝ) : |tiltedUnitSpline t| ≤ splineSupBound := by
  obtain ⟨v, hv⟩ : ∃ v, v = (t - 1 / 2) / (1 / 8) := ⟨_, rfl⟩
  have he : tiltedUnitSpline t = Real.exp v * cubicSpline v := by
    simp only [tiltedUnitSpline, atomDilate, splineProbe,
      tiltedSource, one_mul, hv]
  rw [he, abs_mul, Real.abs_exp]
  unfold splineSupBound
  by_cases hbig : 4 < |v|
  · rw [cubicSpline_eq_zero hbig, abs_zero, mul_zero]
    positivity
  · have hv4 : v ≤ 4 := (le_abs_self v).trans (not_lt.mp hbig)
    have h1 : Real.exp v ≤ Real.exp 4 := Real.exp_le_exp.mpr hv4
    calc Real.exp v * |cubicSpline v| ≤ Real.exp 4 * (1 / 2) :=
          mul_le_mul h1 (abs_cubicSpline_le v) (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring

theorem abs_deriv_tiltedUnitSpline_le (t : ℝ) : |deriv tiltedUnitSpline t| ≤ splineDerivSupBound := by
  obtain ⟨v, hv⟩ : ∃ v, v = (t - 1 / 2) / (1 / 8) := ⟨_, rfl⟩
  have hdB : DifferentiableAt ℝ cubicSpline v :=
    (contDiff_cubicSpline.differentiable (by norm_num)) v
  have hprobe : HasDerivAt (fun w : ℝ => Real.exp w * cubicSpline w)
      (Real.exp v * cubicSpline v +
        Real.exp v * deriv cubicSpline v) v :=
    (Real.hasDerivAt_exp v).mul hdB.hasDerivAt
  have hinner : HasDerivAt (fun s : ℝ => (s - 1 / 2) / (1 / 8)) (1 / (1 / 8)) t :=
    ((hasDerivAt_id t).sub_const (1 / 2)).div_const (1 / 8)
  have hcomp := HasDerivAt.comp (h₂ := fun w : ℝ => Real.exp w * cubicSpline w)
    t (hv ▸ hprobe) hinner
  have hfun : tiltedUnitSpline = (fun w : ℝ => Real.exp w * cubicSpline w) ∘
      fun s : ℝ => (s - 1 / 2) / (1 / 8) := by
    funext s
    simp only [tiltedUnitSpline, atomDilate, splineProbe,
      tiltedSource, one_mul, Function.comp]
  rw [hfun, hcomp.deriv, ← hv]
  unfold splineDerivSupBound
  rw [abs_mul, show ((1 : ℝ) / (1 / 8)) = 8 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  by_cases hbig : 4 < |v|
  · rw [cubicSpline_eq_zero hbig, deriv_cubicSpline_eq_zero hbig]
    simp only [mul_zero, add_zero, abs_zero, zero_mul]
    exact (by positivity : (0 : ℝ) ≤ 6 * Real.exp 4)
  · have hv4 : v ≤ 4 := (le_abs_self v).trans (not_lt.mp hbig)
    have h1 : Real.exp v ≤ Real.exp 4 := Real.exp_le_exp.mpr hv4
    have hsum : |Real.exp v * cubicSpline v +
        Real.exp v * deriv cubicSpline v| ≤ Real.exp 4 * (3 / 4) := by
      rw [← mul_add, abs_mul, Real.abs_exp]
      refine mul_le_mul h1 ?_ (abs_nonneg _) (Real.exp_pos _).le
      have := abs_cubicSpline_le v
      have := abs_deriv_cubicSpline_le v
      refine (abs_add_le _ _).trans ?_
      linarith
    linarith only [hsum]

/-- The explicit commutator constant of the IMS localization. -/
def shellCommutatorConstant : ℝ :=
  18 * 13 * (shellBumpSlope * (splineSupBound + splineDerivSupBound)) ^ 2 * (Real.exp 1 + 1) /
    ∫ u, tiltedUnitSpline u ^ 2

/-- The explicit constant of the dyadic seventh-power archimedean reserve. -/
def dyadicArchConstant : ℝ :=
  (9 * ((factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
      (1 + 8 * Real.exp 1)) / 2 + shellCommutatorConstant +
    648 * shellBumpSlope ^ 2 * (1 + 2 * Real.exp 1)) / 18 +
    2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1)

/-! ### IMS localization -/

/-- Log-space center `log N − (k + 1) log 2` of the `k`-th dyadic shell below `N`. -/
def shellCenter (N k : ℕ) : ℝ := Real.log N - ((k : ℝ) + 1) * Real.log 2

/-- Smooth bump localized around `shellCenter N k`. -/
def dyadicShellBump (N k : ℕ) (u : ℝ) : ℝ := (baseShellBump : ℝ → ℝ) (u - shellCenter N k)

/-- Number of dyadic shells needed to cover `(N / linearDefectCutoff c, N]`. -/
def dyadicShellCount (c : ℝ) : ℕ := ⌊Real.log (linearDefectCutoff c) / Real.log 2⌋₊ + 1

theorem dyadicShellBump_nonneg (N k : ℕ) (u : ℝ) : 0 ≤ dyadicShellBump N k u :=
  baseShellBump_nonneg _

theorem dyadicShellBump_le_one (N k : ℕ) (u : ℝ) : dyadicShellBump N k u ≤ 1 :=
  baseShellBump_le_one _

theorem contDiff_dyadicShellBump (N k : ℕ) : ContDiff ℝ 2 (dyadicShellBump N k) :=
  (contDiff_baseShellBump (n := 2)).comp (contDiff_id.sub contDiff_const)

theorem dyadicShellBump_eq_zero {N k : ℕ} {u : ℝ} (hu : 2 ≤ |u - shellCenter N k|) :
    dyadicShellBump N k u = 0 :=
  baseShellBump_eq_zero hu

theorem dyadicShellBump_eq_one {N k : ℕ} {u : ℝ} (hu : |u - shellCenter N k| ≤ 1) :
    dyadicShellBump N k u = 1 :=
  baseShellBump_eq_one hu

/-- At any point `u`, at most `4 R + 1` dyadic shell centers lie within distance `R` of `u`. -/
theorem card_shellCenter_near_le (s : Finset ℕ) (N : ℕ) (u : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((s.filter fun k : ℕ => |u - shellCenter N k| ≤ R).card : ℝ) ≤ 4 * R + 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set a := (Real.log N - u) / Real.log 2 - 1
  have hsub : (s.filter fun k : ℕ => |u - shellCenter N k| ≤ R) ⊆
      s.filter fun k : ℕ => |((1 : ℕ) : ℝ) * k - a| ≤ R / Real.log 2 := by
    intro k hk
    obtain ⟨hks, hdist⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hks, ?_⟩
    rw [Nat.cast_one, one_mul, le_div_iff₀ hl2]
    have hid : ((k : ℝ) - a) * Real.log 2 = u - shellCenter N k := by
      dsimp only [a, shellCenter]
      field_simp [hl2.ne']
      ring
    rw [← abs_of_pos hl2, ← abs_mul, hid]
    exact hdist
  have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
    (card_mul_near_le s le_rfl a (div_nonneg hR hl2.le))
  rw [Nat.cast_one, div_one] at hcard
  have hdiv : R / Real.log 2 ≤ 2 * R := by
    rw [div_le_iff₀ hl2]
    nlinarith
  linarith

/-- **Smooth dyadic IMS inequality for the Lévy energy.** Summing `levyEnergy (χ_k · f)` across any
finite family of dyadic shells costs at most a bounded multiple of `levyEnergy f + ‖f‖₂²`. -/
theorem sum_levyEnergy_dyadicShellBump_mul_le {L_B : ℝ}
    (hlip : ∀ a b, |(baseShellBump : ℝ → ℝ) a - (baseShellBump : ℝ → ℝ) b| ≤ L_B * |a - b|)
    (s : Finset ℕ) (N : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * f u) ≤
      18 * levyEnergy f + 648 * L_B ^ 2 * ∫ u, f u ^ 2 := by
  have hχf : ∀ k, ContDiff ℝ 2 (fun u => dyadicShellBump N k u * f u) := fun k =>
    (contDiff_dyadicShellBump N k).mul hf
  have hχfc : ∀ k, HasCompactSupport (fun u => dyadicShellBump N k u * f u) := fun k =>
    hfc.mul_left
  have hsum_u : ∀ y > (0 : ℝ),
      (∑ k ∈ s, ∫ u, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
        18 * (∫ u, (f u - f (u + y)) ^ 2) + 36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2 := by
    intro y hy
    rw [← integral_finsetSum s fun k _ =>
      RHTower.WeilMarkovPole.integrable_sub_shift_sq (hχf k).continuous (hχfc k) y]
    have hpt : ∀ u : ℝ,
        (∑ k ∈ s, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
          18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := by
      intro u
      have hterm : ∀ k ∈ s,
          (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2 ≤
            2 * (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) * f (u + y) ^ 2 := by
        intro k _
        have hsplit : dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y) =
            dyadicShellBump N k u * (f u - f (u + y)) +
              (dyadicShellBump N k u - dyadicShellBump N k (u + y)) * f (u + y) := by ring
        have hsq2 : ∀ A B : ℝ, (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := fun A B => by
          nlinarith [sq_nonneg (A - B)]
        have h1 : dyadicShellBump N k u ^ 2 ≤ if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0 := by
          split_ifs with hle
          · have h0 := dyadicShellBump_nonneg N k u
            have h1' := dyadicShellBump_le_one N k u
            nlinarith
          · rw [dyadicShellBump_eq_zero (le_of_not_ge hle), sq, zero_mul]
        have h2 : (dyadicShellBump N k u - dyadicShellBump N k (u + y)) ^ 2 ≤
            L_B ^ 2 * y ^ 2 * ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
              (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) := by
          by_cases hu1 : |u - shellCenter N k| ≤ 2
          · have hl := hlip (u - shellCenter N k) (u + y - shellCenter N k)
            have hd : |(u - shellCenter N k) - (u + y - shellCenter N k)| = y := by
              rw [show (u - shellCenter N k) - (u + y - shellCenter N k) = -y by ring,
                abs_neg, abs_of_pos hy]
            rw [hd] at hl
            have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
            rw [sq_abs, mul_pow] at hsq
            have hind : (1 : ℝ) ≤ (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) := by
              rw [if_pos hu1]
              split_ifs <;> norm_num
            exact hsq.trans (le_mul_of_one_le_right (by positivity) hind)
          · by_cases hu2 : |u + y - shellCenter N k| ≤ 2
            · have hl := hlip (u - shellCenter N k) (u + y - shellCenter N k)
              have hd : |(u - shellCenter N k) - (u + y - shellCenter N k)| = y := by
                rw [show (u - shellCenter N k) - (u + y - shellCenter N k) = -y by ring,
                  abs_neg, abs_of_pos hy]
              rw [hd] at hl
              have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
              rw [sq_abs, mul_pow] at hsq
              have hind : (1 : ℝ) ≤ (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) := by
                rw [if_neg hu1, if_pos hu2]; norm_num
              exact hsq.trans (le_mul_of_one_le_right (by positivity) hind)
            · rw [dyadicShellBump_eq_zero (le_of_not_ge hu1),
                dyadicShellBump_eq_zero (le_of_not_ge hu2), sub_self, sq, zero_mul]
              positivity
        calc (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2
            ≤ 2 * (dyadicShellBump N k u * (f u - f (u + y))) ^ 2 +
                2 * ((dyadicShellBump N k u - dyadicShellBump N k (u + y)) * f (u + y)) ^ 2 := by
              rw [hsplit]; exact hsq2 _ _
          _ = 2 * dyadicShellBump N k u ^ 2 * (f u - f (u + y)) ^ 2 +
                2 * (dyadicShellBump N k u - dyadicShellBump N k (u + y)) ^ 2 * f (u + y) ^ 2 := by
              ring
          _ ≤ _ := (add_le_add
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 zero_le_two) (sq_nonneg _))
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 zero_le_two)
                (sq_nonneg _))).trans_eq (by ring)
      have hc1 : ∑ k ∈ s, (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 9 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        exact (card_shellCenter_near_le s N u (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
      have hc2 : ∑ k ∈ s, (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 9 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        exact (card_shellCenter_near_le s N (u + y) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
      calc ∑ k ∈ s, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2
          ≤ ∑ k ∈ s, (2 * (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) * f (u + y) ^ 2) :=
            sum_le_sum hterm
        _ = 2 * (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (∑ k ∈ s, if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) *
                f (u + y) ^ 2 := by
            rw [sum_add_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ← mul_sum, sum_add_distrib]
        _ ≤ 18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := by
            have ha := mul_le_mul_of_nonneg_right (show 2 * (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 18 by linarith) (sq_nonneg (f u - f (u + y)))
            have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) + (∑ k ∈ s, if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 18 by linarith) (by positivity : 0 ≤ 2 * L_B ^ 2 * y ^ 2)) (sq_nonneg (f (u + y)))
            linarith
    have hi1 : Integrable (fun u => 18 * (f u - f (u + y)) ^ 2) :=
      (RHTower.WeilMarkovPole.integrable_sub_shift_sq hf.continuous hfc y).const_mul 18
    have hi2 : Integrable (fun u => 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) :=
      ((integrable_sq_of_continuous hf.continuous hfc).comp_add_right y).const_mul
        (36 * L_B ^ 2 * y ^ 2)
    have himono : (∫ u, ∑ k ∈ s,
        (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
        ∫ u, (18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) :=
      integral_mono (integrable_finsetSum s fun k _ =>
        RHTower.WeilMarkovPole.integrable_sub_shift_sq (hχf k).continuous (hχfc k) y)
        (hi1.add hi2) hpt
    calc (∫ u, ∑ k ∈ s,
          (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2)
        ≤ ∫ u, (18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) := himono
      _ = (∫ u, 18 * (f u - f (u + y)) ^ 2) +
            ∫ u, 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := integral_add hi1 hi2
      _ = 18 * (∫ u, (f u - f (u + y)) ^ 2) + 36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2 := by
          rw [integral_const_mul, integral_const_mul,
            integral_add_right_eq_self (fun u => f u ^ 2) y]
  have hsum_y : ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * f u) =
      ∫ y in Set.Ioi (0 : ℝ), ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y := by
    unfold levyEnergy
    exact (integral_finsetSum s fun k _ => integrableOn_levyIntegrand (hχf k) (hχfc k)).symm
  rw [hsum_y]
  have hiL : IntegrableOn (fun y => 18 * levyIntegrand f y) (Set.Ioi 0) :=
    (integrableOn_levyIntegrand hf hfc).const_mul 18
  have hiM : IntegrableOn (fun y => (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y))
      (Set.Ioi 0) :=
    RHTower.integrableOn_sq_mul_archLevyDensity.const_mul _
  have hmono : (∫ y in Set.Ioi (0 : ℝ),
        ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y) ≤
      ∫ y in Set.Ioi (0 : ℝ),
        (18 * levyIntegrand f y +
          (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y)) :=
    setIntegral_mono_on
      (integrable_finsetSum s fun k _ => integrableOn_levyIntegrand (hχf k) (hχfc k))
      (hiL.add hiM) measurableSet_Ioi fun y hy => by
        have hω := (archLevyDensity_pos hy).le
        calc ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y
            = archLevyDensity y * ∑ k ∈ s, ∫ u,
                (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2 := by
              unfold levyIntegrand; rw [mul_sum]
          _ ≤ archLevyDensity y * (18 * (∫ u, (f u - f (u + y)) ^ 2) +
                36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2) :=
              mul_le_mul_of_nonneg_left (hsum_u y hy) hω
          _ = 18 * levyIntegrand f y +
                (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y) := by
              unfold levyIntegrand; ring
  have hsplit_int : (∫ y in Set.Ioi (0 : ℝ),
        (18 * levyIntegrand f y +
          (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y))) =
      18 * levyEnergy f + (36 * L_B ^ 2 * ∫ u, f u ^ 2) * RHTower.levySecondMoment := by
    rw [integral_add hiL hiM, integral_const_mul, integral_const_mul]
    rfl
  have hf2 : 0 ≤ 36 * L_B ^ 2 * ∫ u, f u ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  have hm2 := mul_le_mul_of_nonneg_left RHTower.levySecondMoment_le hf2
  linarith [hmono, hsplit_int, hm2]

/-! ### Shell horizon and point-multiplier commutator in `H¹` -/

/-- Effective integer horizon `min N ⌊4 N / 2^k⌋₊` of the `k`-th dyadic shell. -/
def dyadicShellHorizon (N k : ℕ) : ℕ := min N ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊

/-- Every integer `n ≤ N` above `dyadicShellHorizon N k` lies strictly outside the support of
`dyadicShellBump N k (log ·)`. -/
theorem dyadicShellBump_log_eq_zero_of_gt_horizon {N k n : ℕ} (hN : 1 ≤ N) (hnN : n ≤ N)
    (hgt : dyadicShellHorizon N k < n) :
    dyadicShellBump N k (Real.log n) = 0 := by
  have hfl : ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ < n := by
    unfold dyadicShellHorizon at hgt
    omega
  have hlt : 4 * (N : ℝ) / (2 : ℝ) ^ k < n := Nat.lt_of_floor_lt hfl
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hlt
  have he2 : Real.exp 2 < 8 := by
    have he1 : Real.exp 1 < 11 / 4 := by have := Real.exp_one_lt_d9; linarith
    have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he2']
    nlinarith [Real.exp_pos 1]
  have hexp_sc : Real.exp (shellCenter N k + 2) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
    have hid : shellCenter N k + 2 = Real.log N - (k : ℝ) * Real.log 2 + (2 - Real.log 2) := by
      unfold shellCenter; ring
    rw [hid, Real.exp_add, Real.exp_sub, Real.exp_log hNR,
      show (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) by rw [Real.log_pow],
      Real.exp_log (by positivity), Real.exp_sub, Real.exp_log zero_lt_two]
    have h4 : Real.exp 2 / 2 ≤ 4 := by linarith
    calc (N : ℝ) / (2 : ℝ) ^ k * (Real.exp 2 / 2)
        ≤ (N : ℝ) / (2 : ℝ) ^ k * 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := by ring
  have hlog_gt : shellCenter N k + 2 < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos _) (hexp_sc.trans_lt hlt)
    rwa [Real.log_exp] at this
  exact dyadicShellBump_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)

/-- Because `dyadicShellBump N k (log n)` vanishes for `dyadicShellHorizon N k < n ≤ N`, the shell
atomic test at horizon `dyadicShellHorizon N k` equals the atomic test at horizon `N`. -/
theorem atomicTest_dyadicShellHorizon_eq {N k : ℕ} (hN : 1 ≤ N) (y : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest (dyadicShellHorizon N k) (fun n => dyadicShellBump N k (Real.log n) * y n) g =
      atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g := by
  funext u
  unfold atomicTest
  refine sum_subset (Icc_subset_Icc le_rfl (min_le_left N _)) fun n hn hnot => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hgt : dyadicShellHorizon N k < n := by
    by_contra hle
    exact hnot (mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
  dsimp only
  rw [dyadicShellBump_log_eq_zero_of_gt_horizon hN hnN hgt, zero_mul, zero_mul]

/-- **Dyadic commutator bound in Lévy energy.** Replacing smooth multiplication `χ_k · f_y` by
discrete coefficient multiplication `F_k` costs `O(c G Σ y_n²)` summed across all shells. -/
theorem exists_sum_levyEnergy_dyadicCommutator_le :
    ∃ C_comm : ℝ, C_comm = shellCommutatorConstant ∧ 0 ≤ C_comm ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → c ≤ N → ∀ (s : Finset ℕ) (y : ℕ → ℝ),
        ∑ k ∈ s, levyEnergy (fun u =>
          dyadicShellBump N k u * atomicTest N y (atomDilate tiltedUnitSpline (c / N)) u -
            atomicTest (dyadicShellHorizon N k)
              (fun n => dyadicShellBump N k (Real.log n) * y n)
              (atomDilate tiltedUnitSpline (c / N)) u) ≤
          C_comm * c * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
  obtain ⟨L_B, hLd, hLB0, hdB, hlipB⟩ := exists_baseShellBump_deriv_bound
  set M₀ := splineSupBound
  set M₁ := splineDerivSupBound
  have hM₀0 : 0 ≤ M₀ := splineSupBound_nonneg
  have hM₁0 : 0 ≤ M₁ := splineDerivSupBound_nonneg
  have hb0 : ∀ t, |tiltedUnitSpline t| ≤ M₀ := abs_tiltedUnitSpline_le
  have hb1 : ∀ t, |deriv tiltedUnitSpline t| ≤ M₁ := abs_deriv_tiltedUnitSpline_le
  set K₀ := L_B * (M₀ + M₁)
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hφ2 : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  set C_comm := 18 * 13 * K₀ ^ 2 * (Real.exp 1 + 1) / ∫ u, tiltedUnitSpline u ^ 2
  refine ⟨C_comm, (by dsimp only [C_comm, K₀, M₀, M₁]; rw [hLd]; rfl), by positivity, ?_⟩
  intro c N hc1 hcN s y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hdiff_φ : Differentiable ℝ tiltedUnitSpline :=
    contDiff_tiltedUnitSpline.differentiable (by norm_num)
  have hdiff_B : Differentiable ℝ (baseShellBump : ℝ → ℝ) :=
    (contDiff_baseShellBump (n := 2)).differentiable (by norm_num)
  -- Bound each shell commutator by its filtered H¹ norm
  have hshell : ∀ k ∈ s,
      levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
        18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2 := by
    intro k _
    rw [atomicTest_dyadicShellHorizon_eq hN1 y g]
    let S_k : Finset ℕ :=
      (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3)
    let h_atom : ℕ → ℝ → ℝ := fun n u =>
      (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) * g (u - Real.log n)
    have hR_eq : (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) =
        fun u => ∑ n ∈ S_k, y n * h_atom n u := by
      funext u
      unfold atomicTest
      rw [mul_sum, ← sum_sub_distrib]
      have hfull : ∑ x ∈ Icc 1 N, (dyadicShellBump N k u * (y x * g (u - Real.log x)) -
          dyadicShellBump N k (Real.log x) * y x * g (u - Real.log x)) =
          ∑ x ∈ Icc 1 N, y x * h_atom x u :=
        sum_congr rfl fun n _ => by simp only [h_atom]; ring
      rw [hfull]
      refine (sum_subset (filter_subset _ _) fun n hn hnot => ?_).symm
      have hgt3 : 3 < |Real.log (n : ℝ) - shellCenter N k| :=
        lt_of_not_ge fun hle => hnot (mem_filter.mpr ⟨hn, hle⟩)
      simp only [h_atom]
      by_cases huw : u - Real.log n ∈ Set.Icc 0 w
      · obtain ⟨hu0, huw'⟩ := Set.mem_Icc.mp huw
        have h1 : 2 ≤ |Real.log (n : ℝ) - shellCenter N k| := by linarith
        have h2 : 2 ≤ |u - shellCenter N k| := by
          have htri := abs_sub_abs_le_abs_sub (Real.log (n : ℝ) - shellCenter N k)
            (Real.log (n : ℝ) - u)
          have hdu : |Real.log (n : ℝ) - u| ≤ 1 := by
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
          have hid : (Real.log (n : ℝ) - shellCenter N k) - (Real.log (n : ℝ) - u) =
              u - shellCenter N k := by
            ring
          rw [hid] at htri
          linarith
        rw [dyadicShellBump_eq_zero h2, dyadicShellBump_eq_zero h1, sub_self, zero_mul, mul_zero]
      · have hg0 : g (u - Real.log n) = 0 := hsupp _ huw
        rw [hg0, mul_zero, mul_zero]
    have hRk_cd : ContDiff ℝ 2 (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((contDiff_dyadicShellBump N k).mul (contDiff_atomicTest hg N y)).sub
        (contDiff_atomicTest hg N _)
    have hRk_cs : HasCompactSupport (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((hasCompactSupport_atomicTest hsupp N y).mul_left).sub
        (hasCompactSupport_atomicTest hsupp N _)
    have hlev := levyEnergy_le_mul_integral_deriv_sq hRk_cd hRk_cs
    rw [hR_eq] at hlev hRk_cd hRk_cs ⊢
    -- Pointwise derivative bound for each atom `h_atom n`
    have hh_diff : ∀ n : ℕ, Differentiable ℝ (h_atom n) := fun n =>
      (((contDiff_dyadicShellBump N k).sub contDiff_const).mul
        (hg.comp (contDiff_id.sub contDiff_const))).differentiable (by norm_num)
    have hderiv_atom : ∀ (n : ℕ) (u : ℝ),
        |deriv (h_atom n) u| ≤
          K₀ * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro n u
      by_cases huI : u ∈ Set.Icc (Real.log n) (Real.log n + w)
      · rw [Set.indicator_of_mem huI, mul_one]
        obtain ⟨hu_lo, hu_hi⟩ := Set.mem_Icc.mp huI
        have hd1 : HasDerivAt (fun v => dyadicShellBump N k v - dyadicShellBump N k (Real.log n))
            (deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)) u := by
          have hsub1 : HasDerivAt (fun v : ℝ => v - shellCenter N k) 1 u :=
            (hasDerivAt_id u).sub_const (shellCenter N k)
          have hcomp1 := (hdiff_B.differentiableAt.hasDerivAt).comp u hsub1
          simpa only [Function.comp_def, id_eq, mul_one, dyadicShellBump] using
            hcomp1.sub_const (dyadicShellBump N k (Real.log n))
        have hd2 : HasDerivAt (fun v => g (v - Real.log n))
            (deriv tiltedUnitSpline ((u - Real.log n) / w) / w) u := by
          have hsub : HasDerivAt (fun v : ℝ => (v - Real.log n) / w) (1 / w) u :=
            ((hasDerivAt_id u).sub_const (Real.log n)).div_const w
          have hcomp := (hdiff_φ.differentiableAt.hasDerivAt).comp u hsub
          simpa only [Function.comp_def, id_eq, mul_one_div, g, atomDilate] using hcomp
        have hdmul := (hd1.mul hd2).deriv
        change deriv (h_atom n) u = _ at hdmul
        rw [hdmul]
        have hv1 : |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| ≤ L_B * w := by
          have hl := hlipB (u - shellCenter N k) (Real.log n - shellCenter N k)
          have hd : |(u - shellCenter N k) - (Real.log n - shellCenter N k)| ≤ w := by
            rw [show (u - shellCenter N k) - (Real.log n - shellCenter N k) = u - Real.log n by ring,
              abs_of_nonneg (by linarith)]
            linarith
          exact hl.trans (mul_le_mul_of_nonneg_left hd hLB0)
        have hv2 : |g (u - Real.log n)| ≤ M₀ := hb0 _
        have hd2_le : |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| ≤ M₁ / w := by
          rw [abs_div, abs_of_pos hw]
          exact div_le_div_of_nonneg_right (hb1 _) hw.le
        calc |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k) * g (u - Real.log n) +
              (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) *
                (deriv tiltedUnitSpline ((u - Real.log n) / w) / w)|
            ≤ |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k) * g (u - Real.log n)| +
                |(dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) *
                  (deriv tiltedUnitSpline ((u - Real.log n) / w) / w)| := abs_add_le _ _
          _ = |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)| * |g (u - Real.log n)| +
                |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| *
                  |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| := by rw [abs_mul, abs_mul]
          _ ≤ L_B * M₀ + (L_B * w) * (M₁ / w) :=
              add_le_add (mul_le_mul (hdB _) hv2 (abs_nonneg _) hLB0)
                (mul_le_mul hv1 hd2_le (abs_nonneg _) (mul_nonneg hLB0 hw.le))
          _ = K₀ := by simp only [K₀]; field_simp [hw.ne']
      · rw [Set.indicator_of_notMem huI, mul_zero]
        have hev : h_atom n =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
          refine Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds huI) fun v hv => ?_
          have hvw : v - Real.log n ∉ Set.Icc 0 w := fun hmem =>
            hv (Set.mem_Icc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
          simp only [h_atom, g]
          rw [hsupp _ hvw, mul_zero]
        rw [hev.deriv_eq, deriv_const, abs_zero]
    -- Overlap count of intervals `[log n, log n + w]` at any point `u`
    have hoverlap : ∀ u : ℝ,
        ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u ≤
          (Real.exp 1 + 1) * c := by
      intro u
      by_cases hu_hi : Real.log N + w < u
      · have hz : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u = 0 := by
          refine sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
          intro hmem
          have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).2
          have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
          have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
          linarith [hmem.2]
        rw [hz]; positivity
      · push Not at hu_hi
        have hsub : S_k.filter (fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)) ⊆
            S_k.filter (fun n : ℕ => Real.exp (u - w) ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u) := by
          intro n hn
          obtain ⟨hnS, hmem⟩ := mem_filter.mp hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hnS).1).1
          refine mem_filter.mpr ⟨hnS, ?_, ?_⟩
          · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr (by linarith [hmem.2])
          · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hmem.1
        have hsum_ind : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
            ((S_k.filter fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)).card : ℝ) := by
          have heq : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
              ∑ _n ∈ S_k.filter (fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)),
                (1 : ℝ) := by
            symm
            rw [sum_filter (s := S_k)]
            refine sum_congr rfl fun n _ => ?_
            by_cases hm : u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w) <;> simp [hm]
          rw [heq, sum_const, nsmul_eq_mul, mul_one]
        rw [hsum_ind]
        have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
          (card_filter_mem_Icc_real_le S_k (Real.exp_le_exp.mpr (by linarith)))
        have hexpu : Real.exp u ≤ Real.exp 1 * N := by
          calc Real.exp u ≤ Real.exp (Real.log N + w) := Real.exp_le_exp.mpr hu_hi
            _ = (N : ℝ) * Real.exp w := by rw [Real.exp_add, Real.exp_log hNR]
            _ ≤ (N : ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hNR.le
            _ = Real.exp 1 * N := by ring
        have hdiff_exp : Real.exp u - Real.exp (u - w) ≤ Real.exp 1 * c := by
          have h1 : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
          have h0 : 0 ≤ 1 - Real.exp (-w) := by
            have := Real.exp_le_one_iff.mpr (show -w ≤ 0 by linarith); linarith
          calc Real.exp u - Real.exp (u - w)
              = Real.exp u * (1 - Real.exp (-w)) := by
                rw [show u - w = u + (-w) by ring, Real.exp_add]; ring
            _ ≤ (Real.exp 1 * N) * w :=
                mul_le_mul hexpu h1 h0 (by positivity)
            _ = Real.exp 1 * c := by simp only [w]; field_simp [hNR.ne']
        linarith only [hcard, hdiff_exp, hc1]
    -- Pointwise Cauchy–Schwarz on `deriv R_k u ^ 2`
    have hpt_sq : ∀ u : ℝ,
        deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2 ≤
          K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
            ∑ n ∈ S_k, y n ^ 2 * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      have hdsum : deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u =
          ∑ n ∈ S_k, y n * deriv (h_atom n) u := by
        have h0 : HasDerivAt (∑ n ∈ S_k, fun v => y n * h_atom n v)
            (∑ n ∈ S_k, y n * deriv (h_atom n) u) u :=
          HasDerivAt.sum fun n (_ : n ∈ S_k) => ((hh_diff n u).hasDerivAt).const_mul (y n)
        have hfn : (∑ n ∈ S_k, fun v => y n * h_atom n v) =
            fun v => ∑ n ∈ S_k, y n * h_atom n v := by
          ext v; exact Finset.sum_apply v S_k _
        rw [hfn] at h0
        exact h0.deriv
      rw [hdsum]
      let ind : ℕ → ℝ := fun n =>
        (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u
      have hind_sq : ∀ n, ind n ^ 2 = ind n := fun n => by
        simp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have hind0 : ∀ n, 0 ≤ ind n := fun n => by
        simp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have habs : |∑ n ∈ S_k, y n * deriv (h_atom n) u| ≤
          K₀ * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
        calc |∑ n ∈ S_k, y n * deriv (h_atom n) u|
            ≤ ∑ n ∈ S_k, |y n * deriv (h_atom n) u| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ S_k, |y n| * (K₀ * ind n) :=
              sum_le_sum fun n _ => by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hderiv_atom n u) (abs_nonneg _)
          _ = K₀ * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
              rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
              rw [show ind n * (|y n| * ind n) = |y n| * ind n ^ 2 by ring, hind_sq n]; ring
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs, mul_pow] at hsq
      have hcs := sum_mul_sq_le_sq_mul_sq S_k ind (fun n => |y n| * ind n)
      calc (∑ n ∈ S_k, y n * deriv (h_atom n) u) ^ 2
          ≤ K₀ ^ 2 * ((∑ n ∈ S_k, ind n ^ 2) * ∑ n ∈ S_k, (|y n| * ind n) ^ 2) :=
            hsq.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg K₀))
        _ = K₀ ^ 2 * (∑ n ∈ S_k, ind n) * ∑ n ∈ S_k, y n ^ 2 * ind n := by
            simp_rw [mul_pow, sq_abs, hind_sq]; ring
        _ ≤ K₀ ^ 2 * ((Real.exp 1 + 1) * c) * ∑ n ∈ S_k, y n ^ 2 * ind n :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hoverlap u) (sq_nonneg K₀))
              (sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hind0 n))
    have hint_lhs : Integrable (fun u => deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) :=
      integrable_sq_of_continuous (hRk_cd.continuous_deriv (by norm_num)) hRk_cs.deriv
    have hint_ind : ∀ n : ℕ,
        Integrable (fun u => y n ^ 2 *
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) := fun n =>
      ((integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc).const_mul (y n ^ 2)
    have himono : (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) ≤
        K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2) := by
      have h1 := integral_mono hint_lhs
        ((integrable_finsetSum S_k fun n _ => hint_ind n).const_mul
          (K₀ ^ 2 * ((Real.exp 1 + 1) * c))) hpt_sq
      have hind_int : ∀ n : ℕ,
          (∫ u, y n ^ 2 * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) =
            w * y n ^ 2 := fun n => by
        rw [integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const,
          smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
        ring
      calc (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2)
          ≤ ∫ u, K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
              ∑ n ∈ S_k, y n ^ 2 *
                (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := h1
        _ = K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
              ∑ n ∈ S_k, ∫ u, y n ^ 2 *
                (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
            rw [integral_const_mul, integral_finsetSum S_k fun n _ => hint_ind n]
        _ = K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2) := by
            simp_rw [hind_int, ← mul_sum]
    calc levyEnergy (fun v => ∑ n ∈ S_k, y n * h_atom n v)
        ≤ 18 * ∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2 := hlev
      _ ≤ 18 * (K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2)) :=
          mul_le_mul_of_nonneg_left himono (by norm_num)
      _ = 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * ∑ n ∈ S_k, y n ^ 2 := by ring
  -- Sum over `k ∈ s` and swap sums
  have hswap : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
        y n ^ 2 ≤ 13 * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    have heq : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
          y n ^ 2 =
        ∑ n ∈ Icc 1 N, ((s.filter fun k => |Real.log (n : ℝ) - shellCenter N k| ≤ 3).card : ℝ) *
          y n ^ 2 := by
      simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    rw [heq, mul_sum]
    refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact (card_shellCenter_near_le s N (Real.log n) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
      (by norm_num)
  calc ∑ k ∈ s, levyEnergy _
      ≤ ∑ k ∈ s, 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 :=
        sum_le_sum hshell
    _ = 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2 := by
        rw [← mul_sum]
    _ ≤ 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * (13 * ∑ n ∈ Icc 1 N, y n ^ 2) :=
        mul_le_mul_of_nonneg_left hswap (by positivity)
    _ = C_comm * c * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
        simp only [C_comm, w]
        field_simp [hφ2.ne']

private theorem two_pow_le_linearDefectCutoff {c : ℝ} (hc1 : 1 ≤ c) {k : ℕ}
    (hk : k ∈ range (dyadicShellCount c)) :
    (2 : ℝ) ^ k ≤ linearDefectCutoff c := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
  have hk_le : (k : ℝ) ≤ Real.log (linearDefectCutoff c) / Real.log 2 := by
    have hk_nat : k ≤ ⌊Real.log (linearDefectCutoff c) / Real.log 2⌋₊ :=
      Nat.lt_succ_iff.mp (mem_range.mp hk)
    exact (Nat.cast_le.mpr hk_nat).trans (Nat.floor_le
      (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos one_lt_two).le))
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : (k : ℝ) * Real.log 2 ≤ Real.log (linearDefectCutoff c) := (le_div_iff₀ hl2).mp hk_le
  calc (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ ≤ Real.exp (Real.log (linearDefectCutoff c)) := Real.exp_le_exp.mpr hmul
    _ = linearDefectCutoff c := Real.exp_log (by linarith)

private theorem dyadicShell_levyEnergy_ge {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c)
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) (y : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ range (dyadicShellCount c)) :
    (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        (Real.log N / 2) -
      (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (1 + 8 * Real.exp 1) * c) * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
      (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) ≤
    levyEnergy (atomicTest (dyadicShellHorizon N k)
      (fun n => dyadicShellBump N k (Real.log n) * y n)
      (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  have hcN : c ≤ (N : ℝ) := by nlinarith [h4c]
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN_pos
  have hG : 0 < (c / (N : ℝ)) * ∫ u, tiltedUnitSpline u ^ 2 :=
    mul_pos hw integral_tiltedUnitSpline_sq_pos
  have h2k : (2 : ℝ) ^ k ≤ Lc := two_pow_le_linearDefectCutoff hc1 hk
  let Nk := dyadicShellHorizon N k
  have hsqrt_le : Real.sqrt N ≤ Nk := by
    have hsq : Real.sqrt N * Lc ≤ N := by
      have h1 : (Lc : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Lc)]
        exact Real.sqrt_le_sqrt hL2N
      calc Real.sqrt N * Lc ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = N := Real.mul_self_sqrt hN_pos.le
    have h4N : Real.sqrt N + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
      have hdiv : Real.sqrt N ≤ (N : ℝ) / (2 : ℝ) ^ k := by
        rw [le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left h2k (Real.sqrt_nonneg _)).trans hsq
      have hsq3 : 3 ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt N + 1 ≤ 4 * Real.sqrt N := by linarith only [hsq3]
        _ ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
    have hfl : Real.sqrt N ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
      have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
      linarith
    have hN_sq : Real.sqrt N ≤ N := by
      have hsq1 : 1 ≤ Real.sqrt N := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt N = Real.sqrt N * 1 := (mul_one _).symm
        _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
        _ = N := Real.mul_self_sqrt hN_pos.le
    simp only [Nk, dyadicShellHorizon]
    rw [Nat.cast_min, le_min_iff]
    exact ⟨hN_sq, hfl⟩
  have hNk_lb : (N : ℝ) / (2 : ℝ) ^ k ≤ Nk := by
    have hdiv3 : 3 ≤ (N : ℝ) / (2 : ℝ) ^ k := by
      rw [le_div_iff₀ (by positivity)]
      have : 3 * (2 : ℝ) ^ k ≤ (Lc : ℝ) * Lc :=
        mul_le_mul hLc_R h2k (by positivity) (by linarith)
      nlinarith [hL2N]
    have hfl : (N : ℝ) / (2 : ℝ) ^ k ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
      have h4 : (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
        calc (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := by linarith only [hdiv3]
          _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
      have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
      linarith
    have hN_div : (N : ℝ) / (2 : ℝ) ^ k ≤ N :=
      div_le_self hN_pos.le (one_le_pow₀ one_le_two)
    simp only [Nk, dyadicShellHorizon]
    rw [Nat.cast_min, le_min_iff]
    exact ⟨hN_div, hfl⟩
  have hNk_ub : (Nk : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k :=
    (Nat.cast_le.mpr (min_le_right N _)).trans (Nat.floor_le (by positivity))
  let ck := c * (Nk : ℝ) / N
  have hNk_pos : (0 : ℝ) < Nk := lt_of_lt_of_le (Real.sqrt_pos.mpr hN_pos) hsqrt_le
  have hck_min : 1 / 2052 ≤ ck := by
    have he2 : Real.exp 2 < 8 := by
      have he1 : Real.exp 1 < 11 / 4 := by have := Real.exp_one_lt_d9; linarith
      have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he2']; nlinarith [Real.exp_pos 1]
    have hLc_ub : (Lc : ℝ) ≤ 2052 * c := by nlinarith [hLup, hc0]
    have h1 : c / (2 : ℝ) ^ k ≤ ck := by
      simp only [ck]
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      have := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mp hNk_lb) hc0.le
      linarith
    have h2 : 1 / 2052 ≤ c / (2 : ℝ) ^ k := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity), one_mul]
      linarith only [h2k, hLc_ub]
    exact h2.trans h1
  have hck_4c : ck ≤ 4 * c := by
    simp only [ck]
    rw [div_le_iff₀ hN_pos]
    have : (Nk : ℝ) ≤ 4 * N := hNk_ub.trans
      (div_le_self (by positivity) (one_le_pow₀ one_le_two))
    nlinarith
  have hck_Nk : ck ≤ Nk := by
    simp only [ck]
    rw [div_le_iff₀ hN_pos]
    nlinarith [hcN, hNk_pos]
  have hck_div : ck / Nk = c / N := by
    simp only [ck]
    field_simp [hN_pos.ne', hNk_pos.ne']
  have hlogNk : Real.log N / 2 ≤ Real.log Nk := by
    have h1 := Real.log_le_log (Real.sqrt_pos.mpr hN_pos) hsqrt_le
    rwa [Real.log_sqrt hN_pos.le] at h1
  have hsum_eq : ∑ n ∈ Icc 1 Nk, (dyadicShellBump N k (Real.log n) * y n) ^ 2 =
      ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 := by
    have hsub := sum_subset (Icc_subset_Icc (le_rfl : 1 ≤ 1) (min_le_left N _))
      (f := fun n : ℕ => dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) fun n hn hnot => by
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hgt : Nk < n := by
          by_contra hle; exact hnot (mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
        rw [dyadicShellBump_log_eq_zero_of_gt_horizon hN1 hnN hgt, sq, zero_mul, zero_mul]
    rw [← hsub]
    exact sum_congr rfl fun n _ => mul_pow _ _ 2
  have hlev0 := levyEnergy_atomicTest_ge_of_ge hck_min hck_Nk
    (fun n => dyadicShellBump N k (Real.log n) * y n)
  rw [hck_div, hsum_eq] at hlev0
  refine le_trans ?_ hlev0
  have hZ : 0 ≤ ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hG.le) hZ
  have hpos_gain : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * (Real.log N / 2) ≤
      ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * Real.log Nk :=
    mul_le_mul_of_nonneg_left hlogNk
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2052 : ℝ) ^ 8)
        growingMassConstant_pos.le)
        (pow_nonneg (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2052) hck_min).le 7))
  have hneg_cost : (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
      (1 + 2 * Real.exp 1 * ck) ≤
      (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (1 + 8 * Real.exp 1) * c := by
    have h1 : 2 * Real.exp 1 * ck ≤ 8 * Real.exp 1 * c :=
      (mul_le_mul_of_nonneg_left hck_4c
        (mul_nonneg zero_le_two (Real.exp_pos 1).le)).trans_eq (by ring)
    have h2 : 1 + 2 * Real.exp 1 * ck ≤ (1 + 8 * Real.exp 1) * c := by
      linarith only [hc1, h1]
    exact (mul_le_mul_of_nonneg_left h2
      (add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two))
        (mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0))))).trans_eq
      (mul_assoc _ _ _).symm
  linarith only [hpos_gain, hneg_cost]

private theorem inv_eighth_c_pow_seven_eq {B c n N : ℝ} (hN : N ≠ 0) (hn : n ≠ 0) (hc : c ≠ 0) :
    (N / n) ^ 7 / (B ^ 7 * c ^ 7) = 1 / (B * c * n / N) ^ 7 := by
  field_simp [hN, hn, hc]

private theorem dyadicShell_seventh_coverage_ge {c : ℝ} {N : ℕ} (hc1 : 1 ≤ c)
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) {n : ℕ}
    (hn : n ∈ Ioc (N / linearDefectCutoff c) N) :
    (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) ≤
      ∑ k ∈ range (dyadicShellCount c), (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2 := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  let M := N / Lc
  have hL_pos : 0 < Lc := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrat1 : 1 ≤ (N : ℝ) / n := (one_le_div hn0).mpr (by exact_mod_cast hnN)
  have hrat_lt : (N : ℝ) / n < Lc := by
    rw [div_lt_iff₀ hn0]
    have h1 : N < Lc * (M + 1) := Nat.lt_mul_div_succ N hL_pos
    have h2 : Lc * (M + 1) ≤ Lc * n := Nat.mul_le_mul_left Lc hMn
    have h3 : (N : ℝ) < (Lc : ℝ) * n := by exact_mod_cast h1.trans_le h2
    linarith only [h3, (by ring : (Lc : ℝ) * n = (Lc : ℝ) * (n : ℝ))]
  let t := Real.log ((N : ℝ) / n) / Real.log 2
  have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg hrat1) hl2.le
  let k₀ := ⌊t⌋₊
  have hk₀_mem : k₀ ∈ range (dyadicShellCount c) := by
    refine mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono ?_))
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one hrat1) hrat_lt.le) hl2.le
  have hk₀_lo : (k₀ : ℝ) * Real.log 2 ≤ Real.log N - Real.log n := by
    rw [← Real.log_div hN_pos.ne' hn0.ne']
    exact (le_div_iff₀ hl2).mp (Nat.floor_le ht0)
  have hk₀_hi : Real.log N - Real.log n < ((k₀ : ℝ) + 1) * Real.log 2 := by
    rw [← Real.log_div hN_pos.ne' hn0.ne']
    exact (div_lt_iff₀ hl2).mp (Nat.lt_floor_add_one t)
  have hbump1 : dyadicShellBump N k₀ (Real.log n) = 1 := by
    apply dyadicShellBump_eq_one
    have hid : Real.log n - shellCenter N k₀ =
        ((k₀ : ℝ) + 1) * Real.log 2 - (Real.log N - Real.log n) := by
      unfold shellCenter; ring
    rw [hid, abs_of_nonneg (by linarith)]
    have hl2_le1 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hck₀_ub : c * (dyadicShellHorizon N k₀ : ℝ) / N ≤ 8 * c * n / N := by
    have h2k₀_gt : (N : ℝ) / n < 2 * (2 : ℝ) ^ k₀ := by
      have hexp := Real.exp_lt_exp.mpr hk₀_hi
      rw [Real.exp_sub, Real.exp_log hN_pos, Real.exp_log hn0, add_mul, one_mul,
        Real.exp_add, Real.exp_log zero_lt_two,
        show (k₀ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k₀) by rw [Real.log_pow],
        Real.exp_log (by positivity)] at hexp
      linarith
    have hNk₀ : (dyadicShellHorizon N k₀ : ℝ) ≤ 8 * n := by
      have h1 : (dyadicShellHorizon N k₀ : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ :=
        (Nat.cast_le.mpr (min_le_right N _)).trans (Nat.floor_le (by positivity))
      have h2 : 4 * (N : ℝ) / (2 : ℝ) ^ k₀ ≤ 8 * n := by
        rw [div_le_iff₀ (by positivity)]
        have := (div_lt_iff₀ hn0).mp h2k₀_gt
        linarith
      exact h1.trans h2
    calc c * (dyadicShellHorizon N k₀ : ℝ) / N
        ≤ c * (8 * n) / N := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNk₀ hc0.le) hN_pos.le
      _ = 8 * c * n / N := by ring
  have hNk₀_pos : (0 : ℝ) < dyadicShellHorizon N k₀ := by
    have hdiv1 : (1 : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ := by
      rw [one_le_div (by positivity)]
      have hLc_4N : (Lc : ℝ) ≤ 4 * N := by nlinarith only [hLc_R, hL2N]
      exact (two_pow_le_linearDefectCutoff hc1 hk₀_mem).trans hLc_4N
    have hpos : 1 ≤ dyadicShellHorizon N k₀ := le_min hN1 ((Nat.one_le_floor_iff _).mpr hdiv1)
    exact_mod_cast hpos
  have hsingle : (1 / (c * (dyadicShellHorizon N k₀ : ℝ) / N) ^ 7) *
        dyadicShellBump N k₀ (Real.log n) ^ 2 ≤
      ∑ k ∈ range (dyadicShellCount c), (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2 :=
    single_le_sum (f := fun k => (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
        dyadicShellBump N k (Real.log n) ^ 2)
      (fun k _ => mul_nonneg (one_div_nonneg.mpr (pow_nonneg (by positivity) 7)) (sq_nonneg _))
      hk₀_mem
  refine le_trans ?_ hsingle
  rw [hbump1, one_pow, mul_one, inv_eighth_c_pow_seven_eq hN_pos.ne' hn0.ne' hc0.ne']
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hck₀_ub 7)

private theorem shell_term_div_eq (A0 B7 c7 L q x2 : ℝ) :
    (A0 / (2 * B7 * c7)) * L * (q * x2) = A0 * (L / 2) * ((q / (B7 * c7)) * x2) := by
  rw [show 2 * B7 * c7 = (B7 * c7) * 2 by ring, ← div_div,
    div_eq_mul_one_div A0 (B7 * c7), div_eq_mul_one_div q (B7 * c7)]
  ring

private theorem top_arch_levy_combine {A0 B7 c G S S7 L K_low C_comm L_B e1 : ℝ} :
    (1 / 2 : ℝ) * (G * ((A0 / (2 * B7 * c ^ 7)) * L * S7 - 9 * K_low * c * S)) -
        C_comm * c * G * S -
        648 * L_B ^ 2 * (G * ((1 + 2 * e1) * c) * S) =
      18 * (G * ((A0 / (72 * B7 * c ^ 7)) * L * S7)) -
        (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * e1)) * c * G * S := by
  rw [show 72 * B7 * c ^ 7 = (2 * B7 * c ^ 7) * 36 by ring, ← div_div]
  ring

private theorem top_arch_levy_rhs (A B1 c G S7 : ℝ) :
    18 * (G * (A * S7 - (B1 / 18) * c * S7)) =
      18 * (G * (A * S7)) - B1 * c * G * S7 := by
  ring

private theorem dyadicTopMassConstant_div_eq (c : ℝ) :
    dyadicTopMassConstant / c ^ 7 =
      (1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7) := by
  unfold dyadicTopMassConstant
  rw [div_div]

/-- **Dyadic seventh-power archimedean reserve on the top collar.** Summing the shell reserves via
smooth IMS and subtracting the `H¹` commutator upgrades the top `archForm` floor to
`topCollarSeventhMass` at only linear `O(c)` mass cost. -/
theorem exists_top_archForm_dyadic_seventh_reserve :
    ∃ C_arch : ℝ, C_arch = dyadicArchConstant ∧ 0 ≤ C_arch ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N → ∀ x : ℕ → ℝ,
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
          ((dyadicTopMassConstant / c ^ 7) * Real.log N *
              topCollarSeventhMass (N / linearDefectCutoff c) N x -
            C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
          archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨L_B, hLd, hLB0, -, hlipB⟩ := exists_baseShellBump_deriv_bound
  obtain ⟨C_comm, hCd, hCcomm0, hcomm⟩ := exists_sum_levyEnergy_dyadicCommutator_le
  set K_low := (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
    (1 + 8 * Real.exp 1) with hKlow_def
  have hKlow0 : 0 ≤ K_low :=
    mul_nonneg (add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg
      (Real.log_nonneg one_le_two)) (by positivity)) (by positivity)
  set C_arch := (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18 +
    2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1)
  refine ⟨C_arch, (by dsimp only [C_arch, K_low]; rw [hLd, hCd]; rfl), add_nonneg (div_nonneg (add_nonneg (add_nonneg (div_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hKlow0) zero_le_two) hCcomm0)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 648) (sq_nonneg L_B))
      (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le))))
    (by norm_num : (0 : ℝ) ≤ 18))
    (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _))
      (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le))), ?_⟩
  intro c N hc1 hL2N x
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  let M := N / Lc
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN_pos : (0 : ℝ) < N := by linarith
  have hcN : c ≤ (N : ℝ) := by nlinarith [h4c]
  have hMN : M ≤ N := Nat.div_le_self N Lc
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  let g := atomDilate tiltedUnitSpline w
  let G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  let y := atomicTailCoefficients M x
  have hy_eq : ∑ n ∈ Icc 1 N, y n ^ 2 = ∑ n ∈ Ioc M N, x n ^ 2 :=
    sum_atomicTailCoefficients_sq_eq_Ioc' hMN x
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  let s := range (dyadicShellCount c)
  -- Sum the shell Lévy energies
  have hsum_F : G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x -
        9 * K_low * c * ∑ n ∈ Ioc M N, x n ^ 2) ≤
      ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) := by
    have hshell : ∀ k ∈ s,
        (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            (Real.log N / 2) - K_low * c) * G *
          (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) ≤
        levyEnergy (atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g) := by
      intro k hk
      rw [hKlow_def]
      exact dyadicShell_levyEnergy_ge hc1 hL2N y hk
    refine le_trans ?_ (sum_le_sum hshell)
    have hswap : ∑ k ∈ s,
          (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            (Real.log N / 2) - K_low * c) * G *
          (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) =
        G * ((1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
          (∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2) -
          K_low * c * ∑ n ∈ Ioc M N,
            (∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2) := by
      have hrestrict : ∀ k : ℕ,
          ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 =
            ∑ n ∈ Ioc M N, dyadicShellBump N k (Real.log n) ^ 2 * x n ^ 2 := fun k => by
        have hIoc : (Ioc M N : Finset ℕ) ⊆ Icc 1 N := fun n hn =>
          mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hn).1),
            (mem_Ioc.mp hn).2⟩
        rw [← sum_subset hIoc fun n hn hnot => by
          have hle : n ≤ M := by
            by_contra hgt; exact hnot (mem_Ioc.mpr ⟨not_le.mp hgt, (mem_Icc.mp hn).2⟩)
          have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr hle)
          rw [hy0]; ring]
        exact sum_congr rfl fun n hn => by
          have hyx : y n = x n := if_pos (mem_Ioc.mp hn).1
          rw [hyx]
      simp_rw [hrestrict, sub_mul, mul_sum]
      rw [sum_sub_distrib, mul_sub]
      congr 1
      · rw [sum_comm, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_mul, mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
      · rw [sum_comm, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_mul, mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
    rw [hswap]
    refine mul_le_mul_of_nonneg_left (sub_le_sub ?_ ?_) hG.le
    · have h1 : ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 ≤
          ∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2 :=
        sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_right (dyadicShell_seventh_coverage_ge hc1 hL2N hn) (sq_nonneg _)
      have hlog0 : 0 ≤ (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2052 : ℝ) ^ 8)
          growingMassConstant_pos.le)
          (div_nonneg (Real.log_natCast_nonneg N) zero_le_two)
      calc ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
            Real.log N * topCollarSeventhMass M N x
          = (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
              ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 := by
            unfold topCollarSeventhMass
            rw [mul_sum, mul_sum]
            refine sum_congr rfl fun n _ => ?_
            exact shell_term_div_eq ((1 / 2052 : ℝ) ^ 8 * growingMassConstant) (8 ^ 7) (c ^ 7)
              (Real.log N) (((N : ℝ) / n) ^ 7) (x n ^ 2)
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hlog0
    · have hsum9 : ∑ n ∈ Ioc M N, (∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2 ≤
          9 * ∑ n ∈ Ioc M N, x n ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        calc ∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2
            ≤ ∑ k ∈ s, (if |Real.log n - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) :=
              sum_le_sum fun k _ => by
                split_ifs with hle
                · nlinarith [dyadicShellBump_nonneg N k (Real.log n),
                    dyadicShellBump_le_one N k (Real.log n)]
                · rw [dyadicShellBump_eq_zero (le_of_not_ge hle), sq, zero_mul]
          _ ≤ 9 := by
              rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
              exact (card_shellCenter_near_le s N (Real.log n) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
                (by norm_num)
      exact (mul_le_mul_of_nonneg_left hsum9 (mul_nonneg hKlow0 hc0.le)).trans_eq (by ring)
  -- Relate `∑ levyEnergy F_k` to `levyEnergy f_y` via triangle + IMS + commutator
  have htri_sum : (1 / 2 : ℝ) * ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) -
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun k _ => ?_
    let a_k : ℝ → ℝ := fun u => dyadicShellBump N k u * atomicTest N y g u
    let F_k : ℝ → ℝ := atomicTest (dyadicShellHorizon N k)
      (fun n => dyadicShellBump N k (Real.log n) * y n) g
    have hak : ContDiff ℝ 2 a_k := (contDiff_dyadicShellBump N k).mul hfy
    have hakc : HasCompactSupport a_k := hfyc.mul_left
    have hFk : ContDiff ℝ 2 F_k := contDiff_atomicTest hg _ _
    have hFkc : HasCompactSupport F_k := hasCompactSupport_atomicTest hsupp _ _
    have heq : F_k = fun u => a_k u - (a_k u - F_k u) := funext fun _ => by ring
    have hsub := levyEnergy_sub_le_two_mul hak hakc (hak.sub hFk) (hakc.sub hFkc)
    rw [← heq] at hsub
    linarith only [hsub]
  have hims := sum_levyEnergy_dyadicShellBump_mul_le hlipB s N hfy hfyc
  have hcomm_s := hcomm hc1 hcN s y
  clear hcomm hL2N hLc_R hNR hMN
  rw [hy_eq] at hcomm_s
  have hfy2 : ∫ u, atomicTest N y g u ^ 2 ≤
      G * ((1 + 2 * Real.exp 1) * c) * ∑ n ∈ Ioc M N, x n ^ 2 := by
    have h0 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [integral_atomDilate_sq hw, hy_eq] at h0
    refine h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hG.le)
      (sum_nonneg fun _ _ => sq_nonneg _))
    nlinarith only [hc1, Real.exp_pos 1]
  have harch_eq := archForm_eq_levyEnergy hfy hfyc
  clear hy_eq hg hgc hsupp hfy hfyc
  have hγ_fy : -2 * |gammaHardyPhaseRate 0| * ∫ u, atomicTest N y g u ^ 2 ≤
      2 * gammaHardyPhaseRate 0 * ∫ u, atomicTest N y g u ^ 2 := by
    have hf0 : 0 ≤ ∫ u, atomicTest N y g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have habs_rate : -2 * |gammaHardyPhaseRate 0| ≤ 2 * gammaHardyPhaseRate 0 := by
      have := neg_abs_le (gammaHardyPhaseRate 0); linarith only [this]
    exact mul_le_mul_of_nonneg_right habs_rate hf0
  have hS_le_S7 := sum_sq_Ioc_le_topCollarSeventhMass M N x
  -- Combine all pieces into `archForm (atomicTest N y g)`
  have hlev_fy : G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x -
        ((9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18) *
          c * topCollarSeventhMass M N x) ≤
      levyEnergy (atomicTest N y g) := by
    have h18 : 18 * levyEnergy (atomicTest N y g) ≥
        (1 / 2 : ℝ) * ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g) -
        ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
          atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u) -
        648 * L_B ^ 2 * ∫ u, atomicTest N y g u ^ 2 := by
      linarith only [htri_sum, hims]
    have h648 := mul_le_mul_of_nonneg_left hfy2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 648) (sq_nonneg L_B))
    have hhalf := mul_le_mul_of_nonneg_left hsum_F (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hcost_S : (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) * c * G *
        (∑ n ∈ Ioc M N, x n ^ 2) ≤
        (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) * c * G *
          topCollarSeventhMass M N x :=
      mul_le_mul_of_nonneg_left hS_le_S7
        (mul_nonneg (mul_nonneg (add_nonneg (add_nonneg
          (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hKlow0) zero_le_two) hCcomm0)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 648) (sq_nonneg L_B))
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le)))) hc0.le) hG.le)
    have hid_combine := top_arch_levy_combine (A0 := (1 / 2052 : ℝ) ^ 8 * growingMassConstant)
      (B7 := 8 ^ 7) (c := c) (G := G) (S := ∑ n ∈ Ioc M N, x n ^ 2)
      (S7 := topCollarSeventhMass M N x) (L := Real.log N) (K_low := K_low)
      (C_comm := C_comm) (L_B := L_B) (e1 := Real.exp 1)
    have hid_rhs := top_arch_levy_rhs
      (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) * Real.log N)
      (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1))
      c G (topCollarSeventhMass M N x)
    linarith only [h18, hhalf, hcomm_s, h648, hcost_S, hid_combine, hid_rhs]
  have hγ_S7 : 2 * |gammaHardyPhaseRate 0| * ∫ u, atomicTest N y g u ^ 2 ≤
      G * (2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1) * c * topCollarSeventhMass M N x) := by
    have hγ0 : 0 ≤ 2 * |gammaHardyPhaseRate 0| :=
      mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0))
    have h1 := mul_le_mul_of_nonneg_left hfy2 hγ0
    have h2 := mul_le_mul_of_nonneg_left hS_le_S7
      (mul_nonneg hγ0 (mul_nonneg hG.le
        (mul_nonneg (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le)) hc0.le)))
    have hid1 := (fun (a G' b S : ℝ) => (by ring : a * (G' * b * S) = a * (G' * b) * S))
      (2 * |gammaHardyPhaseRate 0|) G ((1 + 2 * Real.exp 1) * c) (∑ n ∈ Ioc M N, x n ^ 2)
    have hid2 := (fun (a G' e1 S7 : ℝ) =>
        (by ring : a * (G' * ((1 + 2 * e1) * c)) * S7 = G' * (a * (1 + 2 * e1) * c * S7)))
      (2 * |gammaHardyPhaseRate 0|) G (Real.exp 1) (topCollarSeventhMass M N x)
    linarith only [h1, h2, hid1, hid2]
  rw [dyadicTopMassConstant_div_eq c, harch_eq]
  have hid_arch := (fun (G' A S7 B1 B2 : ℝ) =>
      (by ring : G' * (A * S7 - (B1 + B2) * c * S7) =
        G' * (A * S7 - B1 * c * S7) - G' * (B2 * c * S7)))
    G (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) * Real.log N)
    (topCollarSeventhMass M N x)
    ((9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18)
    (2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1))
  rw [hid_arch]
  have hid_neg := (fun (a I : ℝ) => (by ring : -2 * a * I = -(2 * a * I)))
    |gammaHardyPhaseRate 0| (∫ u, atomicTest N y g u ^ 2)
  linarith only [hγ_fy, hγ_S7, hlev_fy, hid_neg]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell
