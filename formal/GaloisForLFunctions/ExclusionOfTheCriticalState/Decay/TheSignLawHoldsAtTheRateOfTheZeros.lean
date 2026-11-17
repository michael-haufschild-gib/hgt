import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LandauTailSignObstruction
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLeftContinuationHasSquareIntegrableVerticalTraces
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.StateProductMultiplicity
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheContinuationIsPolynomiallyBoundedOffTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateDecaysExactlyAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheCriticalStateSeesALeftZero
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# The sign law at the rate of the zeros

**Landau against an exponential** (`integrable_exp_of_tail_le_exp`). If `s f ≤ e^{au}` almost
everywhere on a ray `u < -T` (`a > 0`, `s = ±1`) and the transform of `f` continues analytically
along the real axis right of `-a`, then `e^{au} - s f` is one-signed on the ray, its transform is
`1/(w + a) - s Lf(w)`, and the comparison term adds only the real pole `-a`. Hence
`∫ |f| e^{σu} < ∞` for every `σ > -a`.

* **The state** (`criticalState_not_tail_le_exp`). For a zero `ρ` with `Re ρ > ½` and
  `c > 17/2 - Re ρ` (that is `c > 8 - x`, `x = Re ρ - ½`), neither `F ≤ e^{cu}` nor `F ≥ -e^{cu}` holds
  almost everywhere on any ray: a one-sided bound makes `LF` holomorphic on `Re w > -c`, past its pole
  at `ρ - 17/2`. In terms of `Θ` (`criticalState_omega_pm`): both signs exceed `e^{cu}` on every
  ray for every `c > 17/2 - Θ`, while `∫ F² e^{-bu} < ∞` for every `b < 17 - 2Θ`.
* **The prime side** (`criticalState_beyondWall_not_tail_le_exp`). For a seen zero `ρ`
  (`LF(ρ - ½) ≠ 0`, `Re ρ > 0`) and `c < ½ - Re ρ`, neither `Re F⁺ ≤ e^{cx}` nor `Re F⁺ ≥ -e^{cx}` holds
  almost everywhere on any ray `x > T`: a one-sided bound continues the reflected transform of `F⁺`
  across `ρ - 17/2`, and the entire product `ξ(w + 17/2)·LF` would keep the full multiplicity of
  `ρ`. A seen left zero exists, so `F⁺` grows exponentially in both signs
  (`criticalState_beyondWall_omega_pm`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Landau's obstruction against an exponential comparison -/

/-- The comparison exponential `e^{au}` on the negative half-line. -/
def negExp (a u : ℝ) : ℝ := (Iio 0).indicator (fun v => Real.exp (a * v)) u

theorem measurable_negExp (a : ℝ) : Measurable (negExp a) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Iio

theorem negExp_of_nonneg (a : ℝ) {u : ℝ} (hu : 0 ≤ u) : negExp a u = 0 :=
  indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt.mpr hu) _

theorem negExp_of_neg (a : ℝ) {u : ℝ} (hu : u < 0) : negExp a u = Real.exp (a * u) :=
  indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu) _

theorem negExp_nonneg (a u : ℝ) : 0 ≤ negExp a u :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u

theorem negExp_mul_exp (a σ u : ℝ) :
    negExp a u * Real.exp (σ * u) = (Iio 0).indicator (fun v => Real.exp ((a + σ) * v)) u := by
  by_cases hu : u < 0
  · rw [negExp_of_neg a hu, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), ← Real.exp_add]
    congr 1
    ring
  · rw [negExp_of_nonneg a (not_lt.mp hu), zero_mul,
      indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]

theorem integrable_negExp_mul_exp {a σ : ℝ} (h : 0 < a + σ) :
    Integrable fun u => negExp a u * Real.exp (σ * u) := by
  simp_rw [negExp_mul_exp]
  exact ((integrableOn_exp_mul_Iic h 0).mono_set Iio_subset_Iic_self).integrable_indicator
    measurableSet_Iio

theorem integrable_negExp {a : ℝ} (ha : 0 < a) : Integrable (negExp a) := by
  simpa using integrable_negExp_mul_exp (a := a) (σ := 0) (by linarith)

/-- `∫_{u<0} e^{au} e^{xu} du = 1/(x + a)`. -/
theorem laplace_negExp {a x : ℝ} (h : 0 < x + a) :
    negativeHalfLineLaplace (cx (negExp a)) (x : ℂ) = ((1 / (x + a) : ℝ) : ℂ) := by
  rw [negativeHalfLineLaplace_ofReal]
  congr 1
  simp_rw [negExp_mul_exp]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic (a := a + x) (by linarith) 0, mul_zero, Real.exp_zero]
  ring

/-- **Landau against an exponential.** If `s f ≤ e^{au}` almost everywhere on a ray and the transform
of `f` continues analytically along the real axis right of `-a`, then `∫ |f| e^{σu} < ∞` for every
`σ > -a`. -/
theorem integrable_exp_of_tail_le_exp {f : ℝ → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {G : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hG : ∀ x : ℝ, -a < x → AnalyticAt ℂ G (x : ℂ))
    (heq : ∀ x : ℝ, 0 < x → negativeHalfLineLaplace (cx f) (x : ℂ) = G x)
    {s T : ℝ} (hsign : s = 1 ∨ s = -1) (hT : 0 ≤ T)
    (hle : ∀ᵐ u ∂volume.restrict (Iio (-T)), s * f u ≤ Real.exp (a * u))
    {σ : ℝ} (hσ : -a < σ) : Integrable fun u => |f u| * Real.exp (σ * u) := by
  have habs : |s| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  -- the one-signed comparison profile `g = e^{au} - s f` and its continuation
  let g : ℝ → ℝ := fun u => negExp a u - s * f u
  have hgm : Measurable g := (measurable_negExp a).sub (measurable_const.mul hm)
  have hgi : Integrable g := (integrable_negExp ha).sub (hf.const_mul s)
  have hgs : ∀ u, 0 ≤ u → g u = 0 := fun u hu => by
    simp only [g, negExp_of_nonneg a hu, hs u hu, mul_zero, sub_zero]
  have hGg : ∀ x : ℝ, -a < x →
      AnalyticAt ℂ (fun w => 1 / (w + a) - (s : ℂ) * G w) (x : ℂ) := by
    intro x hx
    have hne : (x : ℂ) + a ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    exact (analyticAt_const.div (analyticAt_id.add analyticAt_const) hne).sub
      (analyticAt_const.mul (hG x hx))
  have heqg : ∀ x : ℝ, 0 < x →
      negativeHalfLineLaplace (cx g) (x : ℂ) = 1 / ((x : ℂ) + a) - (s : ℂ) * G x := by
    intro x hx
    have hfx : Integrable fun u => f u * Real.exp (x * u) := by
      refine hf.norm.mono' (hm.mul (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rcases le_or_gt 0 u with hu | hu
      · simp [hs u hu]
      · exact mul_le_of_le_one_right (abs_nonneg _)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hx.le hu.le))
    have hA : (∫ u, negExp a u * Real.exp (x * u)) = 1 / (x + a) := by
      have h := laplace_negExp (a := a) (x := x) (by linarith)
      rw [negativeHalfLineLaplace_ofReal] at h
      exact_mod_cast h
    have hsplit : (∫ u, g u * Real.exp (x * u)) =
        (∫ u, negExp a u * Real.exp (x * u)) - s * ∫ u, f u * Real.exp (x * u) := by
      rw [← integral_const_mul,
        ← integral_sub (integrable_negExp_mul_exp (by linarith)) (hfx.const_mul s)]
      exact integral_congr_ae (Eventually.of_forall fun u => by simp only [g]; ring)
    rw [negativeHalfLineLaplace_ofReal, hsplit, hA, ← heq x hx, negativeHalfLineLaplace_ofReal]
    push_cast
    ring
  have hpos : ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ 1 * g u := by
    filter_upwards [hle, ae_restrict_mem measurableSet_Iio] with u hu hmem
    have hu0 : u < 0 := by have : u < -T := hmem; linarith
    simp only [g, one_mul, negExp_of_neg a hu0]
    linarith
  have hgint := integrable_exp_of_signed_tail_of_real_continuation hgm hgi hgs hGg heqg
    (Or.inl rfl) hT hpos hσ
  -- `|f| ≤ |g| + e^{au}`
  refine (hgint.add (integrable_negExp_mul_exp (a := a) (σ := σ) (by linarith))).mono'
    ((hm.abs.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : |f u| ≤ |g u| + negExp a u := by
    have hf' : f u = s * (negExp a u - g u) := by
      simp only [g]
      rcases hsign with rfl | rfl <;> ring
    have h2 := abs_sub_le (negExp a u) 0 (g u)
    rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (negExp_nonneg a u)] at h2
    rw [hf', abs_mul, habs, one_mul]
    linarith
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (σ * u)).le
  simpa only [Pi.add_apply, add_mul] using h3

/-! ### The state -/

/-- The state continuation is regular at every real point. -/
theorem analyticAt_stateMeromorphic_ofReal {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    AnalyticAt ℂ (stateMeromorphic W₀ F) (x : ℂ) := by
  let U := {w : ℂ | xi (w + 17 / 2) ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun
    (xi_differentiable.continuous.comp (continuous_id.add continuous_const)) continuous_const
  have hd : DifferentiableOn ℂ (stateMeromorphic W₀ F) U := by
    intro w hw
    have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := by rw [xi_half_add_shift]; exact hw
    have h := differentiableAt_globalRemainder_of_xi_ne_zero hF hxi
    exact ((h.comp w (differentiableAt_id.add_const (8 : ℂ))).neg.div_const _).differentiableWithinAt
  apply hd.analyticAt (hU.mem_nhds ?_)
  change xi ((x : ℂ) + 17 / 2) ≠ 0
  rw [show (x : ℂ) + 17 / 2 = ((x + 17 / 2 : ℝ) : ℂ) by push_cast; ring]
  exact xi_ne_zero_of_real _

/-- Right of `-4` the continuation is the transform of the state. -/
theorem criticalState_stateMeromorphic_ofReal {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {x : ℝ} (hx : -4 < x) :
    stateMeromorphic W₀ F (x : ℂ) = negativeHalfLineLaplace (cx F) (x : ℂ) := by
  rw [stateMeromorphic_eq_levyContinuation (by simp only [Complex.ofReal_re]; linarith only [hx]),
    levyContinuation_eq_laplace hW ht hF (by simpa only [Complex.ofReal_re] using hx)]

/-- **A one-sided exponential bound reads the zeros.** If `s F ≤ e^{cu}` almost everywhere on a ray,
`c ≥ 7`, then every zero right of the line has `Re ρ ≤ 17/2 - c`. -/
theorem criticalState_re_le_of_tail_le_exp {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s c T : ℝ}
    (hsign : s = 1 ∨ s = -1) (hc : 7 ≤ c)
    (hle : ∀ᵐ u ∂volume.restrict (Iio (-T)), s * F u ≤ Real.exp (c * u))
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re ≤ 17 / 2 - c := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hle' : ∀ᵐ u ∂volume.restrict (Iio (-(max T 0))), s * F u ≤ Real.exp (c * u) :=
    ae_restrict_of_ae_restrict_of_subset (Iio_subset_Iio (neg_le_neg (le_max_left T 0))) hle
  have habs : ∀ σ, -c < σ → Integrable fun u => |F u| * Real.exp (σ * u) := fun σ hσ =>
    integrable_exp_of_tail_le_exp hd.meas hd.integrable hd.support (G := stateMeromorphic W₀ F)
      (by linarith) (fun x _ => analyticAt_stateMeromorphic_ofReal hd x)
      (fun x hx => (criticalState_stateMeromorphic_ofReal hW ht hF (by linarith)).symm)
      hsign (le_max_right T 0) hle' hσ
  have := zero_re_le_of_laplace_holomorphic hW ht hF (κ := -c) (by linarith)
    (differentiableOn_laplace_of_abs hd.meas hd.support habs) hζ hρ
  linarith

/-- **The sign law at the rate of a zero.** For a zero `ρ` right of the line and `c > 17/2 - Re ρ`,
neither `F ≤ e^{cu}` nor `F ≥ -e^{cu}` holds almost everywhere on a ray `u < -T`. -/
theorem criticalState_not_tail_le_exp {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) {c : ℝ} (hc : 17 / 2 - ρ.re < c) (T : ℝ) :
    (¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), F u ≤ Real.exp (c * u)) ∧
      ¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), -Real.exp (c * u) ≤ F u := by
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have hc7 : 7 ≤ c := by linarith
  constructor
  · intro h
    have := criticalState_re_le_of_tail_le_exp hW ht hF (s := 1) (Or.inl rfl) hc7
      (by simpa only [one_mul] using h) hζ hρ
    linarith
  · intro h
    have := criticalState_re_le_of_tail_le_exp hW ht hF (s := -1) (Or.inr rfl) hc7
      (by filter_upwards [h] with u hu; linarith) hζ hρ
    linarith

/-- **The `Ω±` law of the state.** For every `c > 17/2 - Θ` both signs exceed `e^{cu}` on every
ray, while the square moments `∫ F² e^{-bu}` are finite for every `b < 17 - 2Θ`. -/
theorem criticalState_omega_pm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (∀ c : ℝ, 17 / 2 - zetaZeroAbscissa < c → ∀ T : ℝ,
      (¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), F u ≤ Real.exp (c * u)) ∧
        ¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), -Real.exp (c * u) ≤ F u) ∧
      ∀ b : ℝ, b < 17 - 2 * zetaZeroAbscissa →
        Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  refine ⟨fun c hc T => ?_, fun b hb => integrable_sq_mul_exp_of_lt_decayRate hW ht hF hb⟩
  obtain ⟨ρ₀, hζ₀, hρ₀, -⟩ :=
    exists_zetaZero_re_gt_half_of_not_riemannHypothesis (not_riemannHypothesis_of_threshold ht)
  have hΘ : 1 / 2 < zetaZeroAbscissa := lt_of_lt_of_le hρ₀ (re_le_zetaZeroAbscissa hζ₀)
  obtain ⟨ρ, hζ, hρ⟩ := exists_zetaZero_lt_re (b := max (1 / 2) (17 / 2 - c))
    (max_lt hΘ (by linarith))
  have hρc := lt_of_le_of_lt (le_max_right (1 / 2 : ℝ) (17 / 2 - c)) hρ
  exact criticalState_not_tail_le_exp hW ht hF hζ (lt_of_le_of_lt (le_max_left _ _) hρ)
    (by linarith) T

/-! ### The prime side beyond the wall -/

/-- Reflection with one extra damping: `u ↦ e^u Re D(-u)` on `u < 0`. -/
def wallReflection (D : Lp ℂ 2 halfLineLaplaceMeasure) (u : ℝ) : ℝ :=
  (Iio 0).indicator (fun v => Real.exp v * (D (-v)).re) u

theorem measurable_wallReflection (D : Lp ℂ 2 halfLineLaplaceMeasure) :
    Measurable (wallReflection D) :=
  (Real.measurable_exp.mul ((Lp.stronglyMeasurable D).measurable.comp measurable_neg).re).indicator
    measurableSet_Iio

theorem wallReflection_support (D : Lp ℂ 2 halfLineLaplaceMeasure) (u : ℝ) (hu : 0 ≤ u) :
    wallReflection D u = 0 :=
  indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt.mpr hu) _

theorem integrable_wallReflection (D : Lp ℂ 2 halfLineLaplaceMeasure) :
    Integrable (wallReflection D) := by
  have hi := integrableOn_laplaceRay (Lp.memLp D) (w := (1 : ℂ)) (by norm_num)
  have hind := IntegrableOn.integrable_indicator hi.re measurableSet_Ioi
  have hneg := ((Measure.measurePreserving_neg volume).integrable_comp
    hind.aestronglyMeasurable).mpr hind
  refine hneg.congr (Eventually.of_forall fun u => ?_)
  change (Ioi (0 : ℝ)).indicator (fun v => (D v * expRay ((1 : ℝ) : ℂ) v).re) (-u) =
    wallReflection D u
  by_cases hu : u < 0
  · rw [indicator_of_mem (show -u ∈ Ioi (0 : ℝ) from neg_pos.mpr hu),
      wallReflection, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu), expRay_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [show -((1 : ℝ) * (-u)) = u by ring]
    ring
  · rw [indicator_of_notMem (show -u ∉ Ioi (0 : ℝ) from fun hh => hu (neg_pos.mp hh)),
      wallReflection_support D u (not_lt.mp hu)]

theorem laplace_wallReflection (D : Lp ℂ 2 halfLineLaplaceMeasure) {x : ℝ} (hx : 0 < x) :
    negativeHalfLineLaplace (cx (wallReflection D)) (x : ℂ) =
      ((laplaceRay D ((x + 1 : ℝ) : ℂ)).re : ℂ) := by
  have hi := integrableOn_laplaceRay (Lp.memLp D) (w := ((x + 1 : ℝ) : ℂ))
    (by simp only [Complex.ofReal_re]; linarith only [hx])
  have he : (fun u => wallReflection D u * Real.exp (x * u)) =
      fun u : ℝ => (Ioi (0 : ℝ)).indicator
        (fun v => (D v * expRay ((x + 1 : ℝ) : ℂ) v).re) (-u) := by
    funext u
    by_cases hu : u < 0
    · rw [wallReflection, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu),
        indicator_of_mem (show -u ∈ Ioi (0 : ℝ) from neg_pos.mpr hu), expRay_ofReal]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        _ = (D (-u)).re * Real.exp (u + x * u) := by rw [Real.exp_add]; ring
        _ = _ := by congr 2; ring
    · rw [wallReflection_support D u (not_lt.mp hu), zero_mul,
        indicator_of_notMem (show -u ∉ Ioi (0 : ℝ) from fun hh => hu (neg_pos.mp hh))]
  rw [negativeHalfLineLaplace_ofReal, he, integral_neg_eq_self,
    integral_indicator measurableSet_Ioi]
  congr 1
  exact integral_re hi

/-- The continuation is real on the real axis. -/
theorem criticalState_stateMeromorphic_ofReal_re {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (x : ℝ) :
    stateMeromorphic W₀ F (x : ℂ) = ((stateMeromorphic W₀ F (x : ℂ)).re : ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : AnalyticOnNhd ℝ (fun t : ℝ => (stateMeromorphic W₀ F (t : ℂ)).im) univ := fun t _ =>
    (Complex.imCLM.analyticAt _).comp
      (analyticAt_ofReal_comp (analyticAt_stateMeromorphic_ofReal hd t))
  have hev : (fun t : ℝ => (stateMeromorphic W₀ F (t : ℂ)).im) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (-4 : ℝ) < 0 by norm_num)] with t ht'
    change (stateMeromorphic W₀ F (t : ℂ)).im = 0
    rw [criticalState_stateMeromorphic_ofReal hW ht hF ht', negativeHalfLineLaplace_ofReal,
      Complex.ofReal_im]
  have him := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0 : ℝ)) hev (mem_univ x)
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Pi.zero_apply, Complex.ofReal_im] using him

/-- `Re F⁺(v) = e^v Re D(v)` for the unit datum `D` beyond the wall. -/
theorem beyondWallProfile_re (W₀ : ℝ) {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F) (v : ℝ) :
    (beyondWallProfile W₀ hd v).re =
      Real.exp v * ((leftContinuationDatum hd (c := 1) (by norm_num) (by norm_num) W₀ :
        ℝ → ℂ) v).re := by
  rw [beyondWallProfile, unitLeftDatum, ← Complex.ofReal_exp, Complex.re_ofReal_mul]

/-- **A one-sided growth bound beyond the wall hides the left zeros.** If `s Re F⁺ ≤ e^{cx}` almost
everywhere on a ray `x > T`, then every zero with `0 < Re ρ < ½ - c` is unseen:
`LF(ρ - ½) = 0`. -/
theorem criticalState_unseen_of_beyondWall_le_exp {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s c T : ℝ}
    (hsign : s = 1 ∨ s = -1)
    (hle : ∀ᵐ x ∂volume.restrict (Ioi T),
      s * (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re ≤
        Real.exp (c * x))
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) (hρc : ρ.re < 1 / 2 - c) :
    negativeHalfLineLaplace (cx F) (ρ - 1 / 2) = 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let D := leftContinuationDatum hd (c := 1) (by norm_num) (by norm_num) W₀
  let f := wallReflection D
  -- the bound transported to the reflected datum: `s f(u) ≤ e^{(2-c)u}` on `u < -max T 0`
  have hle' : ∀ᵐ u ∂volume.restrict (Iio (-(max T 0))), s * f u ≤ Real.exp ((2 - c) * u) := by
    have hfull := (ae_restrict_iff' measurableSet_Ioi).mp hle
    have hneg := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hfull
    filter_upwards [ae_restrict_of_ae hneg, ae_restrict_mem measurableSet_Iio] with u hu hmem
    have hu' : u < -(max T 0) := hmem
    have hu0 : u < 0 := by linarith only [hu', le_max_right T 0]
    have huT : T < -u := by linarith only [hu', le_max_left T 0]
    have h := hu huT
    rw [beyondWallProfile_re] at h
    change s * (Iio 0).indicator (fun v => Real.exp v * (D (-v)).re) u ≤ _
    rw [indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu0)]
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (2 * u)).le
    have e1 : Real.exp u = Real.exp (2 * u) * Real.exp (-u) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp ((2 - c) * u) = Real.exp (2 * u) * Real.exp (c * -u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, e2]
    calc s * (Real.exp (2 * u) * Real.exp (-u) * (D (-u)).re)
        = Real.exp (2 * u) * (s * (Real.exp (-u) * (D (-u)).re)) := by ring
      _ ≤ _ := h2
  -- Landau against `e^{(2-c)u}`: the reflected transform converges on `Re w > c - 2`
  let G : ℂ → ℂ := fun w => stateMeromorphic W₀ F (-w - 10)
  have hGa (x : ℝ) : AnalyticAt ℂ G (x : ℂ) := by
    have ha : AnalyticAt ℂ (stateMeromorphic W₀ F) (-(x : ℂ) - 10) := by
      rw [show -(x : ℂ) - 10 = ((-x - 10 : ℝ) : ℂ) by push_cast; rfl]
      exact analyticAt_stateMeromorphic_ofReal hd _
    exact ha.comp (f := fun w : ℂ => -w - 10) (analyticAt_id.neg.sub analyticAt_const)
  have heq (x : ℝ) (hx : 0 < x) : negativeHalfLineLaplace (cx f) (x : ℂ) = G x := by
    rw [laplace_wallReflection D hx]
    have hL := stateMeromorphic_eq_laplaceRay_left (W₀ := W₀) hd
      (c := 1) (by norm_num) (by norm_num) (z := ((x + 1 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith only [hx])
    rw [Complex.ofReal_one,
      show -(((x + 1 : ℝ) : ℂ) + (1 : ℂ)) - 8 = ((-x - 10 : ℝ) : ℂ) by push_cast; ring] at hL
    rw [← hL, ← criticalState_stateMeromorphic_ofReal_re hW ht hF]
    dsimp only [G]
    congr 1
    push_cast
    ring
  have habs : ∀ σ, -(2 - c) < σ → Integrable fun u => |f u| * Real.exp (σ * u) := fun σ hσ =>
    integrable_exp_of_tail_le_exp (measurable_wallReflection D) (integrable_wallReflection D)
      (wallReflection_support D) (by linarith) (fun x _ => hGa x) heq hsign
      (le_max_right T 0) hle' hσ
  have hLf := differentiableOn_laplace_of_abs (measurable_wallReflection D)
    (wallReflection_support D) habs
  -- the reflected transform continues the state on `Re w < -8 - c`
  let Ω : Set ℂ := {w : ℂ | w.re < -8 - c}
  have hΩo : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  let H : ℂ → ℂ := fun w => negativeHalfLineLaplace (cx f) (-w - 10)
  have hH : DifferentiableOn ℂ H Ω :=
    hLf.comp (differentiable_id.neg.sub_const (10 : ℂ)).differentiableOn (fun w hw => by
      change w.re < -8 - c at hw
      change -(2 - c) < -w.re - 10
      linarith only [hw])
  let P : ℂ → ℂ := fun w => xi (w + 17 / 2) * H w
  have hP : AnalyticOnNhd ℂ P Ω :=
    ((xi_differentiable.comp (differentiable_id.add_const _)).differentiableOn.mul hH).analyticOnNhd
      hΩo
  have hEq : EqOn (stateXiProduct W₀ F) P Ω := by
    have hA : AnalyticOnNhd ℂ (stateXiProduct W₀ F) Ω := fun w _ =>
      (differentiable_stateXiProduct hd).analyticAt w
    have hm11 : (-11 : ℂ) ∈ Ω := by
      change (-11 : ℂ).re < -8 - c
      norm_num
      linarith
    have hf : ∃ᶠ w : ℂ in 𝓝[≠] (-11 : ℂ), stateXiProduct W₀ F w = P w := by
      have hev : ∀ᶠ x : ℝ in 𝓝[≠] (-11 : ℝ), stateXiProduct W₀ F (x : ℂ) = P (x : ℂ) := by
        filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
          (show (-11 : ℝ) < -10 by norm_num))] with x hx
        have hx' : x < -10 := hx
        have hxi : xi ((x : ℂ) + 17 / 2) ≠ 0 := by
          rw [show (x : ℂ) + 17 / 2 = ((x + 17 / 2 : ℝ) : ℂ) by push_cast; ring]
          exact xi_ne_zero_of_real _
        rw [stateXiProduct_eq hd hxi]
        dsimp only [P, H]
        congr 1
        have h := heq (-x - 10) (by linarith only [hx'])
        rw [show ((-x - 10 : ℝ) : ℂ) = -(x : ℂ) - 10 by push_cast; ring] at h
        rw [h]
        dsimp only [G]
        congr 1
        ring
      simpa using (tendsto_ofReal_nhdsNE (-11)).frequently hev.frequently
    exact hA.eqOn_of_preconnected_of_frequently_eq hP (convex_halfSpace_re_lt _).isPreconnected
      hm11 hf
  -- the product keeps the full multiplicity of `ρ`, so `ρ` is unseen
  let z : ℂ := ρ - 1 / 2
  have hz8 : z - 8 ∈ Ω := by
    change (ρ - 1 / 2 - 8).re < -8 - c
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hxi : xi (1 / 2 + z) = 0 := by
    rw [show (1 : ℂ) / 2 + z = ρ by dsimp only [z]; ring]
    exact (xi_eq_zero_iff_riemannZeta_of_re_pos hρ0 (fun e =>
      riemannZeta_ne_zero_of_one_le_re (by rw [e]; norm_num) hζ)).mpr hζ
  apply (le_analyticOrderAt_stateXiProduct_iff hW hd hxi).mp
  rw [analyticOrderAt_congr (Filter.eventuallyEq_of_mem (hΩo.mem_nhds hz8) hEq)]
  have hξ : AnalyticAt ℂ (fun w : ℂ => xi (w + 17 / 2)) (z - 8) :=
    (xi_differentiable.comp (differentiable_id.add_const _)).analyticAt _
  have hord : analyticOrderAt (fun w : ℂ => xi (w + 17 / 2)) (z - 8) =
      analyticOrderAt xi (1 / 2 + z) := by
    have he : analyticOrderAt (fun w : ℂ => xi (w + 17 / 2)) (z - 8) =
        analyticOrderAt xi (z - 8 + 17 / 2) := by
      apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi)
        (g := fun w : ℂ => w + 17 / 2) (by fun_prop)
      simp
    simpa only [show z - 8 + 17 / 2 = (1 : ℂ) / 2 + z by ring] using he
  change analyticOrderAt xi (1 / 2 + z) ≤
    analyticOrderAt ((fun w : ℂ => xi (w + 17 / 2)) * H) (z - 8)
  rw [analyticOrderAt_mul hξ (hH.analyticAt (hΩo.mem_nhds hz8)), hord]
  exact le_self_add

/-- **The sign law beyond the wall at the rate of a seen zero.** For a seen zero `ρ`
(`LF(ρ - ½) ≠ 0`, `Re ρ > 0`) and `c < ½ - Re ρ`, neither `Re F⁺ ≤ e^{cx}` nor
`Re F⁺ ≥ -e^{cx}` holds almost everywhere on a ray `x > T`. -/
theorem criticalState_beyondWall_not_tail_le_exp {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ0 : 0 < ρ.re) (hseen : negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0)
    {c : ℝ} (hc : c < 1 / 2 - ρ.re) (T : ℝ) :
    let hd := criticalHalfLineEnergyDomain_of_groundState hF
    (¬ ∀ᵐ x ∂volume.restrict (Ioi T), (beyondWallProfile W₀ hd x).re ≤ Real.exp (c * x)) ∧
      ¬ ∀ᵐ x ∂volume.restrict (Ioi T), -Real.exp (c * x) ≤ (beyondWallProfile W₀ hd x).re := by
  constructor
  · intro h
    exact hseen (criticalState_unseen_of_beyondWall_le_exp hW ht hF (s := 1) (Or.inl rfl)
      (by simpa only [one_mul] using h) hζ hρ0 (by linarith))
  · intro h
    exact hseen (criticalState_unseen_of_beyondWall_le_exp hW ht hF (s := -1) (Or.inr rfl)
      (by filter_upwards [h] with x hx; linarith) hζ hρ0 (by linarith))

/-- **The prime side grows exponentially in both signs.** For some `c₀ > 0` (half the distance of a
seen left zero from the line times two: `c₀ = ½ - Re ρ`), both signs of `Re F⁺` exceed `e^{cx}` on
every ray for every `c < c₀`. -/
theorem criticalState_beyondWall_omega_pm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c < c₀ → ∀ T : ℝ,
      (¬ ∀ᵐ x ∂volume.restrict (Ioi T),
          (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re ≤
            Real.exp (c * x)) ∧
        ¬ ∀ᵐ x ∂volume.restrict (Ioi T), -Real.exp (c * x) ≤
          (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re := by
  obtain ⟨ρ, hζ, hρ0, hρ, hseen⟩ := criticalState_exists_seen_left_zetaZero hW ht hF
  exact ⟨1 / 2 - ρ.re, by linarith, fun c hc T =>
    criticalState_beyondWall_not_tail_le_exp hW ht hF hζ hρ0 hseen hc T⟩

/-- Either RH holds, or the critical state exists and obeys both `Ω±` laws: on the state side at
every rate above `17/2 - Θ`, beyond the wall at every rate below some `c₀ > 0`. -/
theorem riemannHypothesis_or_criticalState_omega_pm :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ) (_ : 0 < W₀)
        (_ : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
        (hF : IsCriticalHalfLineGroundState W₀ F),
        (∀ c : ℝ, 17 / 2 - zetaZeroAbscissa < c → ∀ T : ℝ,
          (¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), F u ≤ Real.exp (c * u)) ∧
            ¬ ∀ᵐ u ∂volume.restrict (Iio (-T)), -Real.exp (c * u) ≤ F u) ∧
        ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c < c₀ → ∀ T : ℝ,
          (¬ ∀ᵐ x ∂volume.restrict (Ioi T),
              (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re ≤
                Real.exp (c * x)) ∧
            ¬ ∀ᵐ x ∂volume.restrict (Ioi T), -Real.exp (c * x) ≤
              (beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) x).re := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, (criticalState_omega_pm hW ht hF).1,
      criticalState_beyondWall_omega_pm hW ht hF⟩

#print axioms criticalState_omega_pm
#print axioms criticalState_beyondWall_omega_pm
#print axioms riemannHypothesis_or_criticalState_omega_pm

end GaloisForLFunctions.ExclusionOfTheCriticalState
