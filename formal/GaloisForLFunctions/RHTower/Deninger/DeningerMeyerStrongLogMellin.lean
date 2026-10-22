import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogTarget
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace

/-!
# Entire Mellin transform of Meyer's all-weight logarithmic target

The all-exponential decay defining `DeningerMeyerStrongLogTarget` is exactly
what is needed to form every logarithmic Mellin moment at every complex
spectral parameter.  This file proves the resulting transform entire, computes
all of its spectral derivatives, identifies its imaginary-axis restriction
with the ordinary Fourier transform, and proves injectivity.

Paugam's weighted reciprocal involution becomes the exact reflection
`s ↦ 1 - s`.  Thus the target carries a faithful entire spectral transform
before any trace formula, zero-set quotient, or positivity hypothesis is
introduced.

No Riemann-hypothesis premise, spectral realization, numerical computation,
or source-provenance hypothesis occurs.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The `k`-th logarithmic Mellin jet integrand. -/
def deningerMeyerStrongLogMellinJet
    (k : ℕ) (s : ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ k * Complex.exp (s * (t : ℂ)) * g t

theorem norm_deningerMeyerStrongLogMellinJet
    (k : ℕ) (s : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    ‖deningerMeyerStrongLogMellinJet k s g t‖ =
      |t| ^ k * Real.exp (s.re * t) * ‖g t‖ := by
  rw [deningerMeyerStrongLogMellinJet, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  congr 2
  simp [mul_re]

/--
Every spectral jet is integrable at every complex parameter.  This is where
the full all-weight condition is essential: ordinary Schwartz decay in `t`
would not control arbitrary `Re(s)`.
-/
theorem integrable_deningerMeyerStrongLogMellinJet
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (k : ℕ) (s : ℂ) :
    Integrable (deningerMeyerStrongLogMellinJet k s g) := by
  have hloc :
      LocallyIntegrable (deningerMeyerStrongLogMellinJet k s g) := by
    apply Continuous.locallyIntegrable
    have hgcont : Continuous g := hg.smooth.continuous
    unfold deningerMeyerStrongLogMellinJet
    fun_prop
  let qTop : ℝ → ℝ := fun t => |t| ^ k * Real.exp (-t)
  let qBot : ℝ → ℝ := fun t => |t| ^ k * Real.exp t
  have hq :
      Integrable (fun t : ℝ =>
        |t| ^ k * Real.exp (-1 * |t|)) :=
    integrable_abs_pow_mul_exp_neg_mul_abs k one_pos
  have hqTop : IntegrableAtFilter qTop atTop := by
    rw [integrableAtFilter_atTop_iff]
    refine ⟨0, ?_⟩
    apply
      (hq.integrableOn.mono_set
        (subset_univ (Ici 0))).congr_fun _ measurableSet_Ici
    intro t ht
    dsimp [qTop]
    rw [abs_of_nonneg ht]
    congr 2
    ring
  have hqBot : IntegrableAtFilter qBot atBot := by
    rw [integrableAtFilter_atBot_iff]
    refine ⟨0, ?_⟩
    apply
      (hq.integrableOn.mono_set
        (subset_univ (Iic 0))).congr_fun _ measurableSet_Iic
    intro t ht
    dsimp [qBot]
    rw [abs_of_nonpos ht]
    congr 2
    ring
  have htopBase := hg.decayTop 0 (s.re + 2)
  rw [iteratedDeriv_zero] at htopBase
  obtain ⟨Ctop, hCtop⟩ := htopBase.bound
  have htop :
      deningerMeyerStrongLogMellinJet k s g =O[atTop] qTop := by
    apply (IsBigOWith.of_bound (c := max Ctop 0) ?_).isBigO
    filter_upwards [hCtop, eventually_ge_atTop 0] with t ht ht0
    have ht' :
        ‖g t‖ ≤
          max Ctop 0 * ‖Real.exp t ^ (-(s.re + 2))‖ :=
      ht.trans
        (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (norm_nonneg _))
    rw [norm_deningerMeyerStrongLogMellinJet]
    dsimp [qTop]
    rw [abs_of_nonneg
      (mul_nonneg
        (pow_nonneg (abs_nonneg t) k) (Real.exp_pos _).le)]
    have hpow :
        ‖Real.exp t ^ (-(s.re + 2))‖ =
          Real.exp (-(s.re + 2) * t) := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (Real.rpow_nonneg (Real.exp_pos t).le _),
        Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
      congr 1
      ring
    rw [hpow] at ht'
    calc
      |t| ^ k * Real.exp (s.re * t) * ‖g t‖ ≤
          |t| ^ k * Real.exp (s.re * t) *
            (max Ctop 0 *
              Real.exp (-(s.re + 2) * t)) := by
        gcongr
      _ = max Ctop 0 *
          (|t| ^ k * Real.exp (-2 * t)) := by
        have hexp :
            Real.exp (s.re * t) *
                Real.exp (-(s.re + 2) * t) =
              Real.exp (-2 * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show
            |t| ^ k * Real.exp (s.re * t) *
                (max Ctop 0 *
                  Real.exp (-(s.re + 2) * t)) =
              max Ctop 0 * |t| ^ k *
                (Real.exp (s.re * t) *
                  Real.exp (-(s.re + 2) * t)) by
              ring,
          hexp]
        ring
      _ ≤ max Ctop 0 *
          (|t| ^ k * Real.exp (-t)) := by
        have hexp :
            Real.exp (-2 * t) ≤ Real.exp (-t) :=
          Real.exp_le_exp.mpr (by linarith)
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp
              (pow_nonneg (abs_nonneg t) k))
            (le_max_right _ _)
  have hbotBase := hg.decayBot 0 (2 - s.re)
  rw [iteratedDeriv_zero] at hbotBase
  obtain ⟨Cbot, hCbot⟩ := hbotBase.bound
  have hbot :
      deningerMeyerStrongLogMellinJet k s g =O[atBot] qBot := by
    apply (IsBigOWith.of_bound (c := max Cbot 0) ?_).isBigO
    filter_upwards [hCbot, eventually_le_atBot 0] with t ht ht0
    have ht' :
        ‖g t‖ ≤
          max Cbot 0 * ‖Real.exp t ^ (2 - s.re)‖ :=
      ht.trans
        (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (norm_nonneg _))
    rw [norm_deningerMeyerStrongLogMellinJet]
    dsimp [qBot]
    rw [abs_of_nonneg
      (mul_nonneg
        (pow_nonneg (abs_nonneg t) k) (Real.exp_pos _).le)]
    have hpow :
        ‖Real.exp t ^ (2 - s.re)‖ =
          Real.exp ((2 - s.re) * t) := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (Real.rpow_nonneg (Real.exp_pos t).le _),
        Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
      congr 1
      ring
    rw [hpow] at ht'
    calc
      |t| ^ k * Real.exp (s.re * t) * ‖g t‖ ≤
          |t| ^ k * Real.exp (s.re * t) *
            (max Cbot 0 *
              Real.exp ((2 - s.re) * t)) := by
        gcongr
      _ = max Cbot 0 *
          (|t| ^ k * Real.exp (2 * t)) := by
        have hexp :
            Real.exp (s.re * t) *
                Real.exp ((2 - s.re) * t) =
              Real.exp (2 * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show
            |t| ^ k * Real.exp (s.re * t) *
                (max Cbot 0 *
                  Real.exp ((2 - s.re) * t)) =
              max Cbot 0 * |t| ^ k *
                (Real.exp (s.re * t) *
                  Real.exp ((2 - s.re) * t)) by
              ring,
          hexp]
        ring
      _ ≤ max Cbot 0 *
          (|t| ^ k * Real.exp t) := by
        have hexp :
            Real.exp (2 * t) ≤ Real.exp t :=
          Real.exp_le_exp.mpr (by linarith)
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp
              (pow_nonneg (abs_nonneg t) k))
            (le_max_right _ _)
  exact
    hloc.integrable_of_isBigO_atBot_atTop
      hbot hqBot htop hqTop

/--
Uniform integrable majorant for every polynomial moment and every exponential
weight.  This is the dominated-differentiation engine for the entire transform.
-/
theorem integrable_deningerMeyerStrongLogAbsMoment
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (k : ℕ) (B : ℝ) :
    Integrable (fun t : ℝ =>
      |t| ^ k * Real.exp (B * |t|) * ‖g t‖) := by
  rw [← integrableOn_univ,
    ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · have hbase :=
      (integrable_deningerMeyerStrongLogMellinJet
        hg k ((-B : ℝ) : ℂ)).norm
    apply
      hbase.integrableOn.mono_set
        (subset_univ (Iic 0)) |>.congr_fun _ measurableSet_Iic
    intro t ht
    change
      ‖deningerMeyerStrongLogMellinJet
          k ((-B : ℝ) : ℂ) g t‖ =
        |t| ^ k * Real.exp (B * |t|) * ‖g t‖
    rw [norm_deningerMeyerStrongLogMellinJet,
      Complex.ofReal_re, abs_of_nonpos ht]
    congr 2
    ring
  · have hbase :=
      (integrable_deningerMeyerStrongLogMellinJet
        hg k (B : ℂ)).norm
    apply
      hbase.integrableOn.mono_set
        (subset_univ (Ioi 0)) |>.congr_fun _ measurableSet_Ioi
    intro t ht
    change
      ‖deningerMeyerStrongLogMellinJet
          k (B : ℂ) g t‖ =
        |t| ^ k * Real.exp (B * |t|) * ‖g t‖
    rw [norm_deningerMeyerStrongLogMellinJet,
      Complex.ofReal_re, abs_of_pos ht]

theorem hasDerivAt_deningerMeyerStrongLogMellinJet
    (k : ℕ) (s : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    HasDerivAt
      (fun z : ℂ =>
        deningerMeyerStrongLogMellinJet k z g t)
      (deningerMeyerStrongLogMellinJet (k + 1) s g t) s := by
  have hinner :
      HasDerivAt
        (fun z : ℂ => z * (t : ℂ)) (t : ℂ) s := by
    simpa using
      (hasDerivAt_id s).mul_const (t : ℂ)
  have hexp :=
    (Complex.hasDerivAt_exp
      (s * (t : ℂ))).comp s hinner
  have hscaled :=
    hexp.const_mul ((t : ℂ) ^ k * g t)
  have hcoef :
      (t : ℂ) ^ k * g t *
          (Complex.exp (s * (t : ℂ)) * (t : ℂ)) =
        deningerMeyerStrongLogMellinJet
          (k + 1) s g t := by
    simp only [
      deningerMeyerStrongLogMellinJet, pow_succ]
    ring
  apply
    (hscaled.congr_deriv hcoef).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => by
    simp only [
      deningerMeyerStrongLogMellinJet,
      Function.comp_apply]
    ring

theorem hasDerivAt_integral_deningerMeyerStrongLogMellinJet
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (k : ℕ) (s₀ : ℂ) :
    HasDerivAt
      (fun s : ℂ =>
        ∫ t : ℝ,
          deningerMeyerStrongLogMellinJet k s g t)
      (∫ t : ℝ,
        deningerMeyerStrongLogMellinJet
          (k + 1) s₀ g t) s₀ := by
  let ε : ℝ := 1
  let B : ℝ := |s₀.re| + 1
  let bound : ℝ → ℝ := fun t =>
    |t| ^ (k + 1) * Real.exp (B * |t|) * ‖g t‖
  have hε : 0 < ε := by simp [ε]
  have hre {z : ℂ} (hz : z ∈ Metric.ball s₀ ε) :
      |z.re| ≤ B := by
    have hdist : ‖z - s₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have hrediff :
        |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      simpa only [Complex.sub_re] using
        Complex.abs_re_le_norm (z - s₀)
    calc
      |z.re| =
          |s₀.re + (z.re - s₀.re)| := by
            ring_nf
      _ ≤ |s₀.re| + |z.re - s₀.re| :=
        abs_add_le _ _
      _ ≤ |s₀.re| + 1 := by
        dsimp [ε] at hdist
        linarith
      _ = B := rfl
  have hbound : Integrable bound :=
    integrable_deningerMeyerStrongLogAbsMoment
      hg (k + 1) B
  have hFmeas :
      ∀ z : ℂ,
        AEStronglyMeasurable
          (deningerMeyerStrongLogMellinJet k z g) := by
    intro z
    exact
      (integrable_deningerMeyerStrongLogMellinJet
        hg k z).1
  have hF'meas :
      AEStronglyMeasurable
        (deningerMeyerStrongLogMellinJet
          (k + 1) s₀ g) :=
    (integrable_deningerMeyerStrongLogMellinJet
      hg (k + 1) s₀).1
  have hdom :
      ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball s₀ ε,
        ‖deningerMeyerStrongLogMellinJet
          (k + 1) z g t‖ ≤ bound t := by
    filter_upwards with t
    intro z hz
    have hzB := hre hz
    rw [norm_deningerMeyerStrongLogMellinJet]
    dsimp [bound]
    have hzt : z.re * t ≤ B * |t| := by
      calc
        z.re * t ≤ |z.re * t| := le_abs_self _
        _ = |z.re| * |t| := abs_mul _ _
        _ ≤ B * |t| :=
          mul_le_mul_of_nonneg_right
            hzB (abs_nonneg t)
    gcongr
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z t =>
        deningerMeyerStrongLogMellinJet k z g t)
      (F' := fun z t =>
        deningerMeyerStrongLogMellinJet
          (k + 1) z g t)
      (x₀ := s₀) (s := Metric.ball s₀ ε)
      (bound := bound)
      (Metric.ball_mem_nhds s₀ hε)
      (Filter.Eventually.of_forall hFmeas)
      (integrable_deningerMeyerStrongLogMellinJet
        hg k s₀)
      hF'meas hdom hbound
      (by
        filter_upwards with t
        intro z hz
        exact
          hasDerivAt_deningerMeyerStrongLogMellinJet
            k z g t)
  exact hresult.2

/--
Entire logarithmic Mellin transform
`s ↦ ∫ exp(s t) g(t) dt`.
-/
def deningerMeyerStrongLogMellin
    (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ,
    deningerMeyerStrongLogMellinJet 0 s g t

theorem hasDerivAt_deningerMeyerStrongLogMellin
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (s : ℂ) :
    HasDerivAt (deningerMeyerStrongLogMellin g)
      (∫ t : ℝ,
        deningerMeyerStrongLogMellinJet 1 s g t) s := by
  change
    HasDerivAt
      (fun s : ℂ =>
        ∫ t : ℝ,
          deningerMeyerStrongLogMellinJet 0 s g t)
      (∫ t : ℝ,
        deningerMeyerStrongLogMellinJet 1 s g t) s
  exact
    hasDerivAt_integral_deningerMeyerStrongLogMellinJet
      hg 0 s

theorem differentiable_deningerMeyerStrongLogMellin
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) :
    Differentiable ℂ (deningerMeyerStrongLogMellin g) :=
  fun s =>
    (hasDerivAt_deningerMeyerStrongLogMellin
      hg s).differentiableAt

/--
All-order spectral jet law: every derivative of the entire transform is the
corresponding logarithmic moment.
-/
theorem
    iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (k : ℕ) (s : ℂ) :
    iteratedDeriv k
        (deningerMeyerStrongLogMellin g) s =
      ∫ t : ℝ,
        deningerMeyerStrongLogMellinJet k s g t := by
  induction k generalizing s with
  | zero =>
      simp only [
        iteratedDeriv_zero,
        deningerMeyerStrongLogMellin]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv k
              (deningerMeyerStrongLogMellin g) =
            fun z : ℂ =>
              ∫ t : ℝ,
                deningerMeyerStrongLogMellinJet
                  k z g t := by
        funext z
        exact ih z
      rw [heq]
      exact
        (hasDerivAt_integral_deningerMeyerStrongLogMellinJet
          hg k s).deriv

theorem analyticOnNhd_deningerMeyerStrongLogMellin
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) :
    AnalyticOnNhd ℂ
      (deningerMeyerStrongLogMellin g) Set.univ :=
  (differentiable_deningerMeyerStrongLogMellin hg).differentiableOn
    |>.analyticOnNhd isOpen_univ

/-- Evaluation of the entire Mellin transform at a fixed spectral point. -/
def deningerMeyerStrongLogMellinLM (s : ℂ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ where
  toFun g := deningerMeyerStrongLogMellin g s
  map_add' g h := by
    change
      (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            0 s (g.val + h.val) t) =
        (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            0 s g.val t) +
        ∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            0 s h.val t
    have heq :
        deningerMeyerStrongLogMellinJet
            0 s (g.val + h.val) =
          deningerMeyerStrongLogMellinJet
              0 s g.val +
            deningerMeyerStrongLogMellinJet
              0 s h.val := by
      funext t
      simp only [
        deningerMeyerStrongLogMellinJet,
        Pi.add_apply]
      ring
    rw [heq]
    simpa only [Pi.add_apply] using
      integral_add
        (integrable_deningerMeyerStrongLogMellinJet
          g.property 0 s)
        (integrable_deningerMeyerStrongLogMellinJet
          h.property 0 s)
  map_smul' c g := by
    change
      (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            0 s (c • g.val) t) =
        c •
          ∫ t : ℝ,
            deningerMeyerStrongLogMellinJet
              0 s g.val t
    have heq :
        deningerMeyerStrongLogMellinJet
            0 s (c • g.val) =
          fun t =>
            c *
              deningerMeyerStrongLogMellinJet
                0 s g.val t := by
      funext t
      simp only [
        deningerMeyerStrongLogMellinJet,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, integral_const_mul, smul_eq_mul]

/--
Paugam's weighted reciprocal involution acts on the faithful entire transform
by reflection about the critical line.
-/
theorem deningerMeyerStrongLogMellin_J
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogJ g) s =
      deningerMeyerStrongLogMellin g (1 - s) := by
  rw [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellin,
    ← integral_neg_eq_self
      (fun t : ℝ =>
        deningerMeyerStrongLogMellinJet
          0 (1 - s) g t) volume]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet,
    deningerMeyerStrongLogMellinJet,
    deningerMeyerStrongLogJ_apply]
  simp only [pow_zero, one_mul, Complex.ofReal_neg]
  rw [Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/--
On the imaginary axis, the entire logarithmic Mellin transform is the real
Fourier transform under the exact `2π` normalization.
-/
theorem deningerMeyerStrongLogMellin_eq_fourier
    (g : DeningerMeyerStrongLogTarget) (w : ℝ) :
    deningerMeyerStrongLogMellin g
        (-((2 * Real.pi * w : ℝ) : ℂ) * I) =
      FourierTransform.fourier (g : ℝ → ℂ) w := by
  rw [deningerMeyerStrongLogMellin,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

/--
The entire logarithmic Mellin transform separates the all-weight Meyer target.
Only its imaginary-axis restriction is needed: Fourier inversion upgrades
spectral equality to pointwise equality using continuity of the target.
-/
theorem deningerMeyerStrongLogMellin_injective :
    Function.Injective
      (fun g : DeningerMeyerStrongLogTarget =>
        deningerMeyerStrongLogMellin g) := by
  intro g h hgh
  apply Subtype.ext
  funext t
  let d : ℝ → ℂ :=
    (g : ℝ → ℂ) - (h : ℝ → ℂ)
  have hdDecay : DeningerMeyerStrongLogDecay d := by
    dsimp [d]
    exact g.property.add h.property.neg
  have hfourier :
      FourierTransform.fourier (g : ℝ → ℂ) =
        FourierTransform.fourier (h : ℝ → ℂ) := by
    funext w
    rw [← deningerMeyerStrongLogMellin_eq_fourier g w,
      ← deningerMeyerStrongLogMellin_eq_fourier h w]
    exact
      congrFun hgh
        (-((2 * Real.pi * w : ℝ) : ℂ) * I)
  have hgint : Integrable (g : ℝ → ℂ) := by
    have hjet :
        deningerMeyerStrongLogMellinJet
            0 (0 : ℂ) (g : ℝ → ℂ) =
          g := by
      funext x
      simp only [
        deningerMeyerStrongLogMellinJet,
        pow_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [← hjet]
    exact
      integrable_deningerMeyerStrongLogMellinJet
        g.property 0 (0 : ℂ)
  have hhint : Integrable (h : ℝ → ℂ) := by
    have hjet :
        deningerMeyerStrongLogMellinJet
            0 (0 : ℂ) (h : ℝ → ℂ) =
          h := by
      funext x
      simp only [
        deningerMeyerStrongLogMellinJet,
        pow_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [← hjet]
    exact
      integrable_deningerMeyerStrongLogMellinJet
        h.property 0 (0 : ℂ)
  have hdfourier :
      FourierTransform.fourier d = 0 := by
    funext w
    calc
      FourierTransform.fourier d w =
          FourierTransform.fourier
              (g : ℝ → ℂ) w -
            FourierTransform.fourier
              (h : ℝ → ℂ) w := by
        rw [Real.fourier_real_eq,
          Real.fourier_real_eq, Real.fourier_real_eq]
        dsimp [d]
        simp only [smul_sub]
        rw [integral_sub]
        · simpa only [Real.inner_apply] using
            (Real.fourierIntegral_convergent_iff w).mpr
              hgint
        · simpa only [Real.inner_apply] using
            (Real.fourierIntegral_convergent_iff w).mpr
              hhint
      _ = 0 := by
        rw [congrFun hfourier w, sub_self]
  have hdint : Integrable d := by
    have hjet :
        deningerMeyerStrongLogMellinJet
            0 (0 : ℂ) d =
          d := by
      funext x
      simp only [
        deningerMeyerStrongLogMellinJet,
        pow_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [← hjet]
    exact
      integrable_deningerMeyerStrongLogMellinJet
        hdDecay 0 (0 : ℂ)
  have hdcont : Continuous d :=
    hdDecay.smooth.continuous
  have hfdint :
      Integrable (FourierTransform.fourier d) := by
    rw [hdfourier]
    exact integrable_zero _ _ _
  have hinv :=
    hdcont.fourierInv_fourier_eq hdint hfdint
  have hd0 : d = 0 := by
    rw [hdfourier] at hinv
    have hinvZero :
        FourierTransform.fourierInv
            (0 : ℝ → ℂ) =
          0 := by
      funext w
      rw [Real.fourierInv_eq]
      simp only [Pi.zero_apply, smul_zero, integral_zero]
    rw [hinvZero] at hinv
    exact hinv.symm
  have ht := congrFun hd0 t
  dsimp [d] at ht
  simpa using sub_eq_zero.mp ht

end

end RHTower
