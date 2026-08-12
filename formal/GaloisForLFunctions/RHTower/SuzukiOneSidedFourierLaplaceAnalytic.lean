import GaloisForLFunctions.RHTower.SuzukiOneSidedFourierLaplace
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of Suzuki's one-sided `L²` Fourier--Laplace transforms

Suzuki's continuation argument in Lemma 4.3 applies the identity theorem to Fourier transforms of
arbitrary `L²` functions supported on a half-line.  This module supplies the missing analytic
foundation.  Strictly inside the upper half-plane, exponential damping makes every such evaluation
absolutely convergent.  A local dominated-differentiation argument proves holomorphy, and in fact
identifies every spectral derivative with its polynomially weighted integral.

No pointwise decay, smoothness, compact support, or analytic-continuation hypothesis is imposed on
the `L²` source.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

/-! ## Polynomial--exponential half-line weights -/

/-- Natural powers times a growing exponential are integrable on every left half-line when the
exponential rate is positive. -/
theorem integrableOn_abs_pow_mul_exp_mul_Iic
    (n : ℕ) {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp (b * t)) (Iic A) := by
  let f : ℝ → ℝ := fun t => |t| ^ n * Real.exp (b * t)
  have hglobal := HTGeometry.integrable_abs_pow_mul_exp_neg_abs n hb
  have hneg : IntegrableOn f (Iic 0) := by
    apply hglobal.integrableOn.congr_fun (fun t ht => ?_) measurableSet_Iic
    dsimp only [f]
    rw [abs_of_nonpos ht]
    congr 2
    ring_nf
  by_cases hA : A ≤ 0
  · exact hneg.mono_set (Iic_subset_Iic.mpr hA)
  · have hzeroA : 0 ≤ A := (lt_of_not_ge hA).le
    have hpos : IntegrableOn f (Ioc 0 A) := by
      exact ((by fun_prop : Continuous f).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [← Iic_union_Ioc_eq_Iic hzeroA]
    exact hneg.union hpos

/-- Reflected version of `integrableOn_abs_pow_mul_exp_mul_Iic` on a right half-line. -/
theorem integrableOn_abs_pow_mul_exp_neg_mul_Ici
    (n : ℕ) {b : ℝ} (hb : 0 < b) (B : ℝ) :
    IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp (-b * t)) (Ici B) := by
  have h := integrableOn_abs_pow_mul_exp_mul_Iic n hb (-B)
  have hreflect := h.comp_neg_Ici
  apply hreflect.congr_fun (fun t _ => ?_) measurableSet_Ici
  simp only [abs_neg]
  congr 2
  ring

/-- `L²` polynomial--exponential weight on a left half-line. -/
def suzukiUpperFourierLaplaceJetWeight
    (A : ℝ) (k : ℕ) (b : ℝ) (t : ℝ) : ℂ :=
  (Iic A).indicator
    (fun t : ℝ => ((|t| ^ k * Real.exp (b * t) : ℝ) : ℂ)) t

theorem suzukiUpperFourierLaplaceJetWeight_memLp
    (A : ℝ) (k : ℕ) {b : ℝ} (hb : 0 < b) :
    MemLp (suzukiUpperFourierLaplaceJetWeight A k b) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (suzukiUpperFourierLaplaceJetWeight A k b) volume :=
    ((by fun_prop : Continuous fun t : ℝ =>
      ((|t| ^ k * Real.exp (b * t) : ℝ) : ℂ))
      |>.aestronglyMeasurable.indicator measurableSet_Iic)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have heq :
      (fun t : ℝ => ‖suzukiUpperFourierLaplaceJetWeight A k b t‖ ^ 2) =
        (Iic A).indicator
          (fun t : ℝ => |t| ^ (2 * k) * Real.exp ((2 * b) * t)) := by
    funext t
    by_cases ht : t ∈ Iic A
    · rw [suzukiUpperFourierLaplaceJetWeight, indicator_of_mem ht,
        indicator_of_mem ht, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) k)
          (Real.exp_pos _).le), mul_pow, ← Real.exp_nat_mul]
      ring
    · simp [suzukiUpperFourierLaplaceJetWeight, ht]
  rw [heq, integrable_indicator_iff measurableSet_Iic]
  exact integrableOn_abs_pow_mul_exp_mul_Iic (2 * k) (by linarith) A

/-- `L²` polynomial--exponential weight on a right half-line. -/
def suzukiLowerFourierLaplaceJetWeight
    (B : ℝ) (k : ℕ) (b : ℝ) (t : ℝ) : ℂ :=
  (Ici B).indicator
    (fun t : ℝ => ((|t| ^ k * Real.exp (-b * t) : ℝ) : ℂ)) t

theorem suzukiLowerFourierLaplaceJetWeight_memLp
    (B : ℝ) (k : ℕ) {b : ℝ} (hb : 0 < b) :
    MemLp (suzukiLowerFourierLaplaceJetWeight B k b) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (suzukiLowerFourierLaplaceJetWeight B k b) volume :=
    ((by fun_prop : Continuous fun t : ℝ =>
      ((|t| ^ k * Real.exp (-b * t) : ℝ) : ℂ))
      |>.aestronglyMeasurable.indicator measurableSet_Ici)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have heq :
      (fun t : ℝ => ‖suzukiLowerFourierLaplaceJetWeight B k b t‖ ^ 2) =
        (Ici B).indicator
          (fun t : ℝ => |t| ^ (2 * k) * Real.exp (-(2 * b) * t)) := by
    funext t
    by_cases ht : t ∈ Ici B
    · rw [suzukiLowerFourierLaplaceJetWeight, indicator_of_mem ht,
        indicator_of_mem ht, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) k)
          (Real.exp_pos _).le), mul_pow, ← Real.exp_nat_mul]
      have hpow : (|t| ^ k) ^ 2 = |t| ^ (2 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow]
      congr 1
      apply congrArg Real.exp
      norm_num
      ring
    · simp [suzukiLowerFourierLaplaceJetWeight, ht]
  rw [heq, integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_abs_pow_mul_exp_neg_mul_Ici (2 * k) (by linarith) B

/-! ## Upper-supported transform and all-order jets -/

def suzukiUpperFourierLaplaceIntegrand
    (A : ℝ) (q : SoninL2) (z : ℂ) (t : ℝ) : ℂ :=
  (Iic A).indicator
    (fun t : ℝ => Complex.exp (-I * z * (t : ℂ)) * q t) t

def suzukiUpperFourierLaplace (A : ℝ) (q : SoninL2) (z : ℂ) : ℂ :=
  ∫ t : ℝ, suzukiUpperFourierLaplaceIntegrand A q z t

def suzukiUpperFourierLaplaceJetIntegrand
    (A : ℝ) (q : SoninL2) (k : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (-I * (t : ℂ)) ^ k * suzukiUpperFourierLaplaceIntegrand A q z t

theorem hasDerivAt_suzukiUpperFourierLaplaceJetIntegrand
    (A : ℝ) (q : SoninL2) (k : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt
      (fun w : ℂ => suzukiUpperFourierLaplaceJetIntegrand A q k w t)
      (suzukiUpperFourierLaplaceJetIntegrand A q (k + 1) z t) z := by
  by_cases ht : t ∈ Iic A
  · unfold suzukiUpperFourierLaplaceJetIntegrand
      suzukiUpperFourierLaplaceIntegrand
    simp only [indicator_of_mem ht]
    have hlin : HasDerivAt (fun w : ℂ => -I * w * (t : ℂ))
        (-I * (t : ℂ)) z := by
      simpa using! (((hasDerivAt_id z).const_mul (-I)).mul_const (t : ℂ))
    refine ((hlin.cexp.mul_const (q t)).const_mul
      ((-I * (t : ℂ)) ^ k)).congr_deriv ?_
    rw [pow_succ]
    ring
  · have hzero : ∀ w : ℂ,
        suzukiUpperFourierLaplaceJetIntegrand A q k w t = 0 := by
      intro w
      simp [suzukiUpperFourierLaplaceJetIntegrand,
        suzukiUpperFourierLaplaceIntegrand, ht]
    have hzero' : suzukiUpperFourierLaplaceJetIntegrand A q (k + 1) z t = 0 := by
      simp [suzukiUpperFourierLaplaceJetIntegrand,
        suzukiUpperFourierLaplaceIntegrand, ht]
    have hfun : (fun w : ℂ =>
        suzukiUpperFourierLaplaceJetIntegrand A q k w t) = fun _ => 0 :=
      funext hzero
    rw [hzero', hfun]
    exact hasDerivAt_const z (0 : ℂ)

theorem aestronglyMeasurable_suzukiUpperFourierLaplaceJetIntegrand
    (A : ℝ) (q : SoninL2) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable
      (suzukiUpperFourierLaplaceJetIntegrand A q k z) volume := by
  have hphase : AEStronglyMeasurable
      (fun t : ℝ => (Iic A).indicator
        (fun t : ℝ => (-I * (t : ℂ)) ^ k *
          Complex.exp (-I * z * (t : ℂ))) t) volume :=
    ((by fun_prop : Continuous fun t : ℝ =>
      (-I * (t : ℂ)) ^ k * Complex.exp (-I * z * (t : ℂ)))
      |>.aestronglyMeasurable.indicator measurableSet_Iic)
  apply (hphase.mul (Lp.memLp q).1).congr
  filter_upwards with t
  by_cases ht : t ∈ Iic A
  · simp [suzukiUpperFourierLaplaceJetIntegrand,
      suzukiUpperFourierLaplaceIntegrand, ht]
    ring
  · simp [suzukiUpperFourierLaplaceJetIntegrand,
      suzukiUpperFourierLaplaceIntegrand, ht]

theorem norm_suzukiUpperFourierLaplaceJetIntegrand
    (A : ℝ) (q : SoninL2) (k : ℕ) (z : ℂ) (t : ℝ) :
    ‖suzukiUpperFourierLaplaceJetIntegrand A q k z t‖ =
      (Iic A).indicator
        (fun t : ℝ => |t| ^ k * Real.exp (z.im * t) * ‖q t‖) t := by
  by_cases ht : t ∈ Iic A
  · rw [suzukiUpperFourierLaplaceJetIntegrand,
      suzukiUpperFourierLaplaceIntegrand, indicator_of_mem ht,
      indicator_of_mem ht]
    simp only [norm_mul, norm_pow, norm_neg, norm_I, one_mul,
      Complex.norm_exp, norm_real, Real.norm_eq_abs]
    have hre : (-I * z * (t : ℂ)).re = z.im * t := by
      simp [Complex.mul_re]
    rw [hre]
    ring
  · simp [suzukiUpperFourierLaplaceJetIntegrand,
      suzukiUpperFourierLaplaceIntegrand, ht]

theorem norm_suzukiUpperFourierLaplaceJetWeight
    (A : ℝ) (k : ℕ) (b : ℝ) (t : ℝ) :
    ‖suzukiUpperFourierLaplaceJetWeight A k b t‖ =
      (Iic A).indicator
        (fun t : ℝ => |t| ^ k * Real.exp (b * t)) t := by
  by_cases ht : t ∈ Iic A
  · rw [suzukiUpperFourierLaplaceJetWeight, indicator_of_mem ht,
      indicator_of_mem ht, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) k)
        (Real.exp_pos _).le)]
  · simp [suzukiUpperFourierLaplaceJetWeight, ht]

theorem integrable_suzukiUpperFourierLaplaceJetIntegrand
    (A : ℝ) (q : SoninL2) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Integrable (suzukiUpperFourierLaplaceJetIntegrand A q k z) := by
  have hweight := suzukiUpperFourierLaplaceJetWeight_memLp A k hz
  have hprod : Integrable
      (fun t : ℝ => suzukiUpperFourierLaplaceJetWeight A k z.im t * q t) :=
    MemLp.integrable_mul hweight (Lp.memLp q)
  apply hprod.mono
    (aestronglyMeasurable_suzukiUpperFourierLaplaceJetIntegrand A q k z)
  · filter_upwards with t
    by_cases ht : t ∈ Iic A
    · have hre : (-I * z * (t : ℂ)).re = z.im * t := by
        simp [Complex.mul_re]
      rw [suzukiUpperFourierLaplaceJetIntegrand,
        suzukiUpperFourierLaplaceIntegrand,
        suzukiUpperFourierLaplaceJetWeight, indicator_of_mem ht,
        indicator_of_mem ht]
      simp only [norm_mul, norm_pow, norm_neg, norm_I, one_mul,
        Complex.norm_exp, norm_real, Real.norm_eq_abs, hre]
      rw [abs_abs, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc] using
        (le_refl (|t| ^ k * Real.exp (z.im * t) * ‖q t‖))
    · simp [suzukiUpperFourierLaplaceJetIntegrand,
        suzukiUpperFourierLaplaceIntegrand,
        suzukiUpperFourierLaplaceJetWeight, ht]

/-- Every polynomial jet of the upper-supported transform differentiates under the integral on
the strict upper half-plane. -/
theorem hasDerivAt_integral_suzukiUpperFourierLaplaceJet
    (A : ℝ) (q : SoninL2) (k : ℕ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    HasDerivAt
      (fun z : ℂ => ∫ t : ℝ,
        suzukiUpperFourierLaplaceJetIntegrand A q k z t)
      (∫ t : ℝ,
        suzukiUpperFourierLaplaceJetIntegrand A q (k + 1) z₀ t) z₀ := by
  let ε : ℝ := z₀.im / 4
  let c : ℝ := z₀.im - ε
  let C : ℝ := Real.exp (2 * ε * max A 0)
  let bound : ℝ → ℝ := fun t =>
    C * ‖suzukiUpperFourierLaplaceJetWeight A (k + 1) c t * q t‖
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hc : 0 < c := by dsimp [c, ε]; linarith
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hweight := suzukiUpperFourierLaplaceJetWeight_memLp A (k + 1) hc
  have hweightProd : Integrable
      (fun t : ℝ =>
        suzukiUpperFourierLaplaceJetWeight A (k + 1) c t * q t) :=
    MemLp.integrable_mul hweight (Lp.memLp q)
  have hbound : Integrable bound := hweightProd.norm.const_mul C
  have him {z : ℂ} (hz : z ∈ Metric.ball z₀ ε) :
      c ≤ z.im ∧ z.im - c ≤ 2 * ε := by
    have hdist : ‖z - z₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    constructor <;> dsimp [c] <;> linarith [le_abs_self (z.im - z₀.im),
      neg_le_of_abs_le himdiff]
  have hdom : ∀ᵐ t : ℝ, ∀ z ∈ Metric.ball z₀ ε,
      ‖suzukiUpperFourierLaplaceJetIntegrand A q (k + 1) z t‖ ≤
        bound t := by
    filter_upwards with t
    intro z hz
    by_cases ht : t ∈ Iic A
    · have him' := him hz
      have hdeltaNonneg : 0 ≤ z.im - c := sub_nonneg.mpr him'.1
      have hmaxNonneg : 0 ≤ max A 0 := le_max_right A 0
      have htmax : t ≤ max A 0 := ht.trans (le_max_left A 0)
      have hdelta : (z.im - c) * t ≤ 2 * ε * max A 0 := by
        by_cases ht0 : t ≤ 0
        · exact (mul_nonpos_of_nonneg_of_nonpos hdeltaNonneg ht0).trans
            (mul_nonneg (by positivity) hmaxNonneg)
        · have ht0' : 0 ≤ t := (lt_of_not_ge ht0).le
          exact mul_le_mul him'.2 htmax ht0' (by positivity)
      have hexp : Real.exp (z.im * t) ≤ C * Real.exp (c * t) := by
        calc
          Real.exp (z.im * t) =
              Real.exp ((z.im - c) * t) * Real.exp (c * t) := by
            rw [← Real.exp_add]
            congr 1
            ring
          _ ≤ Real.exp (2 * ε * max A 0) * Real.exp (c * t) := by
            gcongr
          _ = C * Real.exp (c * t) := by rfl
      rw [norm_suzukiUpperFourierLaplaceJetIntegrand,
        indicator_of_mem ht]
      change |t| ^ (k + 1) * Real.exp (z.im * t) * ‖q t‖ ≤ _
      rw [show bound t =
          C * (|t| ^ (k + 1) * Real.exp (c * t) * ‖q t‖) by
        dsimp [bound]
        rw [norm_mul, norm_suzukiUpperFourierLaplaceJetWeight,
          indicator_of_mem ht]]
      calc
        |t| ^ (k + 1) * Real.exp (z.im * t) * ‖q t‖ ≤
            |t| ^ (k + 1) * (C * Real.exp (c * t)) * ‖q t‖ := by
          gcongr
        _ = C * (|t| ^ (k + 1) * Real.exp (c * t) * ‖q t‖) := by ring
    · rw [norm_suzukiUpperFourierLaplaceJetIntegrand,
        indicator_of_notMem ht]
      exact mul_nonneg hC (norm_nonneg _)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := suzukiUpperFourierLaplaceJetIntegrand A q k)
    (F' := suzukiUpperFourierLaplaceJetIntegrand A q (k + 1))
    (x₀ := z₀) (s := Metric.ball z₀ ε) (bound := bound)
    (Metric.ball_mem_nhds z₀ hε)
    (Filter.Eventually.of_forall
      (aestronglyMeasurable_suzukiUpperFourierLaplaceJetIntegrand A q k))
    (integrable_suzukiUpperFourierLaplaceJetIntegrand A q k hz₀)
    (integrable_suzukiUpperFourierLaplaceJetIntegrand A q (k + 1) hz₀).1
    hdom hbound
    (by
      filter_upwards with t
      intro z _
      exact hasDerivAt_suzukiUpperFourierLaplaceJetIntegrand A q k z t)
  exact hresult.2

theorem hasDerivAt_suzukiUpperFourierLaplace
    (A : ℝ) (q : SoninL2) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (suzukiUpperFourierLaplace A q)
      (∫ t : ℝ, suzukiUpperFourierLaplaceJetIntegrand A q 1 z t) z := by
  unfold suzukiUpperFourierLaplace
  simpa [suzukiUpperFourierLaplaceJetIntegrand] using
    (hasDerivAt_integral_suzukiUpperFourierLaplaceJet A q 0 hz)

def suzukiUpperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_suzukiUpperHalfPlane : IsOpen suzukiUpperHalfPlane := by
  exact isOpen_lt continuous_const (by fun_prop)

theorem isPreconnected_suzukiUpperHalfPlane :
    IsPreconnected suzukiUpperHalfPlane :=
  (convex_halfSpace_im_gt 0).isPreconnected

theorem analyticOnNhd_suzukiUpperFourierLaplace
    (A : ℝ) (q : SoninL2) :
    AnalyticOnNhd ℂ (suzukiUpperFourierLaplace A q)
      suzukiUpperHalfPlane := by
  have hd : DifferentiableOn ℂ (suzukiUpperFourierLaplace A q)
      suzukiUpperHalfPlane := by
    intro z hz
    exact (hasDerivAt_suzukiUpperFourierLaplace A q hz).differentiableAt
      |>.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_suzukiUpperHalfPlane

/-! ## Lower-supported transform by exact reflection -/

/-- Lower-supported Fourier--Laplace transform.  Reflection converts it exactly to the upper
transform, so its holomorphy includes arbitrary `L²` sources without duplicating an analytic
estimate. -/
def suzukiLowerFourierLaplace (B : ℝ) (q : SoninL2) (z : ℂ) : ℂ :=
  suzukiUpperFourierLaplace (-B) (l2Reflection q) z

/-- The reflected definition is the literal lower-half-line integral used by Suzuki. -/
theorem suzukiLowerFourierLaplace_eq_integral
    (B : ℝ) (q : SoninL2) (z : ℂ) :
    suzukiLowerFourierLaplace B q z =
      ∫ t : ℝ, (Ici B).indicator
        (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * q t) t := by
  unfold suzukiLowerFourierLaplace suzukiUpperFourierLaplace
    suzukiUpperFourierLaplaceIntegrand
  rw [integral_indicator measurableSet_Iic]
  calc
    (∫ t : ℝ in Iic (-B),
        Complex.exp (-I * z * (t : ℂ)) * l2Reflection q t) =
        ∫ t : ℝ in Iic (-B),
          Complex.exp (-I * z * (t : ℂ)) * q (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (l2Reflection_ae q)] with t ht
      rw [ht]
    _ = ∫ t : ℝ in Ioi B,
          Complex.exp (I * z * (t : ℂ)) * q t := by
      calc
        (∫ t : ℝ in Iic (-B),
            Complex.exp (-I * z * (t : ℂ)) * q (-t)) =
            ∫ t : ℝ in Iic (-B),
              (fun s : ℝ => Complex.exp (I * z * (s : ℂ)) * q s) (-t) := by
          apply setIntegral_congr_fun measurableSet_Iic
          intro t _
          dsimp only
          rw [show -I * z * (t : ℂ) = I * z * ((-t : ℝ) : ℂ) by
            push_cast
            ring]
        _ = ∫ t : ℝ in Ioi (-(-B)),
              Complex.exp (I * z * (t : ℂ)) * q t :=
          integral_comp_neg_Iic (-B)
            (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * q t)
        _ = ∫ t : ℝ in Ioi B,
              Complex.exp (I * z * (t : ℂ)) * q t := by rw [neg_neg]
    _ = ∫ t : ℝ in Ici B,
          Complex.exp (I * z * (t : ℂ)) * q t := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = ∫ t : ℝ, (Ici B).indicator
          (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * q t) t := by
      rw [integral_indicator measurableSet_Ici]

theorem suzukiLowerFourierLaplace_eq_CLM
    (B : ℝ) (q : SoninL2) (z : ℂ) (hz : 0 < z.im) :
    suzukiLowerFourierLaplace B q z =
      suzukiLowerFourierLaplaceCLM B z hz q := by
  rw [suzukiLowerFourierLaplace_eq_integral,
    suzukiLowerFourierLaplaceCLM_eq_integral]

theorem analyticOnNhd_suzukiLowerFourierLaplace
    (B : ℝ) (q : SoninL2) :
    AnalyticOnNhd ℂ (suzukiLowerFourierLaplace B q)
      suzukiUpperHalfPlane := by
  exact analyticOnNhd_suzukiUpperFourierLaplace (-B) (l2Reflection q)

theorem suzukiUpperFourierLaplace_eq_CLM
    (A : ℝ) (q : SoninL2) (z : ℂ) (hz : 0 < z.im) :
    suzukiUpperFourierLaplace A q z =
      suzukiUpperFourierLaplaceCLM A z hz q := by
  rw [suzukiUpperFourierLaplace,
    suzukiUpperFourierLaplaceCLM_eq_integral]
  rfl

end RHTower
