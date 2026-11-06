import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Szegő's infimum in the form of Helson and Lowdenslager

For a probability space, a weight `W > 0` with `W, log W ∈ L¹` and a family `𝒜` of mean-zero real
functions dense among bounded mean-zero functions,

`exp ∫ log W = inf_{g ∈ 𝒜} ∫ W e^g` (`isGLB_integral_mul_exp`).

The inequality `≤` is Jensen's. For `≥` the exact outer function is replaced by truncations of
`−log W`; each truncation is approximated in `𝒜` by bounded convergence. No boundary limit of an
outer function enters.

On the circle `𝒜` is `{2 Re Q(z) : Q polynomial, Q(0) = 0}` (`isSzegoDense_circleFamily`), because
`|e^{Q(z)}|² = e^{2 Re Q(z)}`: the near-extremal outer functions are exponentials of polynomials.
So for a weight on the circle (`isGLB_circle`)

`exp (mean of log W) = inf_Q mean of W |e^{Q}|²`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-! ### The abstract infimum -/

section Abstract

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A family of real functions is **Szegő dense** if its members are bounded, measurable and of
mean zero, and each bounded measurable mean-zero function is a bounded almost everywhere limit of
members. -/
structure IsSzegoDense (𝒜 : Set (X → ℝ)) : Prop where
  bdd : ∀ g ∈ 𝒜, ∃ C : ℝ, ∀ x, |g x| ≤ C
  meas : ∀ g ∈ 𝒜, Measurable g
  mean : ∀ g ∈ 𝒜, ∫ x, g x ∂μ = 0
  approx : ∀ f : X → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) → ∫ x, f x ∂μ = 0 →
    ∃ g : ℕ → X → ℝ, (∀ n, g n ∈ 𝒜) ∧ (∃ C : ℝ, ∀ n x, |g n x| ≤ C) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x))

variable {μ} [IsProbabilityMeasure μ] {W : X → ℝ}

/-- Jensen's inequality in exponential form on a probability space. -/
theorem exp_integral_le_integral_exp {φ : X → ℝ} (hφ : Integrable φ μ)
    (hexp : Integrable (fun x => Real.exp (φ x)) μ) :
    Real.exp (∫ x, φ x ∂μ) ≤ ∫ x, Real.exp (φ x) ∂μ :=
  convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hφ hexp

/-- The lower bound: `exp ∫ log W ≤ ∫ W e^g` for every bounded measurable mean-zero `g`. -/
theorem exp_integral_log_le {g : X → ℝ} (hpos : ∀ᵐ x ∂μ, 0 < W x)
    (hint : Integrable W μ) (hlog : Integrable (fun x => Real.log (W x)) μ) (hg : Measurable g)
    (hbdd : ∃ C : ℝ, ∀ x, |g x| ≤ C) (hmean : ∫ x, g x ∂μ = 0) :
    Real.exp (∫ x, Real.log (W x) ∂μ) ≤ ∫ x, W x * Real.exp (g x) ∂μ := by
  obtain ⟨C, hC⟩ := hbdd
  have hgi : Integrable g μ :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hprod : Integrable (fun x => W x * Real.exp (g x)) μ := by
    refine hint.mul_bdd (c := Real.exp C) ?_ (Eventually.of_forall fun x => ?_)
    · exact (Real.measurable_exp.comp hg).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hC x))
  have hphi : Integrable (fun x => Real.log (W x) + g x) μ := hlog.add hgi
  have hae : (fun x => Real.exp (Real.log (W x) + g x)) =ᵐ[μ] fun x => W x * Real.exp (g x) := by
    filter_upwards [hpos] with x hx
    rw [Real.exp_add, Real.exp_log hx]
  have hJ := exp_integral_le_integral_exp hphi (hprod.congr hae.symm)
  rw [integral_add hlog hgi, hmean, add_zero, integral_congr_ae hae] at hJ
  exact hJ

/-- Truncation to `[−k, k]`. -/
def clip (k : ℝ) (y : ℝ) : ℝ := max (-k) (min k y)

theorem abs_clip_le {k : ℝ} (hk : 0 ≤ k) (y : ℝ) : |clip k y| ≤ k := by
  unfold clip
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem measurable_clip (k : ℝ) : Measurable (clip k) := by
  unfold clip
  fun_prop

theorem abs_clip_le_abs {k : ℝ} (hk : 0 ≤ k) (y : ℝ) : |clip k y| ≤ |y| := by
  unfold clip
  rw [abs_le]
  constructor
  · refine le_max_of_le_right (le_min ?_ (neg_abs_le y))
    linarith [abs_nonneg y, le_abs_self y, neg_abs_le y, hk]
  · refine max_le ?_ ((min_le_right _ _).trans (le_abs_self y))
    linarith [abs_nonneg y, hk]

theorem tendsto_clip (y : ℝ) : Tendsto (fun n : ℕ => clip n y) atTop (𝓝 y) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨n, hn⟩ := exists_nat_ge |y|
  filter_upwards [eventually_ge_atTop n] with m hm
  have h : |y| ≤ (m : ℝ) := hn.trans (by exact_mod_cast hm)
  have h1 := abs_le.mp h
  unfold clip
  rw [min_eq_right h1.2, max_eq_right h1.1]

/-- `W e^{−clip_k log W} ≤ 1 + W e^{−k}`: the truncated weight is `1` on the bulk, below `1` where
`W` is small, and `W e^{−k}` where `W` is large. -/
theorem mul_exp_neg_clip_le {k y : ℝ} (hk : 0 ≤ k) (hy : 0 < y) :
    y * Real.exp (-clip k (Real.log y)) ≤ 1 + y * Real.exp (-k) := by
  have hexp := Real.exp_pos (-k)
  have hyexp := mul_pos hy hexp
  unfold clip
  rcases le_total k (Real.log y) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    linarith
  · rw [min_eq_right h]
    rcases le_total (-k) (Real.log y) with h' | h'
    · rw [max_eq_right h', Real.exp_neg, Real.exp_log hy, mul_inv_cancel₀ hy.ne']
      linarith
    · rw [max_eq_left h', neg_neg]
      have h2 : y ≤ Real.exp (-k) := by
        rw [← Real.exp_log hy]; exact Real.exp_le_exp.mpr h'
      have h3 : y * Real.exp k ≤ Real.exp (-k) * Real.exp k :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h3
      linarith

/-- The upper bound: the infimum of `∫ W e^g` over bounded measurable mean-zero `g` reaches
`exp ∫ log W`. -/
theorem exists_mean_zero_integral_lt (hW : Measurable W) (hpos : ∀ᵐ x ∂μ, 0 < W x)
    (hint : Integrable W μ) (hlog : Integrable (fun x => Real.log (W x)) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → ℝ, Measurable f ∧ (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧ ∫ x, f x ∂μ = 0 ∧
      ∫ x, W x * Real.exp (f x) ∂μ < Real.exp (∫ x, Real.log (W x) ∂μ) + ε := by
  set L : X → ℝ := fun x => Real.log (W x) with hL
  have hLm : Measurable L := Real.measurable_log.comp hW
  set m : ℕ → ℝ := fun n => ∫ x, clip n (L x) ∂μ with hm
  have hclipi : ∀ n : ℕ, Integrable (fun x => clip n (L x)) μ := fun n =>
    Integrable.of_bound ((measurable_clip _).comp hLm).aestronglyMeasurable n
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_clip_le (Nat.cast_nonneg n) _)
  have hmlim : Tendsto m atTop (𝓝 (∫ x, L x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |L x|)
      (fun n => (hclipi n).aestronglyMeasurable) hlog.abs (fun n => ?_)
      (Eventually.of_forall fun x => tendsto_clip _)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_clip_le_abs (Nat.cast_nonneg n) _
  -- the integral of the truncated weight tends to at most one
  have hbound : ∀ n : ℕ, ∫ x, W x * Real.exp (-clip n (L x)) ∂μ ≤
      1 + (∫ x, W x ∂μ) * Real.exp (-(n : ℝ)) := by
    intro n
    have hi : Integrable (fun x => W x * Real.exp (-clip n (L x))) μ := by
      refine hint.mul_bdd (c := Real.exp n) ?_ (Eventually.of_forall fun x => ?_)
      · exact (Real.measurable_exp.comp ((measurable_clip _).comp hLm).neg).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have := abs_le.mp (abs_clip_le (k := n) (Nat.cast_nonneg n) (L x))
        linarith [this.1]
    have hr : Integrable (fun x => 1 + W x * Real.exp (-(n : ℝ))) μ :=
      (integrable_const _).add (hint.mul_const _)
    calc ∫ x, W x * Real.exp (-clip n (L x)) ∂μ ≤ ∫ x, (1 + W x * Real.exp (-(n : ℝ))) ∂μ := by
          refine integral_mono_ae hi hr ?_
          filter_upwards [hpos] with x hx
          exact mul_exp_neg_clip_le (Nat.cast_nonneg n) hx
      _ = 1 + (∫ x, W x ∂μ) * Real.exp (-(n : ℝ)) := by
          rw [integral_add (integrable_const _) (hint.mul_const _), integral_const,
            integral_mul_const]
          simp
  have hval : Tendsto (fun n : ℕ => Real.exp (m n) * (1 + (∫ x, W x ∂μ) * Real.exp (-(n : ℝ))))
      atTop (𝓝 (Real.exp (∫ x, L x ∂μ) * (1 + (∫ x, W x ∂μ) * 0))) := by
    refine (Real.continuous_exp.tendsto _ |>.comp hmlim).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul ?_))
    have : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    exact Real.tendsto_exp_atBot.comp this
  rw [mul_zero, add_zero, mul_one] at hval
  obtain ⟨n, hn⟩ := (hval.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))).exists
  refine ⟨fun x => m n - clip n (L x), (measurable_const.sub ((measurable_clip _).comp hLm)),
    ⟨|m n| + n, fun x => ?_⟩, ?_, ?_⟩
  · refine (abs_sub _ _).trans ?_
    exact add_le_add le_rfl (abs_clip_le (Nat.cast_nonneg n) _)
  · rw [integral_sub (integrable_const _) (hclipi n), integral_const]
    simp [hm]
  · have he : (fun x => W x * Real.exp (m n - clip n (L x))) =
        fun x => Real.exp (m n) * (W x * Real.exp (-clip n (L x))) := by
      funext x
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    rw [he, integral_const_mul]
    refine lt_of_le_of_lt ?_ hn
    exact mul_le_mul_of_nonneg_left (hbound n) (Real.exp_pos _).le

/-- **Szegő's infimum.** Over a Szegő dense family, `exp ∫ log W` is the greatest lower bound of the
integrals `∫ W e^g`. -/
theorem isGLB_integral_mul_exp {𝒜 : Set (X → ℝ)} (h𝒜 : IsSzegoDense μ 𝒜) (hW : Measurable W)
    (hpos : ∀ᵐ x ∂μ, 0 < W x) (hint : Integrable W μ)
    (hlog : Integrable (fun x => Real.log (W x)) μ) :
    IsGLB ((fun g : X → ℝ => ∫ x, W x * Real.exp (g x) ∂μ) '' 𝒜)
      (Real.exp (∫ x, Real.log (W x) ∂μ)) := by
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    exact exp_integral_log_le hpos hint hlog (h𝒜.meas g hg) (h𝒜.bdd g hg) (h𝒜.mean g hg)
  · intro b hb
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨f, hfm, hfb, hfmean, hf⟩ := exists_mean_zero_integral_lt hW hpos hint hlog hε
    obtain ⟨g, hg𝒜, ⟨C, hC⟩, hlim⟩ := h𝒜.approx f hfm hfb hfmean
    have hconv : Tendsto (fun n => ∫ x, W x * Real.exp (g n x) ∂μ) atTop
        (𝓝 (∫ x, W x * Real.exp (f x) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => |W x| * Real.exp C)
        (fun n => ?_) (hint.abs.mul_const _) (fun n => Eventually.of_forall fun x => ?_) ?_
      · exact (hW.mul (Real.measurable_exp.comp (h𝒜.meas _ (hg𝒜 n)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ((le_abs_self _).trans (hC n x))) (abs_nonneg _)
      · filter_upwards [hlim] with x hx
        exact (Real.continuous_exp.tendsto _ |>.comp hx).const_mul _
    have hb' : b ≤ ∫ x, W x * Real.exp (f x) ∂μ :=
      ge_of_tendsto' hconv fun n => hb ⟨g n, hg𝒜 n, rfl⟩
    linarith

end Abstract

/-! ### The circle -/

section Circle

open AddCircle

instance instFactTwoPi : Fact (0 < 2 * π) := ⟨by positivity⟩

local notation "𝕋" => AddCircle (2 * π)

/-- The boundary coordinate `z = e^{ix}` of the circle. -/
def circleZ (x : 𝕋) : ℂ := fourier 1 x

theorem continuous_circleZ : Continuous circleZ := (fourier (T := 2 * π) 1).continuous

theorem norm_circleZ (x : 𝕋) : ‖circleZ x‖ = 1 := by
  simp [circleZ, fourier_apply]

theorem fourier_natCast_eq (k : ℕ) (x : 𝕋) : fourier (k : ℤ) x = circleZ x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this, fourier_add, ih, pow_succ, circleZ]

/-- The nonconstant characters have mean zero. -/
theorem integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x : 𝕋, fourier n x ∂haarAddCircle = 0 :=
  integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
    (fourier_add_half_inv_index hn (Fact.out))

theorem integral_circleZ_pow {k : ℕ} (hk : k ≠ 0) :
    ∫ x : 𝕋, circleZ x ^ k ∂haarAddCircle = 0 := by
  have h := integral_fourier_eq_zero (n := (k : ℤ)) (by exact_mod_cast hk)
  simpa only [fourier_natCast_eq] using h

theorem continuous_eval_circleZ (Q : Polynomial ℂ) :
    Continuous fun x : 𝕋 => Q.eval (circleZ x) :=
  Q.continuous.comp continuous_circleZ

/-- A polynomial without constant term has mean zero on the circle. -/
theorem integral_eval_circleZ {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    ∫ x : 𝕋, Q.eval (circleZ x) ∂haarAddCircle = 0 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [integral_const_mul]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [Polynomial.mem_support_iff] at hi
      exact absurd hQ hi
    · rw [integral_circleZ_pow hi0, mul_zero]
  · intro i _
    exact ((continuous_const.mul (continuous_circleZ.pow i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The real exponent `2 Re Q(z)`. -/
def circleValue (Q : Polynomial ℂ) (x : 𝕋) : ℝ := 2 * (Q.eval (circleZ x)).re

theorem continuous_circleValue (Q : Polynomial ℂ) : Continuous (circleValue Q) :=
  continuous_const.mul (Complex.continuous_re.comp (continuous_eval_circleZ Q))

theorem integral_circleValue {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    ∫ x : 𝕋, circleValue Q x ∂haarAddCircle = 0 := by
  have hi : Integrable (fun x : 𝕋 => Q.eval (circleZ x)) haarAddCircle :=
    (continuous_eval_circleZ Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [circleValue]
  rw [integral_const_mul]
  have h := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_eval_circleZ hQ]
  simp

/-- The exponents of the near-extremal mollifiers. -/
def circleFamily : Set (𝕋 → ℝ) := circleValue '' {Q | Q.coeff 0 = 0}

/-- The real part of an element of the Fourier span is a constant plus `Re P(z)`. -/
theorem exists_re_eq_of_mem_span {T : C(𝕋, ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * π)))) :
    ∀ c : ℂ, ∃ (a : ℝ) (P : Polynomial ℂ), P.coeff 0 = 0 ∧
      ∀ x : 𝕋, (c * T x).re = a + (P.eval (circleZ x)).re := by
  induction hT using Submodule.span_induction with
  | mem T hmem =>
    obtain ⟨n, rfl⟩ := hmem
    intro c
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · rcases eq_or_ne k 0 with rfl | hk
      · exact ⟨c.re, 0, by simp, fun x => by simp⟩
      · refine ⟨0, Polynomial.C c * Polynomial.X ^ k, ?_, fun x => ?_⟩
        · simp [Polynomial.coeff_X_pow, hk.symm]
        · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
            Polynomial.eval_X, zero_add]
          rw [fourier_natCast_eq]
    · rcases eq_or_ne k 0 with rfl | hk
      · exact ⟨c.re, 0, by simp, fun x => by simp⟩
      · refine ⟨0, Polynomial.C ((starRingEnd ℂ) c) * Polynomial.X ^ k, ?_, fun x => ?_⟩
        · simp [Polynomial.coeff_X_pow, hk.symm]
        · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
            Polynomial.eval_X, zero_add]
          rw [fourier_neg, fourier_natCast_eq]
          have e : (starRingEnd ℂ) c * circleZ x ^ k =
              (starRingEnd ℂ) (c * (starRingEnd ℂ) (circleZ x ^ k)) := by simp
          rw [e, Complex.conj_re]
  | zero =>
    intro c
    exact ⟨0, 0, by simp, fun x => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro c
    obtain ⟨a₁, P₁, hP₁, h₁⟩ := h₁ c
    obtain ⟨a₂, P₂, hP₂, h₂⟩ := h₂ c
    refine ⟨a₁ + a₂, P₁ + P₂, by simp [hP₁, hP₂], fun x => ?_⟩
    have := h₁ x
    have := h₂ x
    simp only [ContinuousMap.add_apply, mul_add, Complex.add_re, Polynomial.eval_add]
    linarith
  | smul d T _ h =>
    intro c
    obtain ⟨a, P, hP, hx⟩ := h (c * d)
    refine ⟨a, P, hP, fun x => ?_⟩
    rw [← hx x]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring_nf

theorem abs_sub_clip_le {k u y : ℝ} (hu : |u| ≤ k) : |u - clip k y| ≤ |u - y| := by
  have h := abs_le.mp hu
  have hk : 0 ≤ k := (abs_nonneg u).trans hu
  unfold clip
  rcases le_total k y with hy | hy
  · rw [min_eq_left hy, max_eq_right (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right hy]
    rcases le_total (-k) y with hy' | hy'
    · rw [max_eq_right hy']
    · rw [max_eq_left hy', abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- **Density on the circle.** Every bounded measurable function of mean zero is a uniformly bounded
almost everywhere limit of exponents `2 Re Q(z)`. -/
theorem isSzegoDense_circleFamily : IsSzegoDense (haarAddCircle (T := 2 * π)) circleFamily := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨Q, -, rfl⟩
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_circleValue Q).continuousOn
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x (mem_univ _)⟩
  · rintro _ ⟨Q, -, rfl⟩
    exact (continuous_circleValue Q).measurable
  · rintro _ ⟨Q, hQ, rfl⟩
    exact integral_circleValue hQ
  intro f hfm ⟨M, hM⟩ hf0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfL : MemLp f 1 (haarAddCircle (T := 2 * π)) :=
    MemLp.of_bound hfm.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  -- one approximation step
  have hstep : ∀ n : ℕ, ∃ (a : ℝ) (P : Polynomial ℂ), P.coeff 0 = 0 ∧
      (∀ x : 𝕋, |a + (P.eval (circleZ x)).re| ≤ M + 1) ∧
      eLpNorm (fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - f x) 1 haarAddCircle ≤
        ENNReal.ofReal (2 / (n + 1)) := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨h, hh, -⟩ := hfL.exists_boundedContinuous_eLpNorm_sub_le (by simp)
      (ε := ENNReal.ofReal (1 / (n + 1))) (by simpa using hn)
    have hkc : Continuous fun x : 𝕋 => clip M (h x) := by
      unfold clip
      fun_prop
    let K : C(𝕋, ℂ) := ⟨fun x => (clip M (h x) : ℂ), Complex.continuous_ofReal.comp hkc⟩
    have hK : K ∈ (Submodule.span ℂ (Set.range (fourier (T := 2 * π)))).topologicalClosure := by
      rw [span_fourier_closure_eq_top]
      trivial
    obtain ⟨T, hT, hd⟩ := Metric.mem_closure_iff.mp hK _ hn
    obtain ⟨a, P, hP, hre⟩ := exists_re_eq_of_mem_span hT 1
    have hclose : ∀ x : 𝕋, |clip M (h x) - (a + (P.eval (circleZ x)).re)| ≤ 1 / (n + 1) := by
      intro x
      have h1 := ContinuousMap.dist_apply_le_dist (f := K) (g := T) x
      have h2 : |clip M (h x) - (a + (P.eval (circleZ x)).re)| ≤ dist (K x) (T x) := by
        rw [← hre x, one_mul, Complex.dist_eq]
        have := Complex.abs_re_le_norm (K x - T x)
        simpa [K] using this
      exact h2.trans (h1.trans hd.le)
    refine ⟨a, P, hP, fun x => ?_, ?_⟩
    · have h1 := abs_clip_le hM0 (h x)
      have h2 := hclose x
      have h3 : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h4 := abs_sub_abs_le_abs_sub (a + (P.eval (circleZ x)).re) (clip M (h x))
      rw [abs_sub_comm] at h4
      linarith
    · have hbound1 : eLpNorm (fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - clip M (h x)) 1
          haarAddCircle ≤ ENNReal.ofReal (1 / (n + 1)) := by
        have := eLpNorm_le_of_ae_bound (μ := haarAddCircle) (p := 1)
          (f := fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - clip M (h x)) (C := 1 / (n + 1))
          (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs, abs_sub_comm]; exact hclose x)
        simpa using this
      have hbound2 : eLpNorm (fun x : 𝕋 => clip M (h x) - f x) 1 haarAddCircle ≤
          ENNReal.ofReal (1 / (n + 1)) := by
        refine le_trans (eLpNorm_mono fun x => ?_) hh
        simp only [Real.norm_eq_abs, Pi.sub_apply]
        rw [abs_sub_comm]
        exact abs_sub_clip_le (hM x)
      have hsum : (fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - f x) =
          (fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - clip M (h x)) +
            fun x : 𝕋 => clip M (h x) - f x := by
        funext x
        simp
      rw [hsum]
      have hc1 : AEStronglyMeasurable
          (fun x : 𝕋 => (a + (P.eval (circleZ x)).re) - clip M (h x)) haarAddCircle :=
        (((continuous_const.add (Complex.continuous_re.comp
          (continuous_eval_circleZ P))).sub hkc).measurable).aestronglyMeasurable
      have hc2 : AEStronglyMeasurable (fun x : 𝕋 => clip M (h x) - f x) haarAddCircle :=
        (hkc.measurable.sub hfm).aestronglyMeasurable
      refine (eLpNorm_add_le hc1 hc2 le_rfl).trans ?_
      calc _ ≤ ENNReal.ofReal (1 / (n + 1)) + ENNReal.ofReal (1 / (n + 1)) :=
            add_le_add hbound1 hbound2
        _ = ENNReal.ofReal (2 / (n + 1)) := by
            rw [← ENNReal.ofReal_add hn.le hn.le]
            congr 1
            ring
  choose a P hP hb hlim using hstep
  set S : ℕ → 𝕋 → ℝ := fun n x => a n + ((P n).eval (circleZ x)).re with hS
  have hSc : ∀ n, Continuous (S n) := fun n =>
    continuous_const.add (Complex.continuous_re.comp (continuous_eval_circleZ (P n)))
  have hzero : Tendsto (fun n : ℕ => eLpNorm (S n - f) 1 (haarAddCircle (T := 2 * π)))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (g := fun _ => 0) (h := fun n : ℕ => ENNReal.ofReal (2 / (n + 1))) ?_
      (fun _ => zero_le) hlim
    have : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ) |>.comp (tendsto_add_atTop_nat 1)
        |>.congr fun n => by simp
    simpa using ENNReal.tendsto_ofReal this
  have hinm := tendstoInMeasure_of_tendsto_eLpNorm (one_ne_zero)
    (fun n => (hSc n).aestronglyMeasurable) hfm.aestronglyMeasurable hzero
  obtain ⟨ns, -, hae⟩ := hinm.exists_seq_tendsto_ae
  have hmean : ∀ n, ∫ x : 𝕋, S n x ∂haarAddCircle = a n := by
    intro n
    have hi : Integrable (fun x : 𝕋 => ((P n).eval (circleZ x)).re) haarAddCircle :=
      (Complex.continuous_re.comp (continuous_eval_circleZ (P n))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun x : 𝕋 => (P n).eval (circleZ x)) haarAddCircle :=
      (continuous_eval_circleZ (P n)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hh := Complex.reCLM.integral_comp_comm hi2
    simp only [Complex.reCLM_apply] at hh
    simp only [hS]
    rw [integral_add (integrable_const _) hi, integral_const, hh, integral_eval_circleZ (hP n)]
    simp
  have hab : ∀ n, |a n| ≤ M + 1 := by
    intro n
    rw [← hmean n, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := M + 1)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb n x)).trans ?_
    simp
  have halim : Tendsto (fun i => a (ns i)) atTop (𝓝 0) := by
    have hconv : Tendsto (fun i => ∫ x : 𝕋, S (ns i) x ∂haarAddCircle) atTop
        (𝓝 (∫ x : 𝕋, f x ∂haarAddCircle)) :=
      tendsto_integral_of_dominated_convergence (fun _ => M + 1)
        (fun i => (hSc (ns i)).aestronglyMeasurable) (integrable_const _)
        (fun i => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb (ns i) x) hae
    simpa only [hmean, hf0] using hconv
  refine ⟨fun i => circleValue (Polynomial.C (1 / 2) * P (ns i)), fun i => ?_,
    ⟨2 * (M + 1), fun i x => ?_⟩, ?_⟩
  · exact ⟨_, by simp [hP], rfl⟩
  · have e : circleValue (Polynomial.C (1 / 2) * P (ns i)) x = S (ns i) x - a (ns i) := by
      simp [circleValue, hS, Complex.mul_re]
    change |circleValue (Polynomial.C (1 / 2) * P (ns i)) x| ≤ _
    rw [e]
    have h1 := hb (ns i) x
    have h2 := hab (ns i)
    calc |S (ns i) x - a (ns i)| ≤ |S (ns i) x| + |a (ns i)| := abs_sub _ _
      _ ≤ 2 * (M + 1) := by
          have : |S (ns i) x| ≤ M + 1 := h1
          linarith
  · filter_upwards [hae] with x hx
    have e : ∀ i, circleValue (Polynomial.C (1 / 2) * P (ns i)) x = S (ns i) x - a (ns i) := by
      intro i
      simp [circleValue, hS, Complex.mul_re]
    simp only [e]
    simpa using hx.sub halim

theorem norm_exp_sq (w : ℂ) : ‖Complex.exp w‖ ^ 2 = Real.exp (2 * w.re) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  norm_num

/-- **Szegő's infimum on the circle.** The geometric mean of a weight is the infimum over
polynomials `Q`, `Q(0) = 0`, of the weighted second moments of `e^{Q(z)}`. -/
theorem isGLB_circle {W : 𝕋 → ℝ} (hW : Measurable W) (hpos : ∀ᵐ x ∂haarAddCircle, 0 < W x)
    (hint : Integrable W haarAddCircle)
    (hlog : Integrable (fun x => Real.log (W x)) haarAddCircle) :
    IsGLB ((fun Q : Polynomial ℂ => ∫ x, W x * ‖Complex.exp (Q.eval (circleZ x))‖ ^ 2 ∂haarAddCircle) ''
        {Q | Q.coeff 0 = 0})
      (Real.exp (∫ x, Real.log (W x) ∂haarAddCircle)) := by
  have h := isGLB_integral_mul_exp isSzegoDense_circleFamily hW hpos hint hlog
  rw [circleFamily, Set.image_image] at h
  simpa only [circleValue, norm_exp_sq] using h

/-- The mean over the circle is the circle average. -/
theorem integral_haar_circleZ (G : ℂ → ℝ) :
    ∫ x : 𝕋, G (circleZ x) ∂haarAddCircle = Real.circleAverage G 0 1 := by
  rw [Real.circleAverage_def, integral_haarAddCircle]
  have h := AddCircle.intervalIntegral_preimage (T := 2 * π) 0 (fun x : 𝕋 => G (circleZ x))
  rw [zero_add] at h
  rw [← h]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have : circleZ (θ : 𝕋) = circleMap 0 1 θ := by
    rw [circleZ, fourier_coe_apply, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  simp only [this]

/-- Integrability over the circle is circle integrability. -/
theorem integrable_haar_circleZ_iff {G : ℂ → ℝ} (hG : Measurable G) :
    Integrable (fun x : 𝕋 => G (circleZ x)) haarAddCircle ↔ CircleIntegrable G 0 1 := by
  have hmp := AddCircle.measurePreserving_mk (2 * π) 0
  rw [zero_add] at hmp
  have hsm : AEStronglyMeasurable (fun x : 𝕋 => G (circleZ x)) volume :=
    (hG.comp continuous_circleZ.measurable).aestronglyMeasurable
  have h1 : Integrable (fun x : 𝕋 => G (circleZ x)) haarAddCircle ↔
      Integrable (fun x : 𝕋 => G (circleZ x)) volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    rw [integrable_smul_measure (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top]
  have h2 := hmp.integrable_comp hsm
  rw [h1, ← h2, CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity),
    IntegrableOn]
  refine integrable_congr (Eventually.of_forall fun θ => ?_)
  have : circleZ (θ : 𝕋) = circleMap 0 1 θ := by
    rw [circleZ, fourier_coe_apply, circleMap]
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  simp only [Function.comp, this]

/-- **Szegő's infimum in circle averages.** -/
theorem isGLB_circleAverage {G : ℂ → ℝ} (hG : Measurable G)
    (hpos : ∀ᵐ x : 𝕋 ∂haarAddCircle, 0 < G (circleZ x))
    (hint : CircleIntegrable G 0 1) (hlog : CircleIntegrable (fun z => Real.log (G z)) 0 1) :
    IsGLB ((fun Q : Polynomial ℂ =>
        Real.circleAverage (fun z => G z * ‖Complex.exp (Q.eval z)‖ ^ 2) 0 1) '' {Q | Q.coeff 0 = 0})
      (Real.exp (Real.circleAverage (fun z => Real.log (G z)) 0 1)) := by
  have h := isGLB_circle (W := fun x => G (circleZ x)) (hG.comp continuous_circleZ.measurable) hpos
    ((integrable_haar_circleZ_iff hG).mpr hint)
    ((integrable_haar_circleZ_iff (Real.measurable_log.comp hG)).mpr hlog)
  have e : (fun Q : Polynomial ℂ =>
      ∫ x : 𝕋, G (circleZ x) * ‖Complex.exp (Q.eval (circleZ x))‖ ^ 2 ∂haarAddCircle) =
      fun Q => Real.circleAverage (fun z => G z * ‖Complex.exp (Q.eval z)‖ ^ 2) 0 1 := by
    funext Q
    exact integral_haar_circleZ (fun z => G z * ‖Complex.exp (Q.eval z)‖ ^ 2)
  rw [e, integral_haar_circleZ (fun z => Real.log (G z))] at h
  exact h

/-- Points of the circle are null sets. -/
instance instNullSingletonHaar : NullSingletonClass (haarAddCircle (T := 2 * π)) where
  measure_singleton x := by
    have h0 : (volume : Measure 𝕋) {x} = 0 := by
      have h := AddCircle.volume_closedBall (T := 2 * π) (x := x) 0
      rw [Metric.closedBall_zero, mul_zero, min_eq_right (by positivity), ENNReal.ofReal_zero] at h
      exact h
    rw [volume_eq_smul_haarAddCircle] at h0
    simp only [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h0
    exact h0.resolve_left (by simp [Real.pi_pos])

/-- A countable set of the plane is a null set of the circle. -/
theorem ae_circleZ_notMem_of_countable {A : Set ℂ} (hA : A.Countable) :
    ∀ᵐ x : 𝕋 ∂haarAddCircle, circleZ x ∉ A := by
  have hinj : Function.Injective circleZ := by
    intro x y hxy
    have h1 : (toCircle x : Circle) = toCircle y := by
      apply Circle.ext
      simpa [circleZ, fourier_one] using hxy
    exact injective_toCircle (by positivity : (2 * π : ℝ) ≠ 0) h1
  have hc : (circleZ ⁻¹' A).Countable := hA.preimage hinj
  exact measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero _)

end Circle

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
