import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Notation

/-!
# The phase-survival profile of the cubic wall

The squared-frequency response

`F(q) = 6 ∫₀¹ v²(1 - v²)²/(1 + q v²) dv`

and the profile `C(τ) = F(τ²)` satisfy:

* `C > 0`, `C(-τ) = C(τ)`, `C(0) = 16/35`;
* `C` is strictly decreasing in `|τ|`, `C(τ) → 0` and `τ² C(τ) → 16/5` as `|τ| → ∞`;
* `F(q) = 3 ∫₀¹ λ^{1/2}(1 - λ)²/(1 + qλ) dλ`, so `C(√q)/(16/35) = E[1/(1 + qΛ)]` for `Λ` with the
  `Beta(3/2, 3)` law of density `(105/16) λ^{1/2}(1 - λ)²`;
* `F` is strictly completely monotone:
  `(-1)ⁿ F⁽ⁿ⁾(q) = 6 n! ∫₀¹ v^{2n+2}(1 - v²)²/(1 + qv²)^{n+1} dv > 0` and
  `(-1)ⁿ F⁽ⁿ⁾(0) = 48 n!/((2n+3)(2n+5)(2n+7))`.

With the Cayley contrast `δ = (x - y)/(x + y)` and coherence `g = 2√(xy)/(x + y)` one has
`δ² + g² = 1`, `κ(x, y) = 8(xy)^{3/2}/(x + y)³ = g³` and `δ² = tanh²((log x - log y)/2)`.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The response moments -/

/-- `G_n(q) = ∫₀¹ v^{2n+2}(1 - v²)²/(1 + qv²)^{n+1} dv`. -/
def phaseResponseMoment (n : ℕ) (q : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1)

/-- The squared-frequency response `F(q) = 6 ∫₀¹ v²(1 - v²)²/(1 + qv²) dv`. -/
def phaseResponse (q : ℝ) : ℝ := 6 * ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2)

/-- The phase-survival profile `C(τ) = F(τ²)`. -/
def phaseSurvivalProfile (τ : ℝ) : ℝ := phaseResponse (τ ^ 2)

theorem phaseResponse_eq_moment (q : ℝ) : phaseResponse q = 6 * phaseResponseMoment 0 q := by
  simp only [phaseResponse, phaseResponseMoment, mul_zero, zero_add, pow_one]

theorem half_le_phaseDenom {q v : ℝ} (hq : -1 / 2 ≤ q) (hv : v ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ 1 + q * v ^ 2 := by
  have h1 : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have h0 : 0 ≤ v ^ 2 := sq_nonneg v
  rcases le_total 0 q with hq0 | hq0
  · nlinarith
  · nlinarith

theorem phaseDenom_pos {q v : ℝ} (hq : -1 / 2 ≤ q) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < 1 + q * v ^ 2 :=
  lt_of_lt_of_le (by norm_num) (half_le_phaseDenom hq hv)

theorem continuousOn_phaseMomentIntegrand (n : ℕ) {q : ℝ} (hq : -1 / 2 ≤ q) :
    ContinuousOn (fun v : ℝ => v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1))
      (Icc 0 1) :=
  ((continuousOn_id.pow _).mul ((continuousOn_const.sub (continuousOn_id.pow 2)).pow 2)).div
    ((continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2))).pow _)
    fun _ hv => pow_ne_zero _ (phaseDenom_pos hq hv).ne'

theorem intervalIntegrable_phaseMomentIntegrand (n : ℕ) {q : ℝ} (hq : -1 / 2 ≤ q) :
    IntervalIntegrable
      (fun v : ℝ => v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1)) volume 0 1 :=
  (continuousOn_phaseMomentIntegrand n hq).intervalIntegrable_of_Icc zero_le_one

theorem phaseResponseMoment_pos (n : ℕ) {q : ℝ} (hq : -1 / 2 ≤ q) :
    0 < phaseResponseMoment n q := by
  refine intervalIntegral_pos_of_pos_on (intervalIntegrable_phaseMomentIntegrand n hq)
    (fun v hv => ?_) zero_lt_one
  have hd := phaseDenom_pos hq (Ioo_subset_Icc_self hv)
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  exact div_pos (mul_pos (pow_pos hv.1 _) (pow_pos h1 2)) (pow_pos hd _)

/-- `(1 + qv²)^{-(n+1)}` differentiated in `q`. -/
theorem hasDerivAt_phaseMomentIntegrand (n : ℕ) {q v : ℝ} (hq : 0 < 1 + q * v ^ 2) :
    HasDerivAt (fun q : ℝ => v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1))
      (-(n + 1 : ℝ) * (v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1 + 1)))
      q := by
  have h1 : HasDerivAt (fun q : ℝ => 1 + q * v ^ 2) (v ^ 2) q := by
    simpa using ((hasDerivAt_id q).mul_const (v ^ 2)).const_add 1
  have hD : HasDerivAt (fun q : ℝ => (1 + q * v ^ 2) ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * (1 + q * v ^ 2) ^ n * v ^ 2) q := by
    have h := h1.pow (n + 1)
    rw [Nat.add_sub_cancel] at h
    exact h
  have hne : 1 + q * v ^ 2 ≠ 0 := hq.ne'
  refine ((hasDerivAt_const q (v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2)).div hD
    (pow_ne_zero _ hne)).congr_deriv ?_
  field_simp
  push_cast
  ring

theorem hasDerivAt_phaseResponseMoment (n : ℕ) {q : ℝ} (hq : -1 / 2 < q) :
    HasDerivAt (phaseResponseMoment n) (-(n + 1 : ℝ) * phaseResponseMoment (n + 1) q) q := by
  set ε := (q + 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ x ∈ Metric.ball q ε, -1 / 2 ≤ x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    linarith [hx.1]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := 0) (b := 1)
    (F := fun q v => v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1))
    (F' := fun q v => -(n + 1 : ℝ) *
      (v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1 + 1)))
    (x₀ := q) (bound := fun _ => (n + 1 : ℝ) * 2 ^ (n + 2)) (Metric.ball_mem_nhds q hε0)
    (Eventually.of_forall fun x => (by fun_prop : Measurable fun v : ℝ =>
      v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + x * v ^ 2) ^ (n + 1)).aestronglyMeasurable)
    (intervalIntegrable_phaseMomentIntegrand n (le_of_lt hq))
    ((by fun_prop : Measurable fun v : ℝ => -(n + 1 : ℝ) *
      (v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) ^ (n + 1 + 1)))
        |>.aestronglyMeasurable)
    (Eventually.of_forall fun v hv x hx => by
      rw [uIoc_of_le zero_le_one] at hv
      have hvI : v ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hv
      have hd := half_le_phaseDenom (hball x hx) hvI
      have hv2 : v ^ 2 ≤ 1 := by nlinarith [hvI.1, hvI.2]
      have hnum0 : 0 ≤ v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 :=
        mul_nonneg (pow_nonneg hvI.1 _) (sq_nonneg _)
      have hnum : v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 ≤ 1 := by
        have h1 : v ^ (2 * (n + 1) + 2) ≤ 1 := pow_le_one₀ hvI.1 hvI.2
        have h2 : (1 - v ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (sq_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hden : (1 / 2 : ℝ) ^ (n + 1 + 1) ≤ (1 + x * v ^ 2) ^ (n + 1 + 1) :=
        pow_le_pow_left₀ (by norm_num) hd _
      have hpos : 0 < (1 + x * v ^ 2) ^ (n + 1 + 1) := pow_pos (by linarith) _
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1),
        abs_of_nonneg (div_nonneg hnum0 hpos.le)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ hpos]
      calc v ^ (2 * (n + 1) + 2) * (1 - v ^ 2) ^ 2 ≤ 1 := hnum
        _ = 2 ^ (n + 2) * (1 / 2) ^ (n + 1 + 1) := by
            rw [show n + 1 + 1 = n + 2 by ring, ← mul_pow]; norm_num
        _ ≤ 2 ^ (n + 2) * (1 + x * v ^ 2) ^ (n + 1 + 1) :=
            mul_le_mul_of_nonneg_left hden (by positivity))
    intervalIntegrable_const
    (Eventually.of_forall fun v hv x hx => by
      rw [uIoc_of_le zero_le_one] at hv
      exact hasDerivAt_phaseMomentIntegrand n
        (phaseDenom_pos (hball x hx) (Ioc_subset_Icc_self hv)))
  have h := key.2
  rw [intervalIntegral.integral_const_mul] at h
  exact h

/-- **(SKPM.8), iterated derivatives.**  On `q > -1/2`,
`F⁽ⁿ⁾(q) = (-1)ⁿ 6 n! G_n(q)`. -/
theorem iteratedDeriv_phaseResponse (n : ℕ) :
    ∀ q, -1 / 2 < q →
      iteratedDeriv n phaseResponse q = (-1) ^ n * 6 * n.factorial * phaseResponseMoment n q := by
  induction n with
  | zero =>
    intro q _
    rw [iteratedDeriv_zero, phaseResponse_eq_moment]
    simp
  | succ n ih =>
    intro q hq
    have hev : iteratedDeriv n phaseResponse
        =ᶠ[𝓝 q] fun q => (-1) ^ n * 6 * n.factorial * phaseResponseMoment n q := by
      filter_upwards [lt_mem_nhds hq] with x hx
      exact ih x hx
    rw [iteratedDeriv_succ, hev.deriv_eq,
      ((hasDerivAt_phaseResponseMoment n hq).const_mul
        ((-1 : ℝ) ^ n * 6 * (n.factorial : ℝ))).deriv,
      Nat.factorial_succ]
    push_cast
    ring

/-- **(SKPM.8).**  `F` is strictly completely monotone on `q ≥ 0`. -/
theorem phaseResponse_completelyMonotone (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (-1) ^ n * iteratedDeriv n phaseResponse q = 6 * n.factorial * phaseResponseMoment n q ∧
      0 < (-1) ^ n * iteratedDeriv n phaseResponse q := by
  have h := iteratedDeriv_phaseResponse n q (by linarith)
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have heq : (-1) ^ n * iteratedDeriv n phaseResponse q
      = 6 * n.factorial * phaseResponseMoment n q := by
    rw [h]
    calc (-1 : ℝ) ^ n * ((-1) ^ n * 6 * n.factorial * phaseResponseMoment n q)
        = ((-1) ^ n * (-1) ^ n) * (6 * n.factorial * phaseResponseMoment n q) := by ring
      _ = _ := by rw [hsq, one_mul]
  refine ⟨heq, ?_⟩
  rw [heq]
  have := phaseResponseMoment_pos n (show (-1 / 2 : ℝ) ≤ q by linarith)
  positivity

theorem phaseResponseMoment_zero (n : ℕ) :
    phaseResponseMoment n 0 = 8 / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7)) := by
  have hexp : ∀ v : ℝ, v ^ (2 * n + 2) * (1 - v ^ 2) ^ 2 / (1 + 0 * v ^ 2) ^ (n + 1)
      = v ^ (2 * n + 2) - 2 * v ^ (2 * n + 4) + v ^ (2 * n + 6) := fun v => by ring
  simp_rw [phaseResponseMoment, hexp]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  · push_cast
    field_simp
    ring
  all_goals first
    | exact (continuous_pow _).intervalIntegrable _ _
    | exact ((continuous_pow _).const_mul _).intervalIntegrable _ _
    | exact ((continuous_pow _).sub ((continuous_pow _).const_mul _)).intervalIntegrable _ _

/-- **(SKPM.9).**  `(-1)ⁿ F⁽ⁿ⁾(0) = 48 n!/((2n+3)(2n+5)(2n+7))`. -/
theorem phaseResponse_jet_zero (n : ℕ) :
    (-1) ^ n * iteratedDeriv n phaseResponse 0
      = 48 * n.factorial / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7)) := by
  rw [(phaseResponse_completelyMonotone n le_rfl).1, phaseResponseMoment_zero]
  ring

/-! ## Theorems A and B: the profile -/

theorem phaseSurvivalProfile_neg (τ : ℝ) : phaseSurvivalProfile (-τ) = phaseSurvivalProfile τ := by
  rw [phaseSurvivalProfile, phaseSurvivalProfile, neg_sq]

theorem phaseSurvivalProfile_pos (τ : ℝ) : 0 < phaseSurvivalProfile τ := by
  rw [phaseSurvivalProfile, phaseResponse_eq_moment]
  have := phaseResponseMoment_pos 0 (show (-1 / 2 : ℝ) ≤ τ ^ 2 by nlinarith [sq_nonneg τ])
  positivity

/-- **(SKPM.4).**  `C(0) = 16/35`. -/
theorem phaseSurvivalProfile_zero : phaseSurvivalProfile 0 = 16 / 35 := by
  rw [phaseSurvivalProfile, phaseResponse_eq_moment, show (0 : ℝ) ^ 2 = 0 by norm_num,
    phaseResponseMoment_zero]
  norm_num

theorem integrand_lt_of_lt {a b v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hv : v ∈ Ioo (0 : ℝ) 1) :
    v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + b * v ^ 2) < v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + a * v ^ 2) := by
  have hv2 : 0 < v ^ 2 := pow_pos hv.1 2
  have h1 : 0 < 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hnum : 0 < v ^ 2 * (1 - v ^ 2) ^ 2 := mul_pos hv2 (pow_pos h1 2)
  refine div_lt_div_of_pos_left hnum (by nlinarith) ?_
  nlinarith

theorem integrand_le_of_le {a b : ℝ} (v : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + b * v ^ 2) ≤ v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + a * v ^ 2) := by
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  exact div_le_div_of_nonneg_left (mul_nonneg hv2 (sq_nonneg _)) (by nlinarith)
    (by nlinarith)

/-- **Theorem B.**  `C` is strictly decreasing in `|τ|`. -/
theorem phaseSurvivalProfile_strictAntiOn : StrictAntiOn phaseSurvivalProfile (Ici 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have ha2 : a ^ 2 < b ^ 2 := by nlinarith
  rw [phaseSurvivalProfile, phaseSurvivalProfile, phaseResponse, phaseResponse]
  refine mul_lt_mul_of_pos_left ?_ (by norm_num)
  have hb2 : (-1 / 2 : ℝ) ≤ b ^ 2 := by nlinarith [sq_nonneg b]
  have ha2' : (-1 / 2 : ℝ) ≤ a ^ 2 := by nlinarith [sq_nonneg a]
  have hcb := continuousOn_phaseMomentIntegrand 0 hb2
  have hca := continuousOn_phaseMomentIntegrand 0 ha2'
  simp only [mul_zero, zero_add, pow_one] at hcb hca
  exact integral_lt_integral_of_continuousOn_of_le_of_exists_lt zero_lt_one hcb hca
    (fun v _ => integrand_le_of_le v (sq_nonneg a) ha2.le)
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩,
      integrand_lt_of_lt (sq_nonneg a) ha2 ⟨by norm_num, by norm_num⟩⟩

theorem tendsto_one_add_sq_mul_atTop {v : ℝ} (hv : 0 < v) :
    Tendsto (fun τ : ℝ => 1 + τ ^ 2 * v ^ 2) atTop atTop := by
  refine tendsto_atTop_add_const_left _ 1 ?_
  exact (tendsto_pow_atTop two_ne_zero).atTop_mul_const (pow_pos hv 2)

/-- **(SKPM.5).**  `C(τ) → 0` as `τ → ∞`. -/
theorem tendsto_phaseSurvivalProfile_atTop : Tendsto phaseSurvivalProfile atTop (𝓝 0) := by
  have h : Tendsto (fun τ : ℝ => ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + τ ^ 2 * v ^ 2))
      atTop (𝓝 (∫ _ in (0 : ℝ)..1, (0 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun v => v ^ 2 * (1 - v ^ 2) ^ 2) (Eventually.of_forall fun τ =>
        (by fun_prop : Measurable fun v : ℝ =>
          v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + τ ^ 2 * v ^ 2)).aestronglyMeasurable)
      (Eventually.of_forall fun τ => Eventually.of_forall fun v hv => ?_)
      ((by fun_prop : Continuous fun v : ℝ => v ^ 2 * (1 - v ^ 2) ^ 2).intervalIntegrable _ _)
      (Eventually.of_forall fun v hv => ?_)
    · rw [uIoc_of_le zero_le_one] at hv
      clear hv
      have hd : 1 ≤ 1 + τ ^ 2 * v ^ 2 := by nlinarith [sq_nonneg τ, sq_nonneg v]
      have hn : 0 ≤ v ^ 2 * (1 - v ^ 2) ^ 2 := mul_nonneg (sq_nonneg v) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by linarith))]
      exact div_le_self hn hd
    · rw [uIoc_of_le zero_le_one] at hv
      exact tendsto_const_nhds.div_atTop (tendsto_one_add_sq_mul_atTop hv.1)
  rw [intervalIntegral.integral_zero] at h
  have := h.const_mul 6
  rw [mul_zero] at this
  exact this

theorem tendsto_phaseSurvivalProfile_atBot : Tendsto phaseSurvivalProfile atBot (𝓝 0) := by
  have h := tendsto_phaseSurvivalProfile_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun τ => ?_
  simp only [Function.comp_apply, phaseSurvivalProfile_neg]

/-- **(SKPM.5).**  `τ² C(τ) → 16/5` as `τ → ∞`. -/
theorem tendsto_sq_mul_phaseSurvivalProfile_atTop :
    Tendsto (fun τ => τ ^ 2 * phaseSurvivalProfile τ) atTop (𝓝 (16 / 5)) := by
  have hrw : ∀ τ : ℝ, τ ^ 2 * phaseSurvivalProfile τ
      = 6 * ∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ 2 * (τ ^ 2 * v ^ 2 / (1 + τ ^ 2 * v ^ 2)) := by
    intro τ
    rw [phaseSurvivalProfile, phaseResponse, ← mul_assoc, mul_comm (τ ^ 2) 6, mul_assoc,
      ← intervalIntegral.integral_const_mul]
    congr 1
    refine integral_congr fun v _ => ?_
    ring
  have hlim : Tendsto (fun τ : ℝ => ∫ v in (0 : ℝ)..1,
      (1 - v ^ 2) ^ 2 * (τ ^ 2 * v ^ 2 / (1 + τ ^ 2 * v ^ 2))) atTop
      (𝓝 (∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ 2)) := by
    have hcont : ∀ τ : ℝ, Continuous fun v : ℝ =>
        (1 - v ^ 2) ^ 2 * (τ ^ 2 * v ^ 2 / (1 + τ ^ 2 * v ^ 2)) := fun τ =>
      (by fun_prop : Continuous fun v : ℝ => (1 - v ^ 2) ^ 2).mul
        ((by fun_prop : Continuous fun v : ℝ => τ ^ 2 * v ^ 2).div
          (by fun_prop : Continuous fun v : ℝ => 1 + τ ^ 2 * v ^ 2)
          fun v => (lt_of_lt_of_le one_pos (le_add_of_nonneg_right
            (mul_nonneg (sq_nonneg τ) (sq_nonneg v)))).ne')
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun v => (1 - v ^ 2) ^ 2) (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
      (Eventually.of_forall fun τ => Eventually.of_forall fun v _ => ?_)
      ((by fun_prop : Continuous fun v : ℝ => (1 - v ^ 2) ^ 2).intervalIntegrable _ _)
      (Eventually.of_forall fun v hv => ?_)
    · have h0 : 0 ≤ τ ^ 2 * v ^ 2 := mul_nonneg (sq_nonneg τ) (sq_nonneg v)
      have hq : τ ^ 2 * v ^ 2 / (1 + τ ^ 2 * v ^ 2) ≤ 1 :=
        (div_le_one (by linarith)).mpr (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (div_nonneg h0 (by linarith)))]
      exact mul_le_of_le_one_right (sq_nonneg _) hq
    · rw [uIoc_of_le zero_le_one] at hv
      have hlim1 : Tendsto (fun τ : ℝ => τ ^ 2 * v ^ 2 / (1 + τ ^ 2 * v ^ 2)) atTop (𝓝 1) := by
        have h := (tendsto_one_add_sq_mul_atTop hv.1).inv_tendsto_atTop
        have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
        rw [sub_zero] at h2
        refine h2.congr' ?_
        filter_upwards [(tendsto_one_add_sq_mul_atTop hv.1).eventually_gt_atTop 0] with τ hτ
        simp only [Pi.inv_apply]
        field_simp
        ring
      have := hlim1.const_mul ((1 - v ^ 2) ^ 2)
      rwa [mul_one] at this
  have hval : ∫ v in (0 : ℝ)..1, (1 - v ^ 2) ^ 2 = 8 / 15 := by
    have hexp : ∀ v : ℝ, (1 - v ^ 2) ^ 2 = 1 - 2 * v ^ 2 + v ^ 4 := fun v => by ring
    simp_rw [hexp]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_one]
    · norm_num
    all_goals first
      | exact continuous_const.intervalIntegrable _ _
      | exact (continuous_pow _).intervalIntegrable _ _
      | exact ((continuous_pow _).const_mul _).intervalIntegrable _ _
      | exact (continuous_const.sub ((continuous_pow _).const_mul _)).intervalIntegrable _ _
  rw [hval] at hlim
  have := hlim.const_mul 6
  rw [show (6 : ℝ) * (8 / 15) = 16 / 5 by norm_num] at this
  exact this.congr fun τ => (hrw τ).symm

theorem tendsto_sq_mul_phaseSurvivalProfile_atBot :
    Tendsto (fun τ => τ ^ 2 * phaseSurvivalProfile τ) atBot (𝓝 (16 / 5)) := by
  have h := tendsto_sq_mul_phaseSurvivalProfile_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun τ => ?_
  simp only [Function.comp_apply, phaseSurvivalProfile_neg, neg_sq]

/-! ## Theorem C: the hidden beta law -/

theorem continuousOn_betaIntegrand {q : ℝ} (hq : -1 / 2 ≤ q) :
    ContinuousOn (fun s : ℝ => Real.sqrt s * (1 - s) ^ 2 / (1 + q * s)) (Icc 0 1) := by
  refine ((Real.continuous_sqrt.continuousOn).mul
    ((continuousOn_const.sub continuousOn_id).pow 2)).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun s hs => ?_
  rcases le_total 0 q with hq0 | hq0
  · nlinarith [hs.1]
  · nlinarith [hs.1, hs.2]

/-- `∫₀¹ λ^{1/2}(1 - λ)²/(1 + qλ) dλ = 2 ∫₀¹ v²(1 - v²)²/(1 + qv²) dv`, by `λ = v²`. -/
theorem integral_betaIntegrand_eq {q : ℝ} (hq : -1 / 2 ≤ q) :
    ∫ s in (0 : ℝ)..1, Real.sqrt s * (1 - s) ^ 2 / (1 + q * s)
      = 2 * ∫ v in (0 : ℝ)..1, v ^ 2 * (1 - v ^ 2) ^ 2 / (1 + q * v ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := 1)
    (f := fun v : ℝ => v ^ 2) (f' := fun v => 2 * v)
    (g := fun s : ℝ => Real.sqrt s * (1 - s) ^ 2 / (1 + q * s))
    (fun v _ => by simpa using hasDerivAt_pow 2 v) (by fun_prop)
    ((continuousOn_betaIntegrand hq).mono (by
      rintro _ ⟨v, hv, rfl⟩
      rw [uIcc_of_le zero_le_one] at hv
      exact ⟨sq_nonneg v, by nlinarith [hv.1, hv.2]⟩))
  simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  simp only [Function.comp_apply, Real.sqrt_sq hv.1]
  ring

/-- **Theorem C.**  `F(q) = 3 ∫₀¹ λ^{1/2}(1 - λ)²/(1 + qλ) dλ`. -/
theorem phaseResponse_eq_beta {q : ℝ} (hq : -1 / 2 ≤ q) :
    phaseResponse q = 3 * ∫ s in (0 : ℝ)..1, Real.sqrt s * (1 - s) ^ 2 / (1 + q * s) := by
  rw [integral_betaIntegrand_eq hq, phaseResponse]
  ring

/-- The `Beta(3/2, 3)` density `(105/16) λ^{1/2}(1 - λ)²` on `(0, 1)`. -/
def phaseBetaDensity (s : ℝ) : ℝ := 105 / 16 * (Real.sqrt s * (1 - s) ^ 2)

/-- The `Beta(3/2, 3)` law on `(0, 1)`. -/
def phaseBetaLaw : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity fun s => ENNReal.ofReal (phaseBetaDensity s)

theorem measurable_phaseBetaDensity : Measurable phaseBetaDensity := by
  unfold phaseBetaDensity
  fun_prop

theorem phaseBetaDensity_nonneg (s : ℝ) : 0 ≤ phaseBetaDensity s :=
  mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg s) (sq_nonneg _))

theorem integral_phaseBetaLaw (f : ℝ → ℝ) :
    ∫ s, f s ∂phaseBetaLaw = ∫ s in (0 : ℝ)..1, phaseBetaDensity s * f s := by
  rw [phaseBetaLaw, integral_withDensity_eq_integral_toReal_smul
    measurable_phaseBetaDensity.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (phaseBetaDensity_nonneg s)]

theorem integral_sqrt_mul_one_sub_sq : ∫ s in (0 : ℝ)..1, Real.sqrt s * (1 - s) ^ 2 = 16 / 105 := by
  have h := integral_betaIntegrand_eq (q := 0) (by norm_num)
  simp only [zero_mul, add_zero, div_one] at h
  rw [h]
  have h0 := phaseResponseMoment_zero 0
  simp only [phaseResponseMoment, mul_zero, zero_add, pow_one, zero_mul, add_zero, div_one,
    Nat.cast_zero] at h0
  rw [h0]
  norm_num

theorem integral_phaseBetaDensity : ∫ s in (0 : ℝ)..1, phaseBetaDensity s = 1 := by
  simp only [phaseBetaDensity]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_mul_one_sub_sq]
  norm_num

instance isProbabilityMeasure_phaseBetaLaw : IsProbabilityMeasure phaseBetaLaw := by
  constructor
  have hc : ContinuousOn phaseBetaDensity (Icc 0 1) := by
    unfold phaseBetaDensity
    fun_prop
  have hint : IntegrableOn phaseBetaDensity (Ioo 0 1) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [phaseBetaLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun s => phaseBetaDensity_nonneg s),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_phaseBetaDensity, ENNReal.ofReal_one]

/-- **(SKPM.7).**  `C(√q)/(16/35) = E[1/(1 + qΛ)]` for `Λ ~ Beta(3/2, 3)`. -/
theorem phaseSurvivalProfile_sqrt_div {q : ℝ} (hq : 0 ≤ q) :
    phaseSurvivalProfile (Real.sqrt q) / (16 / 35) = ∫ s, 1 / (1 + q * s) ∂phaseBetaLaw := by
  rw [integral_phaseBetaLaw, phaseSurvivalProfile, Real.sq_sqrt hq,
    phaseResponse_eq_beta (by linarith)]
  simp only [phaseBetaDensity]
  have : ∀ s : ℝ, 105 / 16 * (Real.sqrt s * (1 - s) ^ 2) * (1 / (1 + q * s))
      = 105 / 16 * (Real.sqrt s * (1 - s) ^ 2 / (1 + q * s)) := fun s => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ## The Cayley picture -/

/-- The Cayley contrast `δ = (x - y)/(x + y)`. -/
def cayleyContrast (x y : ℝ) : ℝ := (x - y) / (x + y)

/-- The Cayley coherence `g = 2√(xy)/(x + y)`. -/
def cayleyCoherence (x y : ℝ) : ℝ := 2 * Real.sqrt (x * y) / (x + y)

/-- `δ² + g² = 1`. -/
theorem cayleyContrast_sq_add_cayleyCoherence_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) : cayleyContrast x y ^ 2 + cayleyCoherence x y ^ 2 = 1 := by
  rw [cayleyContrast, cayleyCoherence, div_pow, div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hx hy)]
  field_simp
  ring

/-- `8(xy)^{3/2}/(x + y)³ = g³`. -/
theorem cubicKernel_eq_cayleyCoherence_pow {x : ℝ} (y : ℝ) (hx : 0 ≤ x) :
    8 * Real.sqrt x ^ 3 * Real.sqrt y ^ 3 / (x + y) ^ 3 = cayleyCoherence x y ^ 3 := by
  rw [cayleyCoherence, div_pow, mul_pow, Real.sqrt_mul hx, mul_pow]
  ring

/-- `δ = tanh((log x - log y)/2)`. -/
theorem cayleyContrast_eq_tanh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cayleyContrast x y = Real.tanh ((Real.log x - Real.log y) / 2) := by
  set w := (Real.log x - Real.log y) / 2
  have ha : Real.exp w * Real.exp w = x / y := by
    rw [← Real.exp_add, show w + w = Real.log x - Real.log y by ring, Real.exp_sub,
      Real.exp_log hx, Real.exp_log hy]
  have hpos := Real.exp_pos w
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, cayleyContrast]
  have hy' : y ≠ 0 := hy.ne'
  have hxy : x + y ≠ 0 := by linarith
  have hx' : x = y * (Real.exp w * Real.exp w) := by rw [ha]; field_simp
  rw [hx']
  field_simp

end GaloisForLFunctions.HTGeometry

