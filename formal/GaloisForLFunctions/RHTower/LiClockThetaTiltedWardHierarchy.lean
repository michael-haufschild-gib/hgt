import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCumulantBoundary
import GaloisForLFunctions.RHTower.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity

/-!
# The whole-line tilted Ward hierarchy of the theta law

Let `k` be the completed theta source on the whole line, `V = -log k`, and for a real tilt `a`
let `M_n(a) = ∫ x^n e^{ax} k(x) dx` and `E_a[g] = (∫ g e^{ax} k)/M_0(a)`.  The tilted score is
`T_a = V' - a`.

* every polynomial times `e^{ax} k^{(m)}` is integrable;
* `V'` is strictly increasing with `V'(x) → +∞` as `x → +∞`;
* (Ward) `E_a[f'(X)] = E_a[f(X) T_a(X)]` for every real polynomial `f`;
* (centered Ward) `E_a[(X - m)^n T_a] = n E_a[(X - m)^{n-1}]`, so `E_a[T_a] = 0`,
  `E_a[(X-κ₁)T_a] = 1`, `E_a[(X-κ₁)²T_a] = 0`, `E_a[(X-κ₁)³T_a] = 3κ₂ > 0`,
  `E_a[(X-κ₁)⁴T_a] = 4κ₃` (negative on small positive tilts), and every odd centered power has
  positive score integral;
* the tilted raw moments `t_n = M_n/M_0` are positive for `a > 0`, satisfy
  `t_n' = t_{n+1} - κ₁ t_n`, and `κ_n = t_n - Σ_{i=1}^{n-1} C(n-1, i-1) κ_i t_{n-i}`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry Polynomial
open scoped ContDiff

noncomputable section

namespace RHTower

local notation "L" => liClockThetaLogGenerator

/-! ## Polynomial admissions -/

theorem integrable_pow_mul_exp_mul_iteratedDeriv_thetaCuspFullSource (j m : ℕ) (a : ℝ) :
    Integrable (fun x : ℝ => x ^ j * Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) := by
  have hI := (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource m (1 + |a|)).const_mul
    (j.factorial : ℝ)
  refine hI.mono' ((((continuous_pow j).mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).mul (contDiff_thetaCuspFullSource.continuous_iteratedDeriv m
      (by exact_mod_cast le_top))).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Real.abs_exp]
  have h1 : |x| ^ j ≤ j.factorial * Real.exp |x| := by
    have h := Real.pow_div_factorial_le_exp _ (abs_nonneg x) j
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    rwa [div_le_iff₀ hf, mul_comm] at h
  have h2 : Real.exp (a * x) ≤ Real.exp (|a| * |x|) :=
    Real.exp_le_exp.2 (by rw [← abs_mul]; exact le_abs_self _)
  have h3 : Real.exp |x| * Real.exp (|a| * |x|) = Real.exp ((1 + |a|) * |x|) := by
    rw [← Real.exp_add]; ring_nf
  calc |x| ^ j * Real.exp (a * x) * |iteratedDeriv m thetaCuspFullSource x| ≤
      (j.factorial * Real.exp |x|) * Real.exp (|a| * |x|) *
        |iteratedDeriv m thetaCuspFullSource x| := by gcongr
    _ = _ := by rw [mul_assoc (j.factorial : ℝ), h3]; ring

theorem integrable_eval_mul_exp_mul_iteratedDeriv_thetaCuspFullSource (f : ℝ[X]) (m : ℕ) (a : ℝ) :
    Integrable (fun x : ℝ => f.eval x * Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) := by
  have h : (fun x : ℝ => f.eval x * Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) =
      fun x => ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i *
        (x ^ i * Real.exp (a * x) * iteratedDeriv m thetaCuspFullSource x) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_pow_mul_exp_mul_iteratedDeriv_thetaCuspFullSource i m a).const_mul _

/-! ## The logarithmic score -/

/-- `V' = -k'/k`. -/
def thetaCuspScore (x : ℝ) : ℝ :=
  -(iteratedDeriv 1 thetaCuspFullSource x / thetaCuspFullSource x)

theorem strictMono_thetaCuspScore : StrictMono thetaCuspScore := by
  have hd : ∀ x, HasDerivAt thetaCuspScore (-iteratedDeriv 2 thetaCuspLogSource x) x := by
    intro x
    have hfun : deriv thetaCuspLogSource = fun y =>
        iteratedDeriv 1 thetaCuspFullSource y / thetaCuspFullSource y :=
      funext fun y => (hasDerivAt_thetaCuspLogSource y).deriv
    have hdiff : DifferentiableAt ℝ (fun y => iteratedDeriv 1 thetaCuspFullSource y /
        thetaCuspFullSource y) x :=
      ((contDiff_thetaCuspFullSource.differentiable_iteratedDeriv 1
        (by exact_mod_cast WithTop.coe_lt_top _)) x).div
          (hasDerivAt_thetaCuspFullSource_iterate_zero x).differentiableAt
          (thetaCuspFullSource_pos_all x).ne'
    have h2 : HasDerivAt (fun y => iteratedDeriv 1 thetaCuspFullSource y / thetaCuspFullSource y)
        (iteratedDeriv 2 thetaCuspLogSource x) x := by
      refine hdiff.hasDerivAt.congr_deriv ?_
      rw [← hfun, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact h2.fun_neg
  refine strictMono_of_deriv_pos fun x => ?_
  rw [(hd x).deriv, iteratedDeriv_two_thetaCuspLogSource_eq]
  have hnum := thetaCuspLogConcavityNumerator_neg_all x
  have hden : 0 < thetaCuspFullSource x ^ 2 := sq_pos_of_pos (thetaCuspFullSource_pos_all x)
  have := div_neg_of_neg_of_pos hnum hden
  linarith

/-- `V'(x) → +∞` as `x → +∞`. -/
theorem tendsto_thetaCuspScore_atTop : Tendsto thetaCuspScore atTop atTop := by
  refine strictMono_thetaCuspScore.monotone.tendsto_atTop_atTop_iff.2 fun A => ?_
  by_contra hcon
  push Not at hcon
  -- `log k + A x` is monotone on `[0, ∞)`
  have hmono : MonotoneOn (fun x => thetaCuspLogSource x + A * x) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (contDiff_thetaCuspFullSource.continuous.log fun x =>
        (thetaCuspFullSource_pos_all x).ne').continuousOn.add (continuous_const.mul
          continuous_id).continuousOn
    · intro x _
      exact ((hasDerivAt_thetaCuspLogSource x).fun_add ((hasDerivAt_id' x).const_mul A)).differentiableAt
        |>.differentiableWithinAt
    · intro x _
      rw [((hasDerivAt_thetaCuspLogSource x).fun_add ((hasDerivAt_id' x).const_mul A)).deriv]
      have := hcon x
      unfold thetaCuspScore at this
      simp only [mul_one]
      linarith
  obtain ⟨C, hC, henv⟩ := thetaCuspFullSource_superexponential_envelope (A + 1)
  have hk0 := thetaCuspFullSource_pos_all 0
  have hbound : ∀ x, 0 ≤ x → thetaCuspFullSource 0 * Real.exp (-(A * x)) ≤ thetaCuspFullSource x := by
    intro x hx
    have h := hmono self_mem_Ici hx hx
    simp only [mul_zero, add_zero, thetaCuspLogSource] at h
    have h' : Real.log (thetaCuspFullSource 0) - A * x ≤ Real.log (thetaCuspFullSource x) := by
      linarith
    have := Real.exp_le_exp.2 h'
    rw [Real.exp_sub, Real.exp_log hk0, Real.exp_log (thetaCuspFullSource_pos_all x)] at this
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact this
  obtain ⟨x, hx1, hx2⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).eventually
    (gt_mem_nhds (show C * 0 < thetaCuspFullSource 0 by rw [mul_zero]; exact hk0))).and
      (eventually_ge_atTop (0 : ℝ)) |>.exists
  have h1 := hbound x hx2
  have h2 := henv x
  rw [abs_of_nonneg hx2] at h2
  have he : Real.exp (-((A + 1) * x)) = Real.exp (-(A * x)) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  rw [he] at h2
  have hA : 0 < Real.exp (-(A * x)) := Real.exp_pos _
  have : thetaCuspFullSource 0 * Real.exp (-(A * x)) ≤ C * Real.exp (-x) * Real.exp (-(A * x)) := by
    nlinarith
  have := le_of_mul_le_mul_right this hA
  linarith

/-! ## The Ward identity -/

/-- The tilted score `T_a = V' - a`. -/
def thetaTiltWardScore (a x : ℝ) : ℝ := thetaCuspScore x - a

/-- **Tilted Ward identity (C15).**  `∫ f'(x) e^{ax} k(x) dx = ∫ f(x) T_a(x) e^{ax} k(x) dx` for
every real polynomial `f`. -/
theorem integral_derivative_mul_tilt_eq_score (f : ℝ[X]) (a : ℝ) :
    ∫ x, (derivative f).eval x * Real.exp (a * x) * thetaCuspFullSource x =
      ∫ x, f.eval x * thetaTiltWardScore a x * Real.exp (a * x) * thetaCuspFullSource x := by
  set v : ℝ → ℝ := fun x => Real.exp (a * x) * thetaCuspFullSource x
  set v' : ℝ → ℝ := fun x => Real.exp (a * x) * (a * thetaCuspFullSource x +
    iteratedDeriv 1 thetaCuspFullSource x)
  have hv : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul a).exp.mul (hasDerivAt_thetaCuspFullSource_iterate_zero x)
    refine h.congr_deriv ?_
    simp only [v']
    ring
  have hu : ∀ x, HasDerivAt (fun x => f.eval x) ((derivative f).eval x) x := fun x => f.hasDerivAt x
  have hk0 := integrable_eval_mul_exp_mul_iteratedDeriv_thetaCuspFullSource
  have huv' : Integrable ((fun x => f.eval x) * v') := by
    have h := ((hk0 f 0 a).const_mul a).add (hk0 f 1 a)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, v', iteratedDeriv_zero]
    ring
  have hu'v : Integrable ((fun x => (derivative f).eval x) * v) := by
    refine (hk0 (derivative f) 0 a).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, v, iteratedDeriv_zero]
    ring
  have huv : Integrable ((fun x => f.eval x) * v) := by
    refine (hk0 f 0 a).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, v, iteratedDeriv_zero]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    huv' hu'v huv
  have e1 : ∫ x, (derivative f).eval x * Real.exp (a * x) * thetaCuspFullSource x =
      ∫ x, (derivative f).eval x * v x := integral_congr_ae (Eventually.of_forall fun x => by
        simp only [v]; ring)
  have e2 : ∫ x, f.eval x * thetaTiltWardScore a x * Real.exp (a * x) * thetaCuspFullSource x =
      -∫ x, f.eval x * v' x := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hk := (thetaCuspFullSource_pos_all x).ne'
    simp only [v', thetaTiltWardScore, thetaCuspScore]
    field_simp
    ring
  rw [e1, e2, key, neg_neg]

/-- The tilted expectation `E_a[g] = (∫ g e^{ax} k)/M_0(a)`. -/
def thetaTiltExpectation (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  (∫ x, g x * Real.exp (a * x) * thetaCuspFullSource x) / thetaTiltMoment a 0

theorem thetaTiltExpectation_ward (f : ℝ[X]) (a : ℝ) :
    thetaTiltExpectation a (fun x => (derivative f).eval x) =
      thetaTiltExpectation a (fun x => f.eval x * thetaTiltWardScore a x) := by
  unfold thetaTiltExpectation
  rw [integral_derivative_mul_tilt_eq_score]

/-- **Centered Ward hierarchy (C16).**  `E_a[(X - m)^{n+1} T_a] = (n+1) E_a[(X - m)^n]`. -/
theorem thetaTiltExpectation_centered_ward (a m : ℝ) (n : ℕ) :
    thetaTiltExpectation a (fun x => (x - m) ^ (n + 1) * thetaTiltWardScore a x) =
      (n + 1) * thetaTiltExpectation a (fun x => (x - m) ^ n) := by
  have h := thetaTiltExpectation_ward ((X - C m) ^ (n + 1)) a
  simp only [derivative_X_sub_C_pow, eval_mul, eval_pow, eval_sub, eval_X, eval_C,
    Nat.add_sub_cancel] at h
  rw [← h]
  unfold thetaTiltExpectation
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  push_cast
  ring

theorem thetaTiltExpectation_score (a : ℝ) : thetaTiltExpectation a (thetaTiltWardScore a) = 0 := by
  have h := thetaTiltExpectation_ward (C 1) a
  simp only [derivative_C, eval_zero, eval_C, one_mul] at h
  rw [← h]
  simp [thetaTiltExpectation]

/-! ## Tilted moments and cumulants -/

/-- The tilted raw moments `t_n = M_n/M_0`. -/
def thetaTiltRawMoment (a : ℝ) (n : ℕ) : ℝ := thetaTiltMoment a n / thetaTiltMoment a 0

theorem thetaTiltExpectation_pow (a : ℝ) (n : ℕ) :
    thetaTiltExpectation a (fun x => x ^ n) = thetaTiltRawMoment a n := rfl

theorem iteratedDeriv_thetaTiltMoment (n : ℕ) :
    iteratedDeriv n (fun t => thetaTiltMoment t 0) = fun t => thetaTiltMoment t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_thetaTiltMoment_global t n).deriv

theorem contDiff_thetaTiltMoment : ContDiff ℝ ∞ fun t => thetaTiltMoment t 0 := by
  refine contDiff_of_differentiable_iteratedDeriv fun n _ => ?_
  rw [iteratedDeriv_thetaTiltMoment]
  exact fun t => (hasDerivAt_thetaTiltMoment_global t n).differentiableAt

/-- `κ₁ = M₁/M₀`. -/
theorem deriv_liClockThetaLogGenerator_eq_thetaTiltMean :
    deriv L = thetaTiltMean := by
  rw [deriv_liClockThetaLogGenerator_eq_xiRealLogDeriv]
  funext a
  exact (thetaTiltMean_eq_xiRealLogDeriv a).symm

/-- `t_n' = t_{n+1} - κ₁ t_n`. -/
theorem hasDerivAt_thetaTiltRawMoment (a : ℝ) (n : ℕ) :
    HasDerivAt (fun t => thetaTiltRawMoment t n)
      (thetaTiltRawMoment a (n + 1) - iteratedDeriv 1 L a * thetaTiltRawMoment a n) a := by
  have h0 := thetaTiltMoment_zero_pos_global a
  have h := (hasDerivAt_thetaTiltMoment_global a n).div (hasDerivAt_thetaTiltMoment_global a 0) h0.ne'
  refine h.congr_deriv ?_
  rw [iteratedDeriv_one, deriv_liClockThetaLogGenerator_eq_thetaTiltMean]
  unfold thetaTiltRawMoment thetaTiltMean
  field_simp

/-- **Cumulant recursion (C17).**
`t_{n+1} = Σ_{i ≤ n} C(n, i) t_i κ_{n+1-i}`, i.e. `κ_n = t_n - Σ_{i=1}^{n-1} C(n-1, i-1) κ_i t_{n-i}`. -/
theorem thetaTiltRawMoment_succ_eq (a : ℝ) (n : ℕ) :
    thetaTiltRawMoment a (n + 1) = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * thetaTiltRawMoment a i * iteratedDeriv (n - i + 1) L a := by
  set Z : ℝ → ℝ := fun t => thetaTiltMoment t 0
  have hZ := contDiff_thetaTiltMoment
  have hκ : ContDiff ℝ ∞ (deriv L) :=
    contDiff_liClockThetaLogGenerator.iterate_deriv 1
  have hZ' : deriv Z = Z * deriv L := by
    funext t
    rw [(hasDerivAt_thetaTiltMoment_global t 0).deriv, Pi.mul_apply,
      deriv_liClockThetaLogGenerator_eq_thetaTiltMean]
    unfold thetaTiltMean
    field_simp [(thetaTiltMoment_zero_pos_global t).ne']
    rfl
  have h := congrFun (iteratedDeriv_thetaTiltMoment (n + 1)) a
  rw [iteratedDeriv_succ', hZ', iteratedDeriv_mul (hZ.contDiffAt.of_le (by exact_mod_cast le_top))
    (hκ.contDiffAt.of_le (by exact_mod_cast le_top))] at h
  have h0 := (thetaTiltMoment_zero_pos_global a).ne'
  unfold thetaTiltRawMoment
  rw [← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_thetaTiltMoment, ← iteratedDeriv_succ']
  field_simp

theorem liClockThetaLogCumulant_eq_rawMoment_sub (a : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) L a = thetaTiltRawMoment a (n + 1) -
      ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) * thetaTiltRawMoment a (i + 1) *
        iteratedDeriv (n - (i + 1) + 1) L a := by
  rw [thetaTiltRawMoment_succ_eq, Finset.sum_range_succ']
  simp [thetaTiltRawMoment, (thetaTiltMoment_zero_pos_global a).ne']

private theorem fold_pos {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) (n : ℕ) :
    0 < x ^ n * Real.exp (a * x) + (-x) ^ n * Real.exp (a * -x) := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow]
    have : 0 < x ^ n := hn.pow_pos hx
    positivity
  · rw [hn.neg_pow]
    rcases lt_or_gt_of_ne hx with hx | hx
    · have h1 : x ^ n < 0 := hn.pow_neg hx
      have h2 : Real.exp (a * x) < Real.exp (a * -x) := Real.exp_lt_exp.2 (by nlinarith)
      nlinarith
    · have h1 : 0 < x ^ n := pow_pos hx n
      have h2 : Real.exp (a * -x) < Real.exp (a * x) := Real.exp_lt_exp.2 (by nlinarith)
      nlinarith

/-- **Positive tilted moments.**  `M_n(a) > 0` and `t_n(a) > 0` for every `n` and `a > 0`. -/
theorem thetaTiltMoment_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < thetaTiltMoment a n := by
  set g : ℝ → ℝ := fun x => x ^ n * Real.exp (a * x) * thetaCuspFullSource x
  have hg := integrable_thetaTiltIntegrand_global a n
  have hneg : ∫ x, g (-x) = ∫ x, g x := integral_neg_eq_self g volume
  have hsum : 2 * thetaTiltMoment a n = ∫ x, (g x + g (-x)) := by
    rw [integral_add hg hg.comp_neg, hneg]
    unfold thetaTiltMoment; ring
  have hfold : ∀ x, g x + g (-x) =
      (x ^ n * Real.exp (a * x) + (-x) ^ n * Real.exp (a * -x)) * thetaCuspFullSource x := by
    intro x
    simp only [g, thetaCuspFullSource_neg]
    ring
  have hnn : 0 ≤ fun x => g x + g (-x) := fun x => by
    show (0 : ℝ) ≤ g x + g (-x)
    rw [hfold]
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [neg_zero]
      rcases n with _ | n
      · simp; positivity [thetaCuspFullSource_pos_all 0]
      · simp
    · exact (mul_pos (fold_pos ha hx n) (thetaCuspFullSource_pos_all x)).le
  have hpos : 0 < ∫ x, (g x + g (-x)) := by
    rw [integral_pos_iff_support_of_nonneg hnn (hg.add hg.comp_neg)]
    have hsupp : Ioi (0 : ℝ) ⊆ Function.support fun x => g x + g (-x) := by
      intro x hx
      rw [Function.mem_support, hfold]
      exact (mul_pos (fold_pos ha (ne_of_gt hx) n) (thetaCuspFullSource_pos_all x)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  linarith

theorem thetaTiltRawMoment_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < thetaTiltRawMoment a n :=
  div_pos (thetaTiltMoment_pos ha n) (thetaTiltMoment_zero_pos_global a)

/-! ## Centered moments and the signed Ward couplings -/

theorem thetaTiltExpectation_centered_one (a : ℝ) :
    thetaTiltExpectation a (fun x => x - iteratedDeriv 1 L a) = 0 := by
  have h0 := (thetaTiltMoment_zero_pos_global a).ne'
  rw [iteratedDeriv_one, deriv_liClockThetaLogGenerator_eq_thetaTiltMean]
  unfold thetaTiltExpectation thetaTiltMean
  have hi : ∫ x, (x - thetaTiltMoment a 1 / thetaTiltMoment a 0) * Real.exp (a * x) *
      thetaCuspFullSource x = thetaTiltMoment a 1 - thetaTiltMoment a 1 / thetaTiltMoment a 0 *
        thetaTiltMoment a 0 := by
    have e : (fun x => (x - thetaTiltMoment a 1 / thetaTiltMoment a 0) * Real.exp (a * x) *
        thetaCuspFullSource x) = fun x => x ^ 1 * Real.exp (a * x) * thetaCuspFullSource x -
          thetaTiltMoment a 1 / thetaTiltMoment a 0 * (x ^ 0 * Real.exp (a * x) *
            thetaCuspFullSource x) := by
      funext x; ring
    rw [e, integral_sub (integrable_thetaTiltIntegrand_global a 1)
      ((integrable_thetaTiltIntegrand_global a 0).const_mul _), integral_const_mul]
    rfl
  rw [hi]
  field_simp
  ring

/-- `E_a[(X - κ₁)^n]` in terms of raw moments. -/
private theorem thetaTiltExpectation_poly (a : ℝ) (p : ℝ[X]) :
    thetaTiltExpectation a (fun x => p.eval x) =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * thetaTiltRawMoment a i := by
  unfold thetaTiltExpectation thetaTiltRawMoment
  have e : (fun x => p.eval x * Real.exp (a * x) * thetaCuspFullSource x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i *
        (x ^ i * Real.exp (a * x) * thetaCuspFullSource x) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, integral_finsetSum _ fun i _ => (integrable_thetaTiltIntegrand_global a i).const_mul _,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  unfold thetaTiltMoment
  ring

/-- `κ₂ = E_a[(X - κ₁)²]`. -/
theorem thetaTiltExpectation_centered_two (a : ℝ) :
    thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 2) = iteratedDeriv 2 L a := by
  have h2 := thetaTiltRawMoment_succ_eq a 1
  have h1 := thetaTiltRawMoment_succ_eq a 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, Nat.sub_zero] at h1 h2
  have ht0 : thetaTiltRawMoment a 0 = 1 := div_self (thetaTiltMoment_zero_pos_global a).ne'
  have e : (fun x => (x - iteratedDeriv 1 L a) ^ 2) = fun x =>
      ((X - C (iteratedDeriv 1 L a)) ^ 2 : ℝ[X]).eval x := by
    funext x; simp
  rw [e, thetaTiltExpectation_poly]
  have hd : ((X - C (iteratedDeriv 1 L a)) ^ 2 : ℝ[X]).natDegree = 2 := by
    rw [natDegree_pow, natDegree_X_sub_C]
  rw [hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have c0 : ((X - C (iteratedDeriv 1 L a)) ^ 2 : ℝ[X]).coeff 0 = iteratedDeriv 1 L a ^ 2 := by
    simp [sq, coeff_mul]
  have c1 : ((X - C (iteratedDeriv 1 L a)) ^ 2 : ℝ[X]).coeff 1 = -2 * iteratedDeriv 1 L a := by
    rw [sq, coeff_mul]
    simp [Finset.Nat.antidiagonal_succ, coeff_X, coeff_C]
    ring
  have c2 : ((X - C (iteratedDeriv 1 L a)) ^ 2 : ℝ[X]).coeff 2 = 1 := by
    have := (monic_X_sub_C (iteratedDeriv 1 L a)).pow 2
    rw [Monic, leadingCoeff, hd] at this
    exact this
  rw [c0, c1, c2, ht0]
  simp only [ht0, one_mul] at h1
  linear_combination h2 - iteratedDeriv 1 L a * h1 + iteratedDeriv 2 L a * ht0

/-- **Signed Ward couplings (C16).**  `E_a[(X-κ₁)T_a] = 1`, `E_a[(X-κ₁)²T_a] = 0`,
`E_a[(X-κ₁)³T_a] = 3κ₂ > 0`. -/
theorem thetaTiltExpectation_centered_score (a : ℝ) :
    thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) * thetaTiltWardScore a x) = 1 ∧
      thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 2 * thetaTiltWardScore a x) = 0 ∧
        thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 3 * thetaTiltWardScore a x) =
          3 * iteratedDeriv 2 L a := by
  have h0 := thetaTiltExpectation_centered_ward a (iteratedDeriv 1 L a) 0
  have h1 := thetaTiltExpectation_centered_ward a (iteratedDeriv 1 L a) 1
  have h2 := thetaTiltExpectation_centered_ward a (iteratedDeriv 1 L a) 2
  simp only [pow_zero, zero_add, pow_one, Nat.cast_zero, one_mul] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]
    unfold thetaTiltExpectation
    rw [show (∫ x, (1 : ℝ) * Real.exp (a * x) * thetaCuspFullSource x) = thetaTiltMoment a 0 from
      integral_congr_ae (Eventually.of_forall fun x => by simp)]
    exact div_self (thetaTiltMoment_zero_pos_global a).ne'
  · rw [h1, thetaTiltExpectation_centered_one, mul_zero]
  · rw [h2, thetaTiltExpectation_centered_two]
    norm_num

/-- Every odd centered power has positive score integral. -/
theorem thetaTiltExpectation_odd_centered_score_pos (a m : ℝ) (r : ℕ) :
    0 < thetaTiltExpectation a (fun x => (x - m) ^ (2 * r + 1) * thetaTiltWardScore a x) := by
  rw [thetaTiltExpectation_centered_ward]
  refine mul_pos (by positivity) ?_
  unfold thetaTiltExpectation
  refine div_pos ?_ (thetaTiltMoment_zero_pos_global a)
  have hint : Integrable (fun x => (x - m) ^ (2 * r) * Real.exp (a * x) * thetaCuspFullSource x) := by
    have := integrable_eval_mul_exp_mul_iteratedDeriv_thetaCuspFullSource ((X - C m) ^ (2 * r)) 0 a
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp
  have hnn : 0 ≤ fun x => (x - m) ^ (2 * r) * Real.exp (a * x) * thetaCuspFullSource x :=
    fun x => by
      have := thetaCuspFullSource_pos_all x
      have : 0 ≤ (x - m) ^ (2 * r) := by rw [pow_mul]; positivity
      positivity
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsupp : Ioi m ⊆ Function.support fun x =>
      (x - m) ^ (2 * r) * Real.exp (a * x) * thetaCuspFullSource x := by
    intro x hx
    rw [Function.mem_support]
    have hxm : x - m ≠ 0 := sub_ne_zero.2 (ne_of_gt hx)
    have : 0 < (x - m) ^ (2 * r) := by rw [pow_mul]; exact pow_pos (by positivity) r
    exact (mul_pos (mul_pos this (Real.exp_pos _)) (thetaCuspFullSource_pos_all x)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsupp)
  rw [Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `κ₃ = E_a[(X - κ₁)³]`. -/
theorem thetaTiltExpectation_centered_three (a : ℝ) :
    thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 3) = iteratedDeriv 3 L a := by
  set m := iteratedDeriv 1 L a with hm
  have e : (fun x => (x - m) ^ 3) = fun x => ((X + C (-m)) ^ 3 : ℝ[X]).eval x := by
    funext x; simp [sub_eq_add_neg]
  have hd : ((X + C (-m)) ^ 3 : ℝ[X]).natDegree = 3 := by
    rw [natDegree_pow, natDegree_X_add_C]
  rw [e, thetaTiltExpectation_poly, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_X_add_C_pow]
  have ht0 : thetaTiltRawMoment a 0 = 1 := div_self (thetaTiltMoment_zero_pos_global a).ne'
  have r1 := thetaTiltRawMoment_succ_eq a 0
  have r2 := thetaTiltRawMoment_succ_eq a 1
  have r3 := thetaTiltRawMoment_succ_eq a 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, Nat.sub_zero] at r1 r2 r3
  norm_num at r1 r2 r3
  rw [ht0] at r1 r2 r3
  simp only [one_mul] at r1 r2 r3
  rw [ht0, r3, r2, r1, hm, iteratedDeriv_one]
  norm_num
  ring

/-- `E_a[(X - κ₁)⁴ T_a] = 4κ₃`, negative on a punctured right neighbourhood of `0`. -/
theorem thetaTiltExpectation_centered_four_score (a : ℝ) :
    thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 4 * thetaTiltWardScore a x) =
      4 * iteratedDeriv 3 L a := by
  rw [thetaTiltExpectation_centered_ward a _ 3, thetaTiltExpectation_centered_three]
  norm_num

theorem exists_thetaTiltExpectation_centered_four_score_neg :
    ∃ ε > 0, ∀ a ∈ Ioo (0 : ℝ) ε,
      thetaTiltExpectation a (fun x => (x - iteratedDeriv 1 L a) ^ 4 * thetaTiltWardScore a x) < 0 := by
  obtain ⟨ε, hε, h⟩ := exists_iteratedDeriv_three_liClockThetaLogGenerator_neg
  refine ⟨ε, hε, fun a ha => ?_⟩
  rw [thetaTiltExpectation_centered_four_score]
  linarith [h a ha]

end RHTower
