import GaloisForLFunctions.RHTower.RouteEDeningerVacuumFiniteDilationFracture
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanInfiniteOrder
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogTarget
import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange
import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier

/-!
# Route E vacuum Meyer-tail / hard-collar decomposition

This module proves the exact positive decomposition left by the finite-dilation fracture:
the vacuum kernel splits into a logarithmic tail in Deninger's all-weight exponential-Schwartz
source and a compact collar.  After Möbius dilation, the collar is literally a finite sum through
scale \(2/x\); all non-Meyer arithmetic mass is isolated there.

It also supplies the reusable bridge from two-sided strong logarithmic decay to the concrete
`DeningerExpSchwartz` subtype.  No Riemann-hypothesis premise, positivity axiom, numerical
computation, or unproved asymptotic input occurs.
-/

open Complex Filter Function Set Topology Asymptotics
open scoped ContDiff

namespace RHTower

noncomputable section

/-- Real logarithmic vacuum profile `t ↦ exp(-exp t)`. -/
def routeEVacuumReal (t : ℝ) : ℝ := Real.exp (-Real.exp t)

theorem routeEVacuumReal_hasDerivAt (t : ℝ) :
    HasDerivAt routeEVacuumReal (-Real.exp t * routeEVacuumReal t) t := by
  have hinner : HasDerivAt (fun y : ℝ => -Real.exp y) (-Real.exp t) t :=
    (Real.hasDerivAt_exp t).neg
  convert hinner.exp using 1
  · rfl
  · simp only [routeEVacuumReal]
    ring

theorem routeE_polynomial_mul_vacuum_hasDerivAt (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun y => p.eval (Real.exp y) * routeEVacuumReal y)
      ((Polynomial.X * (p.derivative - p)).eval (Real.exp t) * routeEVacuumReal t) t := by
  have hp := p.hasDerivAt (Real.exp t)
  have hcomp := hp.comp t (Real.hasDerivAt_exp t)
  have hraw := hcomp.mul (routeEVacuumReal_hasDerivAt t)
  have hfun : ((fun x => p.eval x) ∘ Real.exp) * routeEVacuumReal =
      fun y => p.eval (Real.exp y) * routeEVacuumReal y := by
    funext y
    rfl
  rw [hfun] at hraw
  have hder :
      (Polynomial.X * (p.derivative - p)).eval (Real.exp t) * routeEVacuumReal t =
        p.derivative.eval (Real.exp t) * Real.exp t * routeEVacuumReal t +
          p.eval (Real.exp t) * (-Real.exp t * routeEVacuumReal t) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub]
    ring
  rw [hder]
  simpa only [Function.comp_apply] using hraw

def routeEVacuumLogProfile (t : ℝ) : ℂ := (routeEVacuumReal t : ℂ)

theorem routeEVacuumLogProfile_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) routeEVacuumLogProfile := by
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_neg.comp Real.contDiff_exp))

/-- Every logarithmic vacuum derivative is a polynomial in `exp t` times the vacuum. -/
theorem exists_routeEVacuumJetPolynomial (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ,
      iteratedDeriv n routeEVacuumLogProfile t =
        ((p.eval (Real.exp t) * routeEVacuumReal t : ℝ) : ℂ) := by
  induction n with
  | zero =>
      refine ⟨1, fun t => ?_⟩
      simp [iteratedDeriv_zero, routeEVacuumLogProfile]
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      let q := Polynomial.X * (p.derivative - p)
      refine ⟨q, fun t => ?_⟩
      have hfun : iteratedDeriv n routeEVacuumLogProfile =
          fun y => ((p.eval (Real.exp y) * routeEVacuumReal y : ℝ) : ℂ) := funext hp
      rw [iteratedDeriv_succ, hfun]
      exact (routeE_polynomial_mul_vacuum_hasDerivAt p t).ofReal_comp.deriv

theorem routeEVacuumReal_isLittleO_exp_linear_atTop (r : ℝ) :
    routeEVacuumReal =o[atTop] fun t : ℝ => Real.exp (-r * t) := by
  rw [isLittleO_iff_tendsto]
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero r 1 one_pos).comp
    Real.tendsto_exp_atTop
  convert h using 1
  · funext t
    simp only [routeEVacuumReal, Function.comp_apply, div_eq_mul_inv, ← Real.exp_neg]
    rw [Real.rpow_def_of_pos (Real.exp_pos t)]
    rw [Real.log_exp]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · intro x hx
    exact (Real.exp_ne_zero _ hx).elim

theorem routeE_polynomial_exp_isBigO_exp_natDegree (p : Polynomial ℝ) :
    (fun t : ℝ => p.eval (Real.exp t)) =O[atTop]
      fun t : ℝ => Real.exp ((p.natDegree : ℝ) * t) := by
  have hp : p.eval =O[atTop] (Polynomial.X ^ p.natDegree).eval :=
    p.isBigO_atTop_of_degree_le (Polynomial.X ^ p.natDegree) (by
      rw [Polynomial.degree_X_pow]
      exact p.degree_le_natDegree)
  have hcomp := hp.comp_tendsto Real.tendsto_exp_atTop
  apply hcomp.congr'
  · filter_upwards with t
    rfl
  · filter_upwards with t
    simp only [Function.comp_apply, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← Real.exp_nat_mul]

theorem routeE_polynomial_exp_mul_vacuum_isBigO (p : Polynomial ℝ) (a : ℝ) :
    (fun t : ℝ => p.eval (Real.exp t) * routeEVacuumReal t) =O[atTop]
      fun t : ℝ => Real.exp (-a * t) := by
  have hp := routeE_polynomial_exp_isBigO_exp_natDegree p
  have hv := (routeEVacuumReal_isLittleO_exp_linear_atTop
    (a + (p.natDegree : ℝ))).isBigO
  have hmul := hp.mul hv
  apply hmul.congr'
  · filter_upwards with t
    rfl
  · filter_upwards with t
    rw [← Real.exp_add]
    congr 1
    ring

theorem routeEVacuumLogProfile_decayTop (n : ℕ) (a : ℝ) :
    iteratedDeriv n routeEVacuumLogProfile =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  obtain ⟨p, hp⟩ := exists_routeEVacuumJetPolynomial n
  have h := routeE_polynomial_exp_mul_vacuum_isBigO p a
  rw [show iteratedDeriv n routeEVacuumLogProfile =
      fun t => ((p.eval (Real.exp t) * routeEVacuumReal t : ℝ) : ℂ) from funext hp]
  have hc : (fun t => ((p.eval (Real.exp t) * routeEVacuumReal t : ℝ) : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp (-a * t)) := by
    rw [← isBigO_norm_left]
    simpa using h.norm_left
  apply hc.congr' (Eventually.of_forall fun _ => rfl)
  filter_upwards with t
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
  congr 1
  ring

/-- Smooth cutoff equal to zero on `(-∞,0]` and one on `[log 2,∞)`. -/
def routeEVacuumTailCutoff (t : ℝ) : ℝ :=
  ccmSmoothHalflineCutoff (t / Real.log 2 - 1)

theorem routeEVacuumTailCutoff_eq_zero {t : ℝ} (ht : t ≤ 0) :
    routeEVacuumTailCutoff t = 0 := by
  apply ccmSmoothHalflineCutoff_eq_zero
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply sub_le_iff_le_add.mpr
  norm_num
  exact (div_nonpos_of_nonpos_of_nonneg ht hlog.le)

theorem routeEVacuumTailCutoff_eq_one {t : ℝ} (ht : Real.log 2 ≤ t) :
    routeEVacuumTailCutoff t = 1 := by
  apply ccmSmoothHalflineCutoff_eq_one
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [sub_nonneg, one_le_div hlog]
  exact ht

theorem routeEVacuumTailCutoff_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) routeEVacuumTailCutoff := by
  exact ccmSmoothHalflineCutoff_contDiff.comp
    ((contDiff_id.div_const (Real.log 2)).sub contDiff_const)

/-- Logarithmic Meyer tail: cutoff times the vacuum profile. -/
def routeEVacuumMeyerLogTail (t : ℝ) : ℂ :=
  (routeEVacuumTailCutoff t : ℂ) * routeEVacuumLogProfile t

theorem routeEVacuumMeyerLogTail_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) routeEVacuumMeyerLogTail := by
  exact (Complex.ofRealCLM.contDiff.comp routeEVacuumTailCutoff_contDiff).mul
    routeEVacuumLogProfile_contDiff

theorem routeEVacuumMeyerLogTail_eventuallyEq_vacuum_atTop :
    routeEVacuumMeyerLogTail =ᶠ[atTop] routeEVacuumLogProfile := by
  filter_upwards [eventually_ge_atTop (Real.log 2)] with t ht
  simp [routeEVacuumMeyerLogTail, routeEVacuumTailCutoff_eq_one ht]

theorem routeEVacuumMeyerLogTail_eventuallyEq_zero_atBot :
    routeEVacuumMeyerLogTail =ᶠ[atBot] (0 : ℝ → ℂ) := by
  filter_upwards [eventually_le_atBot 0] with t ht
  simp [routeEVacuumMeyerLogTail, routeEVacuumTailCutoff_eq_zero ht]

theorem iteratedDeriv_routeEVacuumMeyerLogTail_eventuallyEq_vacuum_atTop (n : ℕ) :
    iteratedDeriv n routeEVacuumMeyerLogTail =ᶠ[atTop]
      iteratedDeriv n routeEVacuumLogProfile := by
  filter_upwards [eventually_gt_atTop (Real.log 2)] with t ht
  have hloc : routeEVacuumMeyerLogTail =ᶠ[nhds t] routeEVacuumLogProfile := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    simp [routeEVacuumMeyerLogTail, routeEVacuumTailCutoff_eq_one hy.le]
  exact hloc.iteratedDeriv_eq n

theorem iteratedDeriv_routeEVacuumMeyerLogTail_eventuallyEq_zero_atBot (n : ℕ) :
    iteratedDeriv n routeEVacuumMeyerLogTail =ᶠ[atBot] (0 : ℝ → ℂ) := by
  filter_upwards [eventually_lt_atBot 0] with t ht
  have hloc : routeEVacuumMeyerLogTail =ᶠ[nhds t] (0 : ℝ → ℂ) := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    simp [routeEVacuumMeyerLogTail, routeEVacuumTailCutoff_eq_zero hy.le]
  rw [hloc.iteratedDeriv_eq n]
  exact iteratedDeriv_const_zero

/-- The cutoff vacuum tail has all-order, all-exponential decay at both logarithmic ends. -/
theorem routeEVacuumMeyerLogTail_strongLogDecay :
    DeningerMeyerStrongLogDecay routeEVacuumMeyerLogTail where
  smooth := routeEVacuumMeyerLogTail_contDiff
  decayTop := by
    intro n a
    exact (routeEVacuumLogProfile_decayTop n a).congr'
      (iteratedDeriv_routeEVacuumMeyerLogTail_eventuallyEq_vacuum_atTop n).symm
      (Eventually.of_forall fun _ => rfl)
  decayBot := by
    intro n b
    exact (Asymptotics.isBigO_zero (fun t : ℝ => Real.exp t ^ b) atBot).congr'
      (iteratedDeriv_routeEVacuumMeyerLogTail_eventuallyEq_zero_atBot n).symm
      (Eventually.of_forall fun _ => rfl)

/-- Strong two-sided logarithmic decay gives the global absolute exponential bounds defining `DeningerExpSchwartz`. -/
theorem DeningerMeyerStrongLogDecay.expSchwartzBounds {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
  intro A n
  obtain ⟨Cplus, hCplus⟩ :=
    (hg.weighted_iteratedDeriv_isBounded n A).exists_norm_le
  obtain ⟨Cminus, hCminus⟩ :=
    (hg.weighted_iteratedDeriv_isBounded n (-A)).exists_norm_le
  refine ⟨max Cplus Cminus, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : 0 ≤ x
  · have hraw := hCplus
      (((Real.exp x ^ A : ℝ) : ℂ) * iteratedDeriv n g x)
      (Set.mem_range_self x)
    have hle : Real.exp (A * |x|) * ‖iteratedDeriv n g x‖ ≤ Cplus := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos x) A),
        ← Real.exp_mul] at hraw
      simpa [abs_of_nonneg hx, mul_comm] using hraw
    exact hle.trans (le_max_left _ _)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hraw := hCminus
      (((Real.exp x ^ (-A) : ℝ) : ℂ) * iteratedDeriv n g x)
      (Set.mem_range_self x)
    have hle : Real.exp (A * |x|) * ‖iteratedDeriv n g x‖ ≤ Cminus := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos x) (-A)),
        ← Real.exp_mul] at hraw
      simpa [abs_of_nonpos hx', mul_comm] using hraw
    exact hle.trans (le_max_right _ _)

/-- Canonical landing of a strong-log-decay function in Deninger's exponential-Schwartz source. -/
noncomputable def deningerExpSchwartzOfStrongLogDecay
    (g : ℝ → ℂ) (hg : DeningerMeyerStrongLogDecay g) :
    DeningerExpSchwartz :=
  ⟨deningerExpSchwartzOfBounds g hg.smooth hg.expSchwartzBounds,
    deningerExpSchwartzOfBounds_mem g hg.smooth hg.expSchwartzBounds⟩

@[simp] theorem deningerExpSchwartzOfStrongLogDecay_apply
    (g : ℝ → ℂ) (hg : DeningerMeyerStrongLogDecay g) (t : ℝ) :
    (deningerExpSchwartzOfStrongLogDecay g hg : SchwartzMap ℝ ℂ) t = g t := rfl

/-- The Route E cutoff vacuum tail as a literal element of `DeningerExpSchwartz`. -/
noncomputable def routeEVacuumMeyerDeningerSource : DeningerExpSchwartz :=
  deningerExpSchwartzOfStrongLogDecay routeEVacuumMeyerLogTail
    routeEVacuumMeyerLogTail_strongLogDecay

@[simp] theorem routeEVacuumMeyerDeningerSource_apply (t : ℝ) :
    (routeEVacuumMeyerDeningerSource : SchwartzMap ℝ ℂ) t =
      routeEVacuumMeyerLogTail t := rfl

/-- Complex vacuum kernel `x ↦ exp(-x)`. -/
def routeEVacuumKernel (x : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ))

/-- Positive-radius Meyer tail `(1-χ(x)) exp(-x)`. -/
def routeEVacuumMeyerTail (x : ℝ) : ℂ :=
  (routeEVacuumTailCutoff (Real.log x) : ℂ) * routeEVacuumKernel x

/-- Compact vacuum collar `χ(x) exp(-x)`, supported on `x < 2`. -/
def routeEVacuumCollar (x : ℝ) : ℂ :=
  (1 - (routeEVacuumTailCutoff (Real.log x) : ℂ)) * routeEVacuumKernel x

/-- Exact pointwise vacuum decomposition into Meyer tail and compact collar. -/
theorem routeEVacuumKernel_eq_tail_add_collar (x : ℝ) :
    routeEVacuumKernel x = routeEVacuumMeyerTail x + routeEVacuumCollar x := by
  simp only [routeEVacuumMeyerTail, routeEVacuumCollar]
  ring

/-- Pulling the positive-radius tail through `x = exp t` recovers the strict source. -/
theorem routeEVacuumMeyerTail_exp (t : ℝ) :
    routeEVacuumMeyerTail (Real.exp t) = routeEVacuumMeyerLogTail t := by
  simp only [routeEVacuumMeyerTail, routeEVacuumKernel, Real.log_exp,
    routeEVacuumMeyerLogTail, routeEVacuumLogProfile, routeEVacuumReal]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]

theorem routeEVacuumMeyerTail_eq_zero {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) :
    routeEVacuumMeyerTail x = 0 := by
  have hlog : Real.log x ≤ 0 := by
    rw [← Real.log_one]
    exact Real.log_le_log hx0 hx
  simp [routeEVacuumMeyerTail, routeEVacuumTailCutoff_eq_zero hlog]

theorem routeEVacuumCollar_eq_zero {x : ℝ} (hx : 2 ≤ x) :
    routeEVacuumCollar x = 0 := by
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  simp [routeEVacuumCollar, routeEVacuumTailCutoff_eq_one hlog]

def routeEVacuumMeyerTailTerm (x : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    routeEVacuumMeyerTail ((n : ℝ) * x)

def routeEVacuumCollarTerm (x : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    routeEVacuumCollar ((n : ℝ) * x)

theorem mobiusDiscreteLaplaceTerm_eq_routeEVacuumTail_add_collar (x : ℝ) (n : ℕ) :
    mobiusDiscreteLaplaceTerm x n =
      routeEVacuumMeyerTailTerm x n + routeEVacuumCollarTerm x n := by
  rw [mobiusDiscreteLaplaceTerm, routeEVacuumMeyerTailTerm, routeEVacuumCollarTerm,
    ← mul_add, ← routeEVacuumKernel_eq_tail_add_collar]
  rfl

def routeEVacuumCollarIndexBound (x : ℝ) : ℕ :=
  Nat.floor (2 / x) + 1

/-- Outside the explicit `floor(2/x)+1` aperture, every Möbius collar term vanishes. -/
theorem routeEVacuumCollarTerm_eq_zero_of_not_mem
    {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ∉ Finset.range (routeEVacuumCollarIndexBound x)) :
    routeEVacuumCollarTerm x n = 0 := by
  have hnNat : Nat.floor (2 / x) + 1 ≤ n := by
    simpa [routeEVacuumCollarIndexBound, Finset.mem_range, not_lt] using hn
  have hnReal : ((Nat.floor (2 / x) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnNat
  have hdiv : 2 / x < ((Nat.floor (2 / x) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (2 / x)
  have hdivn : 2 / x < (n : ℝ) := by
    exact hdiv.trans_le (by simpa [Nat.cast_add, Nat.cast_one] using hnReal)
  have htwo : 2 ≤ (n : ℝ) * x := (div_lt_iff₀ hx).mp hdivn |>.le
  rw [routeEVacuumCollarTerm, routeEVacuumCollar_eq_zero htwo, mul_zero]

theorem summable_routeEVacuumCollarTerm {x : ℝ} (hx : 0 < x) :
    Summable (routeEVacuumCollarTerm x) := by
  apply summable_of_ne_finset_zero (s := Finset.range (routeEVacuumCollarIndexBound x))
  intro n hn
  exact routeEVacuumCollarTerm_eq_zero_of_not_mem hx hn

theorem summable_routeEVacuumMeyerTailTerm {x : ℝ} (hx : 0 < x) :
    Summable (routeEVacuumMeyerTailTerm x) := by
  have hsub := (summable_mobiusDiscreteLaplaceTerm hx).sub
    (summable_routeEVacuumCollarTerm hx)
  apply hsub.congr
  intro n
  rw [mobiusDiscreteLaplaceTerm_eq_routeEVacuumTail_add_collar]
  ring

theorem tsum_routeEVacuumCollarTerm_eq_finite {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, routeEVacuumCollarTerm x n) =
      ∑ n ∈ Finset.range (routeEVacuumCollarIndexBound x),
        routeEVacuumCollarTerm x n := by
  rw [tsum_eq_sum (s := Finset.range (routeEVacuumCollarIndexBound x))
    (fun n hn => routeEVacuumCollarTerm_eq_zero_of_not_mem hx hn)]

/-- Exact Möbius-vacuum split: summable strict Meyer tail plus finite hard collar. -/
theorem routeE_mobiusVacuum_easyTail_hardCollar_decomposition
    {x : ℝ} (hx : 0 < x) :
    mobiusDiscreteLaplaceTransform x =
      (∑' n : ℕ, routeEVacuumMeyerTailTerm x n) +
        ∑ n ∈ Finset.range (routeEVacuumCollarIndexBound x),
          routeEVacuumCollarTerm x n := by
  rw [mobiusDiscreteLaplaceTransform]
  calc
    (∑' n : ℕ, mobiusDiscreteLaplaceTerm x n) =
        ∑' n : ℕ, (routeEVacuumMeyerTailTerm x n + routeEVacuumCollarTerm x n) := by
      apply tsum_congr
      intro n
      exact mobiusDiscreteLaplaceTerm_eq_routeEVacuumTail_add_collar x n
    _ = (∑' n : ℕ, routeEVacuumMeyerTailTerm x n) +
          ∑' n : ℕ, routeEVacuumCollarTerm x n :=
      Summable.tsum_add (summable_routeEVacuumMeyerTailTerm hx)
        (summable_routeEVacuumCollarTerm hx)
    _ = _ := by rw [tsum_routeEVacuumCollarTerm_eq_finite hx]

end

end RHTower
