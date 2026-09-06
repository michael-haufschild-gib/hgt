import GaloisForLFunctions.RHTower.ArithmeticLinearPhasePrefix
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Arithmetic logarithmic segments at growing height and cutoff

Integer periodicity and the derivative of the exponential identify the finite-segment
limit of the actual Bernoulli remainder when the height is `lam*N` and `N` grows.
The substitution, power normalization, and fixed complex phase anchor are all retained.

The second complete logarithmic turn is strictly positive at arbitrarily large
cutoffs when `lam=4*pi/3`, even though the height remains below `2*pi*N`. This
refutes a universal nonpositive-turn law for the literal source. Conversely, a fixed
complete prefix with noninteger endpoint and `0<lam<2*pi` is eventually negative.
Integer endpoint coincidences have zero limiting margin and remain outside that
strict sign conclusion. Height varies with cutoff; no zeta zero is asserted here.

These are closed source identities and limiting sign theorems. They do not prove
the cumulative logarithmic-clock conjecture or a constraint on the unit remainder.
No numerical result is used in any proof.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The real logarithmic segment normalized by the positive power N^(sigma+2). -/
def scaledLogarithmicSegment (sigma lam : ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ∫ x in (N:ℝ)*Real.exp (a/N)..(N:ℝ)*Real.exp (b/N),
    RHTower.bernoulliPeriodic x * ((N:ℝ)/x)^(sigma+2) *
      Real.sin (lam*(N:ℝ)*Real.log (x/N))

/-- The exact integrand after substituting x=N*exp(v/N), at height lam*N. -/
def arithmeticClockIntegrand (sigma lam : ℝ) (N : ℕ) (v : ℝ) : ℝ :=
  RHTower.bernoulliPeriodic ((N:ℝ)*Real.exp (v/N)) *
    Real.exp (-(sigma+1)*v/N) * Real.sin (lam*v)

/-- The unscaled real sine component of the Bernoulli remainder segment. -/
def bernoulliLogarithmicSegment (sigma lam : ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ∫ x in (N:ℝ)*Real.exp (a/N)..(N:ℝ)*Real.exp (b/N),
    RHTower.bernoulliPeriodic x * x^(-sigma-2) *
      Real.sin (lam*(N:ℝ)*Real.log (x/N))

/-- The normalization is an explicit positive real power of the integer anchor. -/
theorem scaledLogarithmicSegment_eq_positive_scale (sigma lam a b : ℝ)
    {N : ℕ} (hN : 0<N) :
    scaledLogarithmicSegment sigma lam N a b =
      (N:ℝ)^(sigma+2)*bernoulliLogarithmicSegment sigma lam N a b := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  unfold scaledLogarithmicSegment bernoulliLogarithmicSegment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0<x := lt_of_lt_of_le
    (lt_min (mul_pos hNp (Real.exp_pos _)) (mul_pos hNp (Real.exp_pos _))) hx.1
  dsimp only
  rw [Real.div_rpow hNp.le hx0.le,div_eq_mul_inv,← Real.rpow_neg hx0.le]
  rw [show -(sigma+2)=-sigma-2 by ring]
  ring

private theorem clock_bernoulli_continuous : Continuous RHTower.bernoulliPeriodic :=
  (show Continuous (fun x : ℝ => (x^2-x)/2) by fun_prop).continuousOn.comp_fract'' (by norm_num)

private theorem clock_integrand_continuous (sigma lam : ℝ) (N : ℕ) :
    Continuous (arithmeticClockIntegrand sigma lam N) := by
  unfold arithmeticClockIntegrand
  exact ((clock_bernoulli_continuous.comp (by fun_prop)).mul (by fun_prop)).mul (by fun_prop)

/-- Exact change of variables, including the Jacobian and exponential weight. -/
theorem scaledLogarithmicSegment_eq_clock (sigma lam a b : ℝ) {N : ℕ} (hN : 0 < N) :
    scaledLogarithmicSegment sigma lam N a b =
      ∫ v in a..b, arithmeticClockIntegrand sigma lam N v := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hNne : (N:ℝ)≠0 := hNp.ne'
  let f : ℝ → ℝ := fun v => (N:ℝ)*Real.exp (v/N)
  let g : ℝ → ℝ := fun x => RHTower.bernoulliPeriodic x * ((N:ℝ)/x)^(sigma+2) *
    Real.sin (lam*(N:ℝ)*Real.log (x/N))
  have hd (v : ℝ) : HasDerivAt f (Real.exp (v/N)) v := by
    convert! (((hasDerivAt_id v).div_const (N:ℝ)).exp).const_mul (N:ℝ) using 1
    simp only [id_eq,one_div]
    field_simp
  have hg : ContinuousOn g (f '' uIcc a b) := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := hx
    have hp : 0 < f v := mul_pos hNp (Real.exp_pos _)
    have hc : ContinuousAt (fun x : ℝ => (N:ℝ)/x) (f v) :=
      continuousAt_const.div continuousAt_id hp.ne'
    have hr := hc.rpow_const (p:=sigma+2) (Or.inl (ne_of_gt (div_pos hNp hp)))
    have hl : ContinuousAt (fun x : ℝ => Real.log (x/N)) (f v) :=
      (continuousAt_id.div_const (N:ℝ)).log (ne_of_gt (div_pos hp hNp))
    have hphase : ContinuousAt (fun x : ℝ => lam*(N:ℝ)*Real.log (x/N)) (f v) :=
      continuousAt_const.mul hl
    exact ((clock_bernoulli_continuous.continuousAt.mul hr).mul
      (Real.continuous_sin.continuousAt.comp hphase)).continuousWithinAt
  have hs := intervalIntegral.integral_comp_mul_deriv' (a:=a) (b:=b) (f:=f)
    (f':=fun v => Real.exp (v/N)) (g:=g) (fun v _ => hd v) (by fun_prop) hg
  change (∫ v in a..b, (g ∘ f) v * Real.exp (v/N)) =
    scaledLogarithmicSegment sigma lam N a b at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro v _
  have hdiv : (N:ℝ)/((N:ℝ)*Real.exp (v/N))=Real.exp (-(v/N)) := by
    rw [Real.exp_neg]
    field_simp
  have hlog : Real.log (((N:ℝ)*Real.exp (v/N))/N)=v/N := by
    rw [mul_div_cancel_left₀ _ hNne, Real.log_exp]
  dsimp [g,f,Function.comp_def,arithmeticClockIntegrand]
  rw [hdiv,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,hlog]
  rw [show lam*(N:ℝ)*(v/N)=lam*v by field_simp]
  have he : Real.exp (-(v/N)*(sigma+2))*Real.exp (v/N)=
      Real.exp (-(sigma+1)*v/N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ = RHTower.bernoulliPeriodic ((N:ℝ)*Real.exp (v/N)) *
      (Real.exp (-(v/N)*(sigma+2))*Real.exp (v/N))*Real.sin (lam*v) := by ring
    _ = _ := by rw [he]

private theorem inverse_clock_tendsto :
    Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun n => by
    change (0:ℝ)<1/((n:ℝ)+1)
    positivity)⟩

/-- The displacement from an integer anchor approaches the constant-speed coordinate. -/
theorem tendsto_arithmetic_clock_displacement (v : ℝ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)*(Real.exp (v/((n:ℝ)+1))-1)) atTop (𝓝 v) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp (v*x)) v 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).const_mul v).exp using 1
    simp
  have hs := hd.tendsto_slope_zero_right.comp inverse_clock_tendsto
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using hs

/-- Integer periodicity removes the diverging anchor before taking the pointwise limit. -/
theorem tendsto_arithmeticClockIntegrand (sigma lam v : ℝ) :
    Tendsto (fun n : ℕ => arithmeticClockIntegrand sigma lam (n+1) v) atTop
      (𝓝 (RHTower.bernoulliPeriodic v*Real.sin (lam*v))) := by
  have hb := clock_bernoulli_continuous.continuousAt.tendsto.comp
    (tendsto_arithmetic_clock_displacement v)
  have hw : Tendsto (fun n : ℕ => Real.exp (-(sigma+1)*v/((n:ℝ)+1))) atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (-(sigma+1)*v)
    have he := Real.continuous_exp.continuousAt.tendsto.comp h
    simpa [Function.comp_def,div_eq_mul_inv] using he
  have h := (hb.mul hw).mul_const (Real.sin (lam*v))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards with n
  unfold arithmeticClockIntegrand
  have hp : RHTower.bernoulliPeriodic (((n:ℝ)+1)*Real.exp (v/((n:ℝ)+1))) =
      RHTower.bernoulliPeriodic (((n:ℝ)+1)*(Real.exp (v/((n:ℝ)+1))-1)) := by
    rw [show ((n:ℝ)+1)*Real.exp (v/((n:ℝ)+1)) =
      ((n:ℝ)+1)*(Real.exp (v/((n:ℝ)+1))-1)+(n+1:ℕ) by push_cast; ring]
    simp only [RHTower.bernoulliPeriodic,Int.fract_add_natCast]
  simp only [Nat.cast_add,Nat.cast_one,hp,Function.comp_apply]

/-- Fixed finite segments converge while the height grows proportionally to the cutoff. -/
theorem tendsto_scaledLogarithmicSegment {sigma a b : ℝ} (hsigma : -1 ≤ sigma)
    (ha : 0 ≤ a) (hab : a ≤ b) (lam : ℝ) :
    Tendsto (fun n : ℕ => scaledLogarithmicSegment sigma lam (n+1) a b) atTop
      (𝓝 (∫ v in a..b, RHTower.bernoulliPeriodic v*Real.sin (lam*v))) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a:=a) (b:=b) (μ:=volume) (l:=atTop) (F:=fun n : ℕ => arithmeticClockIntegrand sigma lam (n+1))
    (f:=fun v => RHTower.bernoulliPeriodic v*Real.sin (lam*v)) (bound:=fun _ => (1:ℝ))
  have hm : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (arithmeticClockIntegrand sigma lam (n+1)) (volume.restrict (uIoc a b)) :=
    Eventually.of_forall (fun n => (clock_integrand_continuous sigma lam (n+1)).aestronglyMeasurable)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ᵐ v ∂volume, v ∈ uIoc a b →
      ‖arithmeticClockIntegrand sigma lam (n+1) v‖ ≤ 1 := by
    apply Eventually.of_forall
    intro n
    filter_upwards with v hv
    rw [uIoc_of_le hab] at hv
    have hv0 : 0 ≤ v := ha.trans hv.1.le
    have hw : Real.exp (-(sigma+1)*v/(n+1:ℕ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
    unfold arithmeticClockIntegrand
    rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc |RHTower.bernoulliPeriodic ((n+1:ℕ)*Real.exp (v/(n+1:ℕ)))| *
        Real.exp (-(sigma+1)*v/(n+1:ℕ)) * |Real.sin (lam*v)|
        ≤ 1*1*1 := mul_le_mul
          (mul_le_mul (RHTower.abs_bernoulliPeriodic_le_one _) hw
            (Real.exp_pos _).le (by norm_num))
          (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hl : ∀ᵐ v ∂volume, v ∈ uIoc a b →
      Tendsto (fun n : ℕ => arithmeticClockIntegrand sigma lam (n+1) v) atTop
        (𝓝 (RHTower.bernoulliPeriodic v*Real.sin (lam*v))) := by
    filter_upwards with v _
    exact tendsto_arithmeticClockIntegrand sigma lam v
  have hlim := h hm hb (continuous_const.intervalIntegrable a b) hl
  apply hlim.congr'
  filter_upwards with n
  exact (scaledLogarithmicSegment_eq_clock sigma lam a b (show 0<n+1 by omega)).symm

/-- The positive constant-speed second turn persists in the actual logarithmic source. -/
theorem eventually_scaledLogarithmic_second_turn_pos {sigma : ℝ} (hsigma : -1 ≤ sigma) :
    ∀ᶠ n : ℕ in atTop,
      0 < scaledLogarithmicSegment sigma (4*Real.pi/3) (n+1) (3/2) 3 := by
  have h := tendsto_scaledLogarithmicSegment hsigma (by norm_num : (0:ℝ)≤3/2)
    (by norm_num : (3/2:ℝ)≤3) (4*Real.pi/3)
  exact h.eventually (eventually_gt_nhds linearPhase_second_turn_pos)

/-- A fixed complete prefix with noninteger limiting endpoint has an eventual strict negative sign. -/
theorem eventually_scaledLogarithmic_prefix_neg {sigma lam r : ℝ} (hsigma : -1 ≤ sigma)
    (hlam : 0 < lam) (hlam' : lam < 2*Real.pi) (m K : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (hturn : lam*((m:ℝ)+r)=2*Real.pi*K) :
    ∀ᶠ n : ℕ in atTop, scaledLogarithmicSegment sigma lam (n+1) 0 ((m:ℝ)+r) < 0 := by
  have h := tendsto_scaledLogarithmicSegment hsigma (le_refl (0:ℝ))
    (show 0≤(m:ℝ)+r by positivity) lam
  have hn := linearPhasePrefix_complete_turn_neg hlam hlam' m K hr0 hr1 hturn
  exact h.eventually (eventually_lt_nhds hn)

/-- The second logarithmic turn cannot be eventually nonpositive in this scaling family. -/
theorem not_eventually_scaledLogarithmic_second_turn_nonpos {sigma : ℝ} (hsigma : -1 ≤ sigma) :
    ¬ ∀ᶠ n : ℕ in atTop,
      scaledLogarithmicSegment sigma (4*Real.pi/3) (n+1) (3/2) 3 ≤ 0 := by
  intro h
  obtain ⟨n,hn,hp⟩ := (h.and (eventually_scaledLogarithmic_second_turn_pos hsigma)).exists
  linarith

/-- Positive real second turns exist beyond every cutoff below the proposed height threshold. -/
theorem exists_arbitrarily_large_positive_logarithmic_second_turn {sigma : ℝ}
    (hsigma : -1 ≤ sigma) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 0<N ∧
      0<(4*Real.pi/3)*(N:ℝ) ∧ (4*Real.pi/3)*(N:ℝ)<2*Real.pi*(N:ℝ) ∧
      0<bernoulliLogarithmicSegment sigma (4*Real.pi/3) N (3/2) 3 := by
  obtain ⟨n,hn,hp⟩ := ((eventually_ge_atTop M).and
    (eventually_scaledLogarithmic_second_turn_pos hsigma)).exists
  have hN : 0<n+1 := by omega
  have hNp : (0:ℝ)<(n+1:ℕ) := by exact_mod_cast hN
  refine ⟨n+1,by omega,hN,by positivity,?_,?_⟩
  · exact mul_lt_mul_of_pos_right (by nlinarith [Real.pi_pos]) hNp
  · rw [scaledLogarithmicSegment_eq_positive_scale sigma (4*Real.pi/3) (3/2) 3 hN] at hp
    exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos hNp _)).mp hp

private theorem anchored_kernel_im (s : ℂ) {N : ℕ} (hN : 0<N) {x : ℝ} (hx : 0<x) :
    ((N:ℂ)^(-s)*((RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2))).im =
      (N:ℝ)^(-s.re) * (RHTower.bernoulliPeriodic x*x^(-s.re-2)*
        Real.sin (s.im*Real.log (x/N))) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hNc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hxc : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  have hlogN : Complex.log (N:ℂ)=(Real.log (N:ℝ):ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hNp.le).symm
  rw [Complex.cpow_def_of_ne_zero hNc,Complex.cpow_def_of_ne_zero hxc,
    hlogN,← Complex.ofReal_log hx.le]
  have he : Complex.exp ((Real.log (N:ℝ):ℂ)*(-s))*
      ((RHTower.bernoulliPeriodic x:ℂ)*Complex.exp ((Real.log x:ℂ)*(-star s-2))) =
      (RHTower.bernoulliPeriodic x:ℂ)*Complex.exp
        ((Real.log (N:ℝ):ℂ)*(-s)+(Real.log x:ℂ)*(-star s-2)) := by
    rw [Complex.exp_add]
    ring
  rw [he,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,
    Complex.exp_im,Real.rpow_def_of_pos hNp,Real.rpow_def_of_pos hx,
    Real.log_div hx.ne' hNp.ne']
  simp only [Complex.add_re,Complex.mul_re,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,
    Complex.sub_re,Complex.sub_im]
  norm_num
  rw [Real.exp_add]
  ring_nf

/-- The literal complex remainder segment with the phase fixed at the integer anchor N. -/
def anchoredLogarithmicSegment (s : ℂ) (N : ℕ) (a b : ℝ) : ℂ :=
  (N:ℂ)^(-s) * ∫ x in (N:ℝ)*Real.exp (a/N)..(N:ℝ)*Real.exp (b/N),
    (RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2)

/-- Exact phase transport from the complex remainder segment to its real sine integral. -/
theorem anchoredLogarithmicSegment_im (s : ℂ) (a b : ℝ) {N : ℕ} (hN : 0<N) :
    (anchoredLogarithmicSegment s N a b).im =
      (N:ℝ)^(-s.re) * bernoulliLogarithmicSegment s.re (s.im/(N:ℝ)) N a b := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hx (x : ℝ) (hx : x ∈ uIcc ((N:ℝ)*Real.exp (a/N)) ((N:ℝ)*Real.exp (b/N))) :
      0<x := lt_of_lt_of_le
    (lt_min (mul_pos hNp (Real.exp_pos _)) (mul_pos hNp (Real.exp_pos _))) hx.1
  have hi : IntervalIntegrable (fun x : ℝ =>
      (N:ℂ)^(-s)*((RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2)))
      volume ((N:ℝ)*Real.exp (a/N)) ((N:ℝ)*Real.exp (b/N)) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul
      (Complex.continuous_ofReal.comp clock_bernoulli_continuous).continuousOn
    exact ContinuousOn.cpow_const (by fun_prop)
      (fun x h => Or.inl (by simpa using hx x h))
  have he := Complex.imCLM.intervalIntegral_comp_comm hi
  change (∫ x in (N:ℝ)*Real.exp (a/N)..(N:ℝ)*Real.exp (b/N),
      ((N:ℂ)^(-s)*((RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2))).im) =
    (∫ x in (N:ℝ)*Real.exp (a/N)..(N:ℝ)*Real.exp (b/N),
      (N:ℂ)^(-s)*((RHTower.bernoulliPeriodic x:ℂ)*(x:ℂ)^(-star s-2))).im at he
  unfold anchoredLogarithmicSegment bernoulliLogarithmicSegment
  rw [← intervalIntegral.integral_const_mul,← he,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x h
  dsimp only
  rw [anchored_kernel_im s hN (hx x h),div_mul_cancel₀ _ hNp.ne']

/-- Actual fixed-anchor complex second turns are positive at arbitrarily large cutoffs,
with height strictly below 2*pi times the cutoff. No zero of zeta is asserted here. -/
theorem exists_arbitrarily_large_positive_anchored_second_turn {sigma : ℝ}
    (hsigma : -1 ≤ sigma) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 0<N ∧
      0<(4*Real.pi/3)*(N:ℝ) ∧ (4*Real.pi/3)*(N:ℝ)<2*Real.pi*(N:ℝ) ∧
      0<(anchoredLogarithmicSegment
        ((sigma:ℂ)+(((4*Real.pi/3)*(N:ℝ):ℝ):ℂ)*Complex.I) N (3/2) 3).im := by
  obtain ⟨N,hM,hN,ht0,ht1,hpos⟩ :=
    exists_arbitrarily_large_positive_logarithmic_second_turn hsigma M
  refine ⟨N,hM,hN,ht0,ht1,?_⟩
  rw [anchoredLogarithmicSegment_im _ _ _ hN]
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  simpa [hNp.ne'] using mul_pos (Real.rpow_pos_of_pos hNp (-sigma)) hpos


/-- No sign law can make every literal complete logarithmic turn nonpositive, even
below the proposed height threshold. The phase anchor is not reset between turns. -/
theorem not_all_complete_logarithmic_turns_nonpos {sigma : ℝ} (hsigma : -1 ≤ sigma) :
    ¬ ∀ (N : ℕ), 0<N → ∀ (t : ℝ), 0<t → t<2*Real.pi*(N:ℝ) → ∀ (k : ℕ),
      ((N:ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        ∫ x in (N:ℝ)*Real.exp (2*Real.pi*(k:ℝ)/t)..
          (N:ℝ)*Real.exp (2*Real.pi*((k:ℝ)+1)/t),
          (RHTower.bernoulliPeriodic x:ℂ)*
            (x:ℂ)^(-star ((sigma:ℂ)+(t:ℂ)*Complex.I)-2)).im ≤ 0 := by
  intro h
  obtain ⟨N,_,hN,ht0,ht1,hpos⟩ :=
    exists_arbitrarily_large_positive_anchored_second_turn hsigma 0
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 2*Real.pi/((4*Real.pi/3)*(N:ℝ))=(3/2)/(N:ℝ) := by
    field_simp [Real.pi_pos.ne',hNp.ne']
    ring
  have hb : 2*Real.pi*((1:ℝ)+1)/((4*Real.pi/3)*(N:ℝ))=3/(N:ℝ) := by
    field_simp [Real.pi_pos.ne',hNp.ne']
    ring
  have hn := h N hN ((4*Real.pi/3)*(N:ℝ)) ht0 ht1 1
  simp only [Nat.cast_one,mul_one,ha,hb] at hn
  exact (not_le_of_gt hpos) hn

end RHTower.DeletionMixedRefinement
