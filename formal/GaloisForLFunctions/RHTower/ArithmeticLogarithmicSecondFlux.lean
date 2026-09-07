import GaloisForLFunctions.RHTower.ArithmeticLogarithmicResponseHeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Complete second logarithmic flux and its compensated arithmetic current

The first complete source flux is differentiated cell by cell. Every integer contributes
its literal logarithmic jump atom; the continuous periodic quadratic retains its boundary
terms. The resulting finite identity gives convergence of the arithmetic sum minus the
entire regular second-flux integral to `1/12 + t^2 * criticalFullLogResponse t`.

The two terms are kept together before taking the limit. The exact cutoff error is the
original flux tail plus the actual boundary and has an explicit majorant preserving height
dependence. No independent sign of the compensated current or RH exclusion is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Fractional-part multiplication preserves finite-interval integrability for complex profiles. -/
theorem intervalIntegrable_complex_fract_mul {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => ((Int.fract x:ℝ):ℂ)*f x) volume a b := by
  have hm : Measurable (fun x : ℝ => ((Int.fract x:ℝ):ℂ)) := by fun_prop
  have hn : ∀ x : ℝ, ‖((Int.fract x:ℝ):ℂ)‖ ≤ 1 := by
    intro x
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  exact ⟨hf.1.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hn),
    hf.2.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hn)⟩

/-- A complex unit-cell integration identity retains the upper integer jump. -/
theorem integral_unit_complex_fract_derivative {F f : ℝ → ℂ}
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F (f x) x)
    (hf : ContinuousOn f (Ioi 0)) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n:ℝ)..((n:ℝ)+1), ((Int.fract x:ℝ):ℂ)*f x) =
      F ((n:ℝ)+1)-(∫ x in (n:ℝ)..((n:ℝ)+1), F x) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : ∀ x ∈ uIcc (n:ℝ) ((n:ℝ)+1), 0<x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    linarith [hx.1]
  have he : (∫ x in (n:ℝ)..((n:ℝ)+1), ((Int.fract x:ℝ):ℂ)*f x) =
      ∫ x in (n:ℝ)..((n:ℝ)+1), ((x-(n:ℝ):ℝ):ℂ)*f x := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x : ℝ, x≠(n:ℝ)+1 := by
      rw [Filter.eventually_iff,MeasureTheory.mem_ae_iff,
        show {x : ℝ | x≠(n:ℝ)+1}ᶜ = {(n:ℝ)+1} by ext x; simp]
      exact measure_singleton _
    filter_upwards [hne] with x hx hmem
    rw [uIoc_of_le (by linarith : (n:ℝ)≤(n:ℝ)+1)] at hmem
    have hfloor : Int.floor x=(n:ℤ) := Int.floor_eq_iff.mpr
      ⟨by exact_mod_cast hmem.1.le,by exact_mod_cast lt_of_le_of_ne hmem.2 hx⟩
    simp [Int.fract,hfloor]
  rw [he]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := fun x : ℝ => ((x-(n:ℝ):ℝ):ℂ)) (u' := fun _ => (1:ℂ))
    (v := F) (v' := f)
    (fun x _ => ((hasDerivAt_id x).sub_const (n:ℝ)).ofReal_comp.hasDerivWithinAt)
    (fun x hx => (hF x (hp x hx)).hasDerivWithinAt)
    intervalIntegrable_const ((hf.mono (fun x hx => hp x hx)).intervalIntegrable)
  simpa using h

/-- The complex finite fractional-part identity includes every integer atom. -/
theorem integral_one_to_succ_complex_fract_derivative {F f : ℝ → ℂ}
    (hF : ∀ x : ℝ, 0<x → HasDerivAt F (f x) x)
    (hf : ContinuousOn f (Ioi 0)) (m : ℕ) :
    (∫ x in (1:ℝ)..((m:ℝ)+1), ((Int.fract x:ℝ):ℂ)*f x) =
      (∑ k ∈ Finset.range m, F ((k:ℝ)+2))-(∫ x in (1:ℝ)..((m:ℝ)+1), F x) := by
  have hFc : ContinuousOn F (Ioi 0) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hi {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntervalIntegrable f volume a b :=
    (hf.mono (fun x hx => lt_of_lt_of_le (lt_min ha hb) hx.1)).intervalIntegrable
  have hFi {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntervalIntegrable F volume a b :=
    (hFc.mono (fun x hx => lt_of_lt_of_le (lt_min ha hb) hx.1)).intervalIntegrable
  induction m with
  | zero => simp
  | succ m ih =>
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_complex_fract_mul (hi zero_lt_one (by positivity : 0<(m:ℝ)+1)))
      (intervalIntegrable_complex_fract_mul (hi (by positivity : 0<(m:ℝ)+1) (by positivity : 0<(m:ℝ)+2)))
    have hb := intervalIntegral.integral_add_adjacent_intervals
      (hFi zero_lt_one (by positivity : 0<(m:ℝ)+1))
      (hFi (by positivity : 0<(m:ℝ)+1) (by positivity : 0<(m:ℝ)+2))
    have hc := integral_unit_complex_fract_derivative hF hf (n := m+1) (by omega)
    norm_num only [Nat.cast_add,Nat.cast_one] at hc ⊢
    rw [show (m:ℝ)+1+1=(m:ℝ)+2 by ring] at hc ⊢
    rw [←ha,hc,ih,Finset.sum_range_succ,←hb]
    ring

/-- Exact positive-power logarithmic jump carried by every integer. -/
def criticalLogJumpAtom (t x : ℝ) : ℂ :=
  ((x^(-(1/2:ℝ))*Real.log x:ℝ):ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The continuous part of the next boundary amplitude. -/
def criticalLogSmoothBoundary (t x : ℝ) : ℂ :=
  ((x^(-(3/2:ℝ))*(1-(3/2)*Real.log x):ℝ):ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Exact derivative of the logarithmic jump profile. -/
def criticalLogJumpDerivative (t x : ℝ) : ℂ :=
  (((x^(-(3/2:ℝ))*(1-(1/2)*Real.log x):ℝ):ℂ)+
    (t:ℂ)*Complex.I*((x^(-(3/2:ℝ))*Real.log x:ℝ):ℂ))*
      Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Exact derivative of the smooth part of the boundary. -/
def criticalLogSmoothDerivative (t x : ℝ) : ℂ :=
  (((x^(-(5/2:ℝ))*((9/4)*Real.log x-3):ℝ):ℂ)+
    (t:ℂ)*Complex.I*((x^(-(5/2:ℝ))*(1-(3/2)*Real.log x):ℝ):ℂ))*
      Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Second boundary, before and after each integer jump. -/
def criticalLogSecondBoundary (t x : ℝ) : ℂ := (x:ℂ)*criticalLogFluxDensity t x

/-- Regular part of the second derivative; its discrete jump contribution is separate. -/
def criticalLogSecondRegularKernel (x : ℝ) : ℝ :=
  x^(-(1/2:ℝ))*Real.log x+
    (Int.fract x-1/2)*x^(-(3/2:ℝ))*(2-2*Real.log x)+
    (RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*((9/4)*Real.log x-3)

/-- Full phase-bearing regular second flux. -/
def criticalLogSecondRegularDensity (t x : ℝ) : ℂ :=
  (criticalLogSecondRegularKernel x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The jump profile is differentiated without modifying its arithmetic phase. -/
theorem hasDerivAt_criticalLogJumpAtom (t : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (criticalLogJumpAtom t) (criticalLogJumpDerivative t x) x := by
  have hpow := Real.hasDerivAt_rpow_const (p := -(1/2:ℝ)) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have he : x^(-(1/2:ℝ))=x^(-(3/2:ℝ))*x := by
    calc _=x^((-(3/2:ℝ))+1) := by norm_num
         _=_ := by rw [Real.rpow_add hx,Real.rpow_one]
  convert! ((hpow.mul hl).ofReal_comp).mul (hasDerivAt_logHeightCharacter t hx) using 1
  simp only [criticalLogJumpDerivative,Pi.mul_apply]
  norm_num
  rw [he]
  push_cast
  have hxC : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  field_simp [hxC]
  ring

/-- The smooth boundary part retains its full logarithmic derivative. -/
theorem hasDerivAt_criticalLogSmoothBoundary (t : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (criticalLogSmoothBoundary t) (criticalLogSmoothDerivative t x) x := by
  have hpow := Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne')
  have hl := (Real.hasDerivAt_log hx.ne').const_mul (3/2)
  have he : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc _=x^((-(5/2:ℝ))+1) := by norm_num
         _=_ := by rw [Real.rpow_add hx,Real.rpow_one]
  convert! ((hpow.mul ((hasDerivAt_const x (1:ℝ)).sub hl)).ofReal_comp).mul
    (hasDerivAt_logHeightCharacter t hx) using 1
  simp only [criticalLogSmoothDerivative,Pi.mul_apply,Pi.sub_apply]
  norm_num
  rw [he]
  push_cast
  have hxC : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  field_simp [hxC]
  ring

/-- Both explicit differentiated profiles are continuous on the positive ray. -/
theorem continuousOn_criticalLogSecondDerivatives (t : ℝ) :
    ContinuousOn (criticalLogJumpDerivative t) (Ioi 0) ∧
      ContinuousOn (criticalLogSmoothDerivative t) (Ioi 0) := by
  constructor <;> intro x hx <;> apply ContinuousAt.continuousWithinAt
  · have hx0 : x≠0 := ne_of_gt hx
    unfold criticalLogJumpDerivative
    fun_prop (disch := simp [hx0])
  · have hx0 : x≠0 := ne_of_gt hx
    unfold criticalLogSmoothDerivative
    fun_prop (disch := simp [hx0])

/-- The second boundary splits into its discontinuous and continuous factors. -/
theorem criticalLogSecondBoundary_eq (t : ℝ) {x : ℝ} (hx : 0<x) :
    criticalLogSecondBoundary t x =
      (((Int.fract x-1/2:ℝ):ℂ)*criticalLogJumpAtom t x)+
        (((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*criticalLogSmoothBoundary t x) := by
  have h1 : x^(-(1/2:ℝ))=x^(-(3/2:ℝ))*x := by
    calc _=x^((-(3/2:ℝ))+1) := by norm_num
         _=_ := by rw [Real.rpow_add hx,Real.rpow_one]
  have h2 : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc _=x^((-(5/2:ℝ))+1) := by norm_num
         _=_ := by rw [Real.rpow_add hx,Real.rpow_one]
  unfold criticalLogSecondBoundary criticalLogFluxDensity criticalLogDerivativeKernel
    criticalLogJumpAtom criticalLogSmoothBoundary
  rw [h1,h2]
  push_cast
  ring

/-- The actual regular second flux preserves the first flux and its height term exactly. -/
theorem criticalLogSecondRegularDensity_eq (t x : ℝ) :
    criticalLogSecondRegularDensity t x = criticalLogJumpAtom t x+
      ((Int.fract x-1/2:ℝ):ℂ)*criticalLogJumpDerivative t x+
      (((Int.fract x-1/2:ℝ):ℂ)*criticalLogSmoothBoundary t x+
        ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*criticalLogSmoothDerivative t x)-
      (t:ℂ)*Complex.I*criticalLogFluxDensity t x := by
  unfold criticalLogSecondRegularDensity criticalLogSecondRegularKernel criticalLogJumpAtom
    criticalLogJumpDerivative criticalLogSmoothBoundary criticalLogSmoothDerivative
    criticalLogFluxDensity criticalLogDerivativeKernel
  push_cast
  ring

/-- At integer cutoffs the boundary retains the correct post-jump value. -/
theorem criticalLogSecondBoundary_nat (t : ℝ) (m : ℕ) :
    criticalLogSecondBoundary t ((m:ℝ)+1) =
      -(1/2:ℂ)*criticalLogJumpAtom t ((m:ℝ)+1)+
        (1/12:ℂ)*criticalLogSmoothBoundary t ((m:ℝ)+1) := by
  rw [criticalLogSecondBoundary_eq t (by positivity)]
  simp [RHTower.bernoulliPeriodic]

/-- The unit boundary is nonzero and independent of height. -/
theorem criticalLogSecondBoundary_one (t : ℝ) : criticalLogSecondBoundary t 1=1/12 := by
  simpa [criticalLogJumpAtom,criticalLogSmoothBoundary] using criticalLogSecondBoundary_nat t 0

/-- Every integer jump and both boundaries are retained in the finite second integration. -/
theorem criticalLogSecondFlux_finite (t : ℝ) (m : ℕ) :
    (∫ x in (1:ℝ)..((m:ℝ)+1), criticalLogSecondRegularDensity t x)+
      (t:ℂ)*Complex.I*(∫ x in (1:ℝ)..((m:ℝ)+1), criticalLogFluxDensity t x) =
        criticalLogSecondBoundary t ((m:ℝ)+1)-1/12+
          ∑ k ∈ Finset.range m, criticalLogJumpAtom t ((k:ℝ)+2) := by
  let N : ℝ := (m:ℝ)+1
  have hN : 1≤N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hpos : ∀ x ∈ uIcc (1:ℝ) N, 0<x := by
    intro x hx
    rw [uIcc_of_le hN] at hx
    linarith [hx.1]
  let P : ℝ → ℂ := fun x => ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)
  let Q : ℝ → ℂ := fun x => ((Int.fract x-1/2:ℝ):ℂ)
  have hPc : Continuous P := Complex.continuous_ofReal.comp continuous_centeredBernoulliKernel
  have hQi : IntervalIntegrable Q volume 1 N := by
    have h := (intervalIntegrable_complex_fract_mul
      (intervalIntegrable_const (c := (1:ℂ)) (a := (1:ℝ)) (b := N))).sub
        (intervalIntegrable_const (c := (1/2:ℂ)))
    simpa [Q] using h
  have hHc : ContinuousOn (criticalLogJumpAtom t) (uIcc (1:ℝ) N) :=
    fun x hx => (hasDerivAt_criticalLogJumpAtom t (hpos x hx)).continuousAt.continuousWithinAt
  have hKc : ContinuousOn (criticalLogSmoothBoundary t) (uIcc (1:ℝ) N) :=
    fun x hx => (hasDerivAt_criticalLogSmoothBoundary t (hpos x hx)).continuousAt.continuousWithinAt
  have hHpc := (continuousOn_criticalLogSecondDerivatives t).1.mono (fun x hx => hpos x hx)
  have hKpc := (continuousOn_criticalLogSecondDerivatives t).2.mono (fun x hx => hpos x hx)
  have hQH := hQi.mul_continuousOn hHpc
  have hQK := hQi.mul_continuousOn hKc
  have hPK : IntervalIntegrable (fun x => P x*criticalLogSmoothDerivative t x) volume 1 N :=
    hKpc.intervalIntegrable.continuousOn_mul hPc.continuousOn
  have hJ : IntervalIntegrable (criticalLogFluxDensity t) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hN).mpr
      ((integrable_criticalLogFluxDensity t).mono_set Ioc_subset_Ioi_self)
  have hPd : ∀ x : ℝ, HasDerivWithinAt P (Q x) (Ioi x) x := by
    intro x
    exact (((bernoulliPeriodic_hasDerivWithinAt_right x).add_const (1/12)).mono
      Ioi_subset_Ici_self).ofReal_comp
  have hPKint : (∫ x in (1:ℝ)..N, Q x*criticalLogSmoothBoundary t x+
      P x*criticalLogSmoothDerivative t x)=
        P N*criticalLogSmoothBoundary t N-P 1*criticalLogSmoothBoundary t 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hPc.continuousOn.mul hKc)
    · intro x hx
      have hx0 : 0<x := by
        rw [min_eq_left hN,max_eq_right hN] at hx
        linarith [hx.1]
      exact (hPd x).mul (hasDerivAt_criticalLogSmoothBoundary t hx0).hasDerivWithinAt
    · exact hQK.add hPK
  have hHi : (∫ x in (1:ℝ)..N, criticalLogJumpDerivative t x)=
      criticalLogJumpAtom t N-criticalLogJumpAtom t 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_criticalLogJumpAtom t (hpos x hx)) hHpc.intervalIntegrable
  have hfract := integral_one_to_succ_complex_fract_derivative
    (fun x hx => hasDerivAt_criticalLogJumpAtom t hx)
    (continuousOn_criticalLogSecondDerivatives t).1 m
  have hQint : (∫ x in (1:ℝ)..N, Q x*criticalLogJumpDerivative t x) =
      (∑ k ∈ Finset.range m, criticalLogJumpAtom t ((k:ℝ)+2))-
        (∫ x in (1:ℝ)..N, criticalLogJumpAtom t x)-
        (1/2:ℂ)*(criticalLogJumpAtom t N-criticalLogJumpAtom t 1) := by
    have he : (fun x => Q x*criticalLogJumpDerivative t x) =
        fun x => ((Int.fract x:ℝ):ℂ)*criticalLogJumpDerivative t x-
          (1/2:ℂ)*criticalLogJumpDerivative t x := by
      funext x; dsimp [Q]; push_cast; ring
    rw [he,intervalIntegral.integral_sub
      (intervalIntegrable_complex_fract_mul hHpc.intervalIntegrable)
      (hHpc.intervalIntegrable.const_mul (1/2)),intervalIntegral.integral_const_mul,hHi]
    exact congrArg (fun z => z-(1/2:ℂ)*(criticalLogJumpAtom t N-criticalLogJumpAtom t 1)) hfract
  have he : (fun x => criticalLogSecondRegularDensity t x) = fun x =>
      criticalLogJumpAtom t x+Q x*criticalLogJumpDerivative t x+
        (Q x*criticalLogSmoothBoundary t x+P x*criticalLogSmoothDerivative t x)-
          (t:ℂ)*Complex.I*criticalLogFluxDensity t x := by
    funext x; exact criticalLogSecondRegularDensity_eq t x
  change (∫ x in (1:ℝ)..N, criticalLogSecondRegularDensity t x)+_
    =criticalLogSecondBoundary t N-1/12+_
  rw [he,intervalIntegral.integral_sub ((hHc.intervalIntegrable.add hQH).add (hQK.add hPK))
    (hJ.const_mul ((t:ℂ)*Complex.I)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hHc.intervalIntegrable.add hQH) (hQK.add hPK),
    intervalIntegral.integral_add hHc.intervalIntegrable hQH,hPKint,hQint]
  rw [show criticalLogJumpAtom t 1=0 by simp [criticalLogJumpAtom],
    show criticalLogSmoothBoundary t 1=1 by simp [criticalLogSmoothBoundary]]
  rw [show P N=(1/12:ℂ) by simp [P,N,RHTower.bernoulliPeriodic],
    show P 1=(1/12:ℂ) by simp [P,RHTower.bernoulliPeriodic]]
  dsimp only [N]
  rw [criticalLogSecondBoundary_nat]
  ring

/-- A negative power times the logarithm tends to zero. -/
theorem tendsto_criticalLog_power_log_zero {a : ℝ} (ha : 0<a) :
    Tendsto (fun x : ℝ => x^(-a)*Real.log x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.rpow_neg hx.le]
  ring

/-- The exact jump profile vanishes at the infinite endpoint. -/
theorem tendsto_criticalLogJumpAtom_zero (t : ℝ) :
    Tendsto (criticalLogJumpAtom t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_criticalLog_power_log_zero (by norm_num : (0:ℝ)<1/2)).norm
  simpa [criticalLogJumpAtom,Complex.norm_exp,Complex.mul_re] using h

/-- The smooth part of the second boundary also vanishes. -/
theorem tendsto_criticalLogSmoothBoundary_zero (t : ℝ) :
    Tendsto (criticalLogSmoothBoundary t) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/2)
  have h1 := tendsto_criticalLog_power_log_zero (by norm_num : (0:ℝ)<3/2)
  have ha : Tendsto (fun x : ℝ => x^(-(3/2:ℝ))*(1-(3/2)*Real.log x)) atTop (𝓝 0) := by
    have h := h0.sub (h1.const_mul (3/2:ℝ))
    simp only [mul_zero,sub_zero] at h
    convert h using 1
    funext x; ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [criticalLogSmoothBoundary,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_zero,Real.exp_zero,mul_one,norm_zero] using ha.norm

/-- The true post-jump boundary tends to zero along every integer cutoff. -/
theorem tendsto_criticalLogSecondBoundary_nat_zero (t : ℝ) :
    Tendsto (fun m : ℕ => criticalLogSecondBoundary t ((m:ℝ)+1)) atTop (𝓝 0) := by
  have hseq : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h := ((tendsto_criticalLogJumpAtom_zero t).comp hseq).const_mul (-(1/2:ℂ))
  have h' := ((tendsto_criticalLogSmoothBoundary_zero t).comp hseq).const_mul (1/12:ℂ)
  simpa only [mul_zero,add_zero] using (h.add h').congr
    (fun m => (criticalLogSecondBoundary_nat t m).symm)

/-- The actual arithmetic sum is compensated by the complete regular second flux before taking a limit. -/
def criticalLogSecondCurrent (t : ℝ) (m : ℕ) : ℂ :=
  (∑ k ∈ Finset.range m, criticalLogJumpAtom t ((k:ℝ)+2))-
    ∫ x in (1:ℝ)..((m:ℝ)+1), criticalLogSecondRegularDensity t x

/-- Exact finite reconstruction of the compensated current from the original first flux. -/
theorem criticalLogSecondCurrent_eq (t : ℝ) (m : ℕ) :
    criticalLogSecondCurrent t m =
      (t:ℂ)*Complex.I*(∫ x in (1:ℝ)..((m:ℝ)+1), criticalLogFluxDensity t x)-
        criticalLogSecondBoundary t ((m:ℝ)+1)+1/12 := by
  have h := criticalLogSecondFlux_finite t m
  unfold criticalLogSecondCurrent
  linear_combination -h

/-- The original full flux determines the second height response exactly. -/
theorem criticalLogFlux_second_height_identity (t : ℝ) : (t:ℂ)*Complex.I*(∫ x in Ioi (1:ℝ), criticalLogFluxDensity t x)=
    ((t^2:ℝ):ℂ)*criticalFullLogResponse t := by
  have h := criticalFullLogResponse_flux_identity t
  have hj : (∫ x in Ioi (1:ℝ), criticalLogFluxDensity t x)=
      -((t:ℂ)*Complex.I*criticalFullLogResponse t) := by linear_combination h
  rw [hj]
  calc (t:ℂ)*Complex.I*(-((t:ℂ)*Complex.I*criticalFullLogResponse t)) =
      -((t:ℂ)*Complex.I)^2*criticalFullLogResponse t := by ring
       _ = _ := by rw [mul_pow,Complex.I_sq]; push_cast; ring

/-- The second arithmetic current converges with all integer jumps and the unit boundary retained. -/
theorem tendsto_criticalLogSecondCurrent (t : ℝ) :
    Tendsto (criticalLogSecondCurrent t) atTop
      (𝓝 (1/12+((t^2:ℝ):ℂ)*criticalFullLogResponse t)) := by
  have hseq : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hi := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
    (integrable_criticalLogFluxDensity t) hseq
  have hh := criticalLogFlux_second_height_identity t
  have h := (((hi.const_mul ((t:ℂ)*Complex.I)).sub
    (tendsto_criticalLogSecondBoundary_nat_zero t)).add_const (1/12:ℂ))
  rw [sub_zero,hh,add_comm] at h
  exact h.congr (fun m => (criticalLogSecondCurrent_eq t m).symm)

/-- Exact cutoff error; every omitted integer jump remains encoded in the original flux tail. -/
theorem criticalLogSecondCurrent_sub_limit (t : ℝ) (m : ℕ) :
    criticalLogSecondCurrent t m-(1/12+((t^2:ℝ):ℂ)*criticalFullLogResponse t) =
      -((t:ℂ)*Complex.I*(∫ x in Ioi ((m:ℝ)+1), criticalLogFluxDensity t x))-
        criticalLogSecondBoundary t ((m:ℝ)+1) := by
  have hN : (1:ℝ)≤(m:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [criticalLogSecondCurrent_eq,←criticalLogFlux_second_height_identity,
    ←intervalIntegral.integral_Ioi_sub_Ioi (integrable_criticalLogFluxDensity t) hN]
  ring

/-- A literal tail certificate controls moving cutoffs with their full height dependence. -/
theorem norm_criticalLogSecondCurrent_sub_limit_le (t : ℝ) (m : ℕ) :
    ‖criticalLogSecondCurrent t m-(1/12+((t^2:ℝ):ℂ)*criticalFullLogResponse t)‖ ≤
      |t| * (∫ x in Ioi ((m:ℝ)+1), criticalLogDerivativeMajorant x)+
        ‖criticalLogSecondBoundary t ((m:ℝ)+1)‖ := by
  have hN : (1:ℝ)≤(m:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hj : ‖∫ x in Ioi ((m:ℝ)+1), criticalLogFluxDensity t x‖ ≤
      ∫ x in Ioi ((m:ℝ)+1), criticalLogDerivativeMajorant x := by
    apply norm_integral_le_of_norm_le
      (integrable_criticalLogDerivativeMajorant.mono_set (Ioi_subset_Ioi hN))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [criticalLogFluxDensity,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
      Real.exp_zero,mul_one]
    exact abs_criticalLogDerivativeKernel_le (hN.trans hx.le)
  rw [criticalLogSecondCurrent_sub_limit]
  calc ‖-((t:ℂ)*Complex.I*(∫ x in Ioi ((m:ℝ)+1), criticalLogFluxDensity t x))-
        criticalLogSecondBoundary t ((m:ℝ)+1)‖ ≤
        ‖-((t:ℂ)*Complex.I*(∫ x in Ioi ((m:ℝ)+1), criticalLogFluxDensity t x))‖+
          ‖criticalLogSecondBoundary t ((m:ℝ)+1)‖ := norm_sub_le _ _
       _ ≤ _ := by
        simp only [norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
        gcongr

end RHTower.DeletionMixedRefinement
