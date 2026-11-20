import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShiftedSquarefreeHarmonicDiagonal
import GaloisForLFunctions.RHTower.Sieve.CoprimeSignDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite and scaled limits of small frequency shifts

The Mellin weight from El Kaouni's Proposition F.2 gives a uniform
boundary term for squarefree harmonic sums. Its primitive obeys an
exact circle equation. This determines all finite limits at heights
tending to zero, and all limits after multiplication by the height.
-/
noncomputable section
open Complex Filter
open scoped Topology Interval
open _root_.RHTower (logPhase)
open _root_.RHTower.Sieve (squarefreeDensity squarefreeDensity_pos)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Arithmetic sum with its actual logarithmic phase. -/
abbrev shiftedMass (X h : ℝ) := weightedSquarefree X (logPhase h)

/-- Fourier primitive over a log interval of signed length T. -/
def logWindowPrimitive (h T : ℝ) := (T:ℂ)*unitLogWindow (h*T)

private theorem zero_window : unitLogWindow 0=1 := by
  simp [unitLogWindow]

private theorem window_continuous : Continuous unitLogWindow := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun v t : ℝ => Complex.exp (-(v:ℂ)*I*(t:ℂ)))
    (by fun_prop) 0 1

private theorem endpoint_phase (h T : ℝ) :
    1-(h:ℂ)*I*logWindowPrimitive h T=Complex.exp (-(h:ℂ)*I*(T:ℂ)) := by
  by_cases hh : h=0
  · simp [hh]
  by_cases hT : T=0
  · simp [hT,logWindowPrimitive]
  have hv : -(↑(h*T):ℂ)*I≠0 := mul_ne_zero (neg_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero hh hT))) I_ne_zero
  rw [logWindowPrimitive,unitLogWindow,integral_exp_mul_complex hv]
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero,Complex.ofReal_mul]
  rw [show -((h:ℂ)*(T:ℂ))*I=-(h:ℂ)*I*(T:ℂ) by ring]
  field_simp [Complex.ofReal_ne_zero.mpr hh,Complex.ofReal_ne_zero.mpr hT,I_ne_zero]
  ring

private theorem unit_endpoint (h T : ℝ) : ‖1-(h:ℂ)*I*logWindowPrimitive h T‖=1 := by
  rw [endpoint_phase,Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

/-- The imaginary part of the primitive is exactly its squared magnitude
times minus half the frequency. This identity includes zero frequency. -/
theorem log_window_circle (h T : ℝ) :
    2*(logWindowPrimitive h T).im= -h*‖logWindowPrimitive h T‖^2 := by
  by_cases hh : h=0
  · simp [hh,logWindowPrimitive,zero_window]
  let w := logWindowPrimitive h T
  have hz := congrArg (fun a : ℝ => a^2) (unit_endpoint h T)
  change ‖1-(h:ℂ)*I*w‖^2=1^2 at hz
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.one_im,one_pow,zero_mul,mul_zero,zero_add,add_zero,sub_zero,mul_one,
    zero_sub] at hz
  change 2*w.im= -h*‖w‖^2
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  have he : h*(2*w.im+h*(w.re*w.re+w.im*w.im))=0 := by linear_combination hz
  have hzero := (mul_eq_zero.mp he).resolve_left hh
  linarith only [hzero]

private theorem remainder_limit {α : Type*} {l : Filter α} {X h : α → ℝ}
    (hX : Tendsto X l atTop) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun k => shiftedMass (X k) (h k)-(squarefreeDensity:ℂ)*logWindowPrimitive (h k) (Real.log (X k)))
      l (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := ((tendsto_rpow_neg_atTop (by norm_num : 0<(1/2:ℝ))).comp hX).const_mul 12
  have ht := hr.add (hh.abs.const_mul 24)
  simp only [abs_zero,mul_zero,add_zero] at ht
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [hX.eventually_gt_atTop 1] with k hk
  simpa only [shiftedMass,logWindowPrimitive,←mul_assoc,Function.comp_apply] using squarefree_shifted_diagonal hk (h k)

/-- Even along arbitrary cofinal subsequences, any finite limit of raw
small-shift squarefree sums is real. -/
theorem finite_shifted_mass_limit_is_real {α : Type*} {l : Filter α} [l.NeBot]
    {X h : α → ℝ} (hX : Tendsto X l atTop) (hh : Tendsto h l (𝓝 0)) {z : ℂ}
    (hz : Tendsto (fun k => shiftedMass (X k) (h k)) l (𝓝 z)) : z.im=0 := by
  let w := fun k => logWindowPrimitive (h k) (Real.log (X k))
  let v := (z-(squarefreeHarmonicConstant:ℂ))/(squarefreeDensity:ℂ)
  have hd := Complex.ofReal_ne_zero.mpr squarefreeDensity_pos.ne'
  have hw : Tendsto w l (𝓝 v) := by
    have ht := (hz.sub (remainder_limit hX hh)).div_const (squarefreeDensity:ℂ)
    simpa only [w,v,sub_sub_cancel,mul_div_cancel_left₀ _ hd] using ht
  have he : Tendsto (fun k => 2*(w k).im) l (𝓝 0) := by
    have hzero := hh.neg.mul (hw.norm.pow 2)
    simp only [neg_zero,zero_mul] at hzero
    exact hzero.congr' (.of_forall fun k => (log_window_circle _ _).symm)
  have hv := tendsto_nhds_unique ((Complex.continuous_im.continuousAt.tendsto.comp hw).const_mul 2) he
  have hv0 : v.im=0 := by linarith only [hv]
  have heq : z=(squarefreeDensity:ℂ)*v+(squarefreeHarmonicConstant:ℂ) := by
    dsimp only [v]; rw [mul_div_cancel₀ _ hd,sub_add_cancel]
  simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,hv0,mul_zero,zero_mul,add_zero] using congrArg Complex.im heq

private theorem equal_primitive_after_period {h T t : ℝ} (hh : h≠0)
    (he : h*(T-t)=2*Real.pi) : logWindowPrimitive h T=logWindowPrimitive h t := by
  have ha : -(h:ℂ)*I*(T:ℂ) = -(h:ℂ)*I*(t:ℂ)-(2*(Real.pi:ℂ)*I) := by
    have he' := congrArg Complex.ofReal he
    push_cast at he'
    linear_combination -I*he'
  have hb : Complex.exp (-(h:ℂ)*I*(T:ℂ))=Complex.exp (-(h:ℂ)*I*(t:ℂ)) := by
    rw [ha,Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one]
  rw [←endpoint_phase,←endpoint_phase] at hb
  exact mul_left_cancel₀ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hh) I_ne_zero) (by linear_combination -hb)

private theorem log_sub_atTop (t : ℝ) : Tendsto (fun X : ℝ => Real.log X-t) atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  exact (Real.tendsto_log_atTop.eventually_ge_atTop (b+t)).mono fun X hX => by linarith only [hX]

/-- Moving the zero of the frequency window from log X to log X-t
retains precisely t units of unsmoothed logarithmic mass. -/
theorem squarefree_detuned_harmonic (t : ℝ) :
    Tendsto (fun X : ℝ => shiftedMass X (2*Real.pi/(Real.log X-t))) atTop
      (𝓝 ((squarefreeHarmonicConstant:ℂ)+(squarefreeDensity:ℂ)*(t:ℂ))) := by
  let h := fun X : ℝ => 2*Real.pi/(Real.log X-t)
  have hT := log_sub_atTop t
  have hh : Tendsto h atTop (𝓝 0) := by
    simpa [h,div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hT).const_mul (2*Real.pi)
  have hw : Tendsto (fun X : ℝ => logWindowPrimitive (h X) (Real.log X)) atTop (𝓝 (t:ℂ)) := by
    have hunit := window_continuous.continuousAt (x:=0) |>.tendsto
    have ht := (hunit.comp (by simpa only [zero_mul] using hh.mul_const t)).const_mul (t:ℂ)
    rw [zero_window,mul_one] at ht
    apply ht.congr'
    filter_upwards [hT.eventually_gt_atTop 0] with X hX
    have he : h X*(Real.log X-t)=2*Real.pi := div_mul_cancel₀ _ hX.ne'
    exact (equal_primitive_after_period (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hX.ne') he).symm
  have hsum := (remainder_limit tendsto_id hh).add (hw.const_mul (squarefreeDensity:ℂ))
  simpa only [id_eq,sub_add_cancel] using hsum

/-- The set of all finite limits obtained by choosing a vanishing height
through real cutoffs is exactly the real axis in the complex plane. -/
theorem squarefree_finite_shifted_limits (z : ℂ) :
    (∃ h : ℝ → ℝ,Tendsto h atTop (𝓝 0) ∧ Tendsto (fun X => shiftedMass X (h X)) atTop (𝓝 z)) ↔ z.im=0 := by
  refine ⟨fun ⟨_,hh,hz⟩ => finite_shifted_mass_limit_is_real tendsto_id hh hz,fun hz => ?_⟩
  let t := (z.re-squarefreeHarmonicConstant)/squarefreeDensity
  refine ⟨fun X => 2*Real.pi/(Real.log X-t),?_,?_⟩
  · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp (log_sub_atTop t)).const_mul (2*Real.pi)
  · have he : (squarefreeHarmonicConstant:ℂ)+(squarefreeDensity:ℂ)*(t:ℂ)=z := by
      rw [←Complex.ofReal_mul,←Complex.ofReal_add]
      dsimp only [t]
      rw [mul_div_cancel₀ _ squarefreeDensity_pos.ne',add_sub_cancel]
      exact Complex.ext rfl (by simp [hz])
    simpa only [he] using squarefree_detuned_harmonic t

private theorem rescaled_error {α : Type*} {l : Filter α} {X h : α → ℝ}
    (hX : Tendsto X l atTop) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun k => (h k:ℂ)*(shiftedMass (X k) (h k)-
      (squarefreeDensity:ℂ)*logWindowPrimitive (h k) (Real.log (X k)))) l (𝓝 0) := by
  simpa only [Complex.ofReal_zero,zero_mul,Function.comp_apply] using
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hh).mul (remainder_limit hX hh)

/-- Multiplication by the small height changes the limiting locus from a line
to the circle of radius d through zero centered at -id, with d=6/π². -/
theorem squarefree_scaled_shifted_limits (z : ℂ) :
    (∃ h : ℝ → ℝ, Tendsto h atTop (𝓝 0) ∧
      Tendsto (fun X => (h X:ℂ)*shiftedMass X (h X)) atTop (𝓝 z)) ↔
        ‖1-I*z/(squarefreeDensity:ℂ)‖=1 := by
  have hd := Complex.ofReal_ne_zero.mpr squarefreeDensity_pos.ne'
  constructor
  · rintro ⟨h,hh,hz⟩
    have hsum := (hz.sub (rescaled_error tendsto_id hh)).div_const (squarefreeDensity:ℂ)
    rw [sub_zero] at hsum
    have hw : Tendsto (fun X : ℝ => (h X:ℂ)*logWindowPrimitive (h X) (Real.log X))
        atTop (𝓝 (z/(squarefreeDensity:ℂ))) := by
      apply hsum.congr'
      exact .of_forall fun X => by dsimp only [id_eq]; field_simp;ring
    have hnorm := (tendsto_const_nhds (x:=(1:ℂ))).sub (hw.const_mul I)
    have he : Tendsto (fun X : ℝ => ‖1-I*((h X:ℂ)*logWindowPrimitive (h X) (Real.log X))‖)
        atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      exact .of_forall fun X => by
        change 1=‖1-I*((h X:ℂ)*logWindowPrimitive (h X) (Real.log X))‖
        rw [←mul_assoc,mul_comm I,unit_endpoint]
    simpa only [mul_div_assoc] using tendsto_nhds_unique hnorm.norm he
  · intro he
    let w := 1-I*z/(squarefreeDensity:ℂ)
    let c := -Complex.arg w
    let h := fun X : ℝ => c/Real.log X
    have hh : Tendsto h atTop (𝓝 0) := by
      exact Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
    have hp : Complex.exp (-(c:ℂ)*I)=w := by
      have harg := Complex.norm_mul_exp_arg_mul_I w
      rw [show ‖w‖=1 from he,Complex.ofReal_one,one_mul] at harg
      simpa only [c,Complex.ofReal_neg,neg_neg] using harg
    have hs : (squarefreeDensity:ℂ)*(c:ℂ)*unitLogWindow c=z := by
      have hphase := endpoint_phase c 1
      simp only [logWindowPrimitive,Complex.ofReal_one,one_mul,mul_one,hp,w] at hphase
      have hv : ((c:ℂ)*I*unitLogWindow c)=I*z/(squarefreeDensity:ℂ) := by
        linear_combination -hphase
      have heq := (eq_div_iff hd).mp hv
      calc _ = -I*(I*((squarefreeDensity:ℂ)*(c:ℂ)*unitLogWindow c)) := by rw [←mul_assoc,neg_mul,Complex.I_mul_I];ring
           _ = -I*(I*z) := by congr 1;linear_combination heq
           _ = z := by rw [←mul_assoc,neg_mul,Complex.I_mul_I]; ring
    refine ⟨h,hh,?_⟩
    have herr := (rescaled_error tendsto_id hh).add_const z
    rw [zero_add] at herr
    apply herr.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hec : h X*Real.log X=c := div_mul_cancel₀ _ (Real.log_pos hX).ne'
    have hcast := congrArg Complex.ofReal hec
    rw [Complex.ofReal_mul] at hcast
    dsimp only [id_eq]
    rw [logWindowPrimitive,hec,←hs]
    linear_combination -(squarefreeDensity:ℂ)*unitLogWindow c*hcast

/-- Signed distance in log length to the nearest complete period.
The principal argument fixes the convention at a half period. -/
def principalLogOffset (h T : ℝ) := if h=0 then T else
  -Complex.arg (Complex.exp (-(h:ℂ)*I*(T:ℂ)))/h

private theorem phase_of_offset (h T : ℝ) :
    h*principalLogOffset h T= -Complex.arg (Complex.exp (-(h:ℂ)*I*(T:ℂ))) := by
  by_cases hh : h=0
  · simp [hh]
  · rw [principalLogOffset,if_neg hh,mul_div_cancel₀ _ hh]

private theorem primitive_at_offset (h T : ℝ) :
    logWindowPrimitive h T=logWindowPrimitive h (principalLogOffset h T) := by
  by_cases hh : h=0
  · simp only [principalLogOffset,if_pos hh]
  let e := Complex.exp (-(h:ℂ)*I*(T:ℂ))
  have he : ‖e‖=1 := by
    change ‖Complex.exp (-(h:ℂ)*I*(T:ℂ))‖=1
    rw [←endpoint_phase]
    exact unit_endpoint _ _
  have harg := Complex.norm_mul_exp_arg_mul_I e
  rw [he,Complex.ofReal_one,one_mul] at harg
  have hangle := congrArg Complex.ofReal (phase_of_offset h T)
  simp only [Complex.ofReal_mul,Complex.ofReal_neg] at hangle
  have hexp : Complex.exp (-(h:ℂ)*I*(principalLogOffset h T:ℂ))=e := by
    rw [show -(h:ℂ)*I*(principalLogOffset h T:ℂ)=(Complex.arg e:ℂ)*I by
      dsimp only [e] at hangle ⊢;linear_combination -I*hangle]
    exact harg
  have hphase := (endpoint_phase h T).trans ((endpoint_phase h (principalLogOffset h T)).trans hexp).symm
  apply mul_left_cancel₀ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hh) I_ne_zero)
  linear_combination -hphase

/-- Along arbitrary cofinal observations, a prescribed finite value occurs
exactly when the reduced log length tends to its corresponding real offset.
The frequency may change sign, wind over many periods or vanish exactly. -/
theorem squarefree_limit_iff_principal_detuning {α : Type*} {l : Filter α} {X h : α → ℝ}
    (hX : Tendsto X l atTop) (hh : Tendsto h l (𝓝 0)) (t : ℝ) :
    Tendsto (fun k => shiftedMass (X k) (h k)) l
        (𝓝 ((squarefreeHarmonicConstant:ℂ)+(squarefreeDensity:ℂ)*(t:ℂ))) ↔
      Tendsto (fun k => principalLogOffset (h k) (Real.log (X k))) l (𝓝 t) := by
  let w := fun k => logWindowPrimitive (h k) (Real.log (X k))
  let u := fun k => principalLogOffset (h k) (Real.log (X k))
  have hform (k : α) : w k=(u k:ℂ)*unitLogWindow (h k*u k) :=
    primitive_at_offset _ _
  have hwiff : Tendsto (fun k => shiftedMass (X k) (h k)) l
      (𝓝 ((squarefreeHarmonicConstant:ℂ)+(squarefreeDensity:ℂ)*(t:ℂ))) ↔ Tendsto w l (𝓝 (t:ℂ)) := by
    constructor
    · intro hz
      have he := (hz.sub (remainder_limit hX hh)).div_const (squarefreeDensity:ℂ)
      have hd := Complex.ofReal_ne_zero.mpr squarefreeDensity_pos.ne'
      simpa only [w,add_sub_cancel_left,sub_sub_cancel,mul_div_cancel_left₀ _ hd] using he
    · intro hw
      have he := (remainder_limit hX hh).add (hw.const_mul (squarefreeDensity:ℂ))
      simpa only [w,sub_add_cancel] using he
  rw [hwiff]
  constructor
  · intro hw
    have hhc := Complex.continuous_ofReal.continuousAt.tendsto.comp hh
    have hep := (tendsto_const_nhds (x:=(1:ℂ))).sub ((hhc.mul_const I).mul hw)
    simp only [Complex.ofReal_zero,zero_mul,sub_zero] at hep
    have hangle := Complex.continuousAt_arg Complex.one_mem_slitPlane |>.tendsto.comp hep
    rw [Complex.arg_one] at hangle
    have hu : Tendsto (fun k => h k*u k) l (𝓝 0) := by
      have h' := hangle.neg
      rw [neg_zero] at h'
      apply h'.congr'
      exact .of_forall fun k => by
        change -Complex.arg (1-(h k:ℂ)*I*logWindowPrimitive (h k) (Real.log (X k)))=
          h k*principalLogOffset (h k) (Real.log (X k))
        rw [phase_of_offset,endpoint_phase]
    have hunit := window_continuous.continuousAt.tendsto.comp hu
    rw [zero_window] at hunit
    have hrat := hw.div hunit one_ne_zero
    rw [div_one] at hrat
    have hn := hunit.eventually_ne one_ne_zero
    have huv : Tendsto (fun k => (u k:ℂ)) l (𝓝 (t:ℂ)) := hrat.congr' (hn.mono fun k hk => by
      change w k/unitLogWindow (h k*u k)=(u k:ℂ)
      change unitLogWindow (h k*u k)≠0 at hk
      rw [hform,mul_div_cancel_right₀ _ hk])
    have hreal : Tendsto (fun k => ((u k:ℂ)).re) l (𝓝 ((t:ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp huv
    exact hreal
  · intro hu
    have hprod := hh.mul hu
    rw [zero_mul] at hprod
    have hunit := window_continuous.continuousAt.tendsto.comp hprod
    rw [zero_window] at hunit
    have h' := (Complex.continuous_ofReal.continuousAt.tendsto.comp hu).mul hunit
    rw [mul_one] at h'
    exact h'.congr' (.of_forall fun k => (hform k).symm)

#print axioms squarefree_limit_iff_principal_detuning
#print axioms log_window_circle
#print axioms finite_shifted_mass_limit_is_real
#print axioms squarefree_detuned_harmonic
#print axioms squarefree_finite_shifted_limits
#print axioms squarefree_scaled_shifted_limits
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
