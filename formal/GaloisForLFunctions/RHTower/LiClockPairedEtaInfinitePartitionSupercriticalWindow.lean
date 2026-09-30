import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBorel
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace RHTower
noncomputable section

private theorem sc_log_pos {N : ℕ} (hN : 0<N) : 0<Real.log (2*(N:ℝ)) := by
  apply Real.log_pos
  have h : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  linarith

private theorem sc_sqrt_half {c : ℝ} (hc : (1/4:ℝ)<c) : (1/2:ℝ)<Real.sqrt c := by
  have hs:=Real.sq_sqrt (show 0≤c by linarith)
  have hn:=Real.sqrt_nonneg c
  nlinarith

private theorem sc_exp_integrable {L : ℝ} (hL : 0<L) (v : ℝ) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (v*(p.1-p.2)))
      (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability hL
  apply (integrable_const (Real.exp (|v| * L))).mono'
    (show Continuous (fun p:ℝ×ℝ=>Real.exp (v*(p.1-p.2))) by fun_prop).aestronglyMeasurable
  filter_upwards [liClockPairedEtaContiguousSymmetrizedMeasure_support L] with p hp
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    v*(p.1-p.2)≤|v*(p.1-p.2)| := le_abs_self _
    _=|v| * |p.1-p.2| := abs_mul _ _
    _≤|v| * L := mul_le_mul_of_nonneg_left hp (abs_nonneg v)

private theorem sc_cosh_integrable {L : ℝ} (hL : 0<L) (v : ℝ) :
    Integrable (fun p:ℝ×ℝ=>Real.cosh (v*(p.1-p.2)))
      (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  have hi:=((sc_exp_integrable hL v).add (sc_exp_integrable hL (-v))).div_const 2
  convert hi using 1
  funext p
  rw [Real.cosh_eq]
  congr 2
  congr 1
  ring

private theorem sc_mgf_eq {L : ℝ} (hL : 0<L) {v : ℝ}
    (hm : 1/2-v≠0) (hp : 1/2+v≠0) :
    mgf (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L) v =
      ((1-Real.exp (-L*(1/2-v)))/(1/2-v))*
      ((1-Real.exp (-L*(1/2+v)))/(1/2+v)) /
        liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  have hmc : (1/2:ℂ)-(v:ℂ)≠0 := by
    have h:=Complex.ofReal_ne_zero.mpr hm
    push_cast at h
    exact h
  have hpc : (1/2:ℂ)+(v:ℂ)≠0 := by
    have h:=Complex.ofReal_ne_zero.mpr hp
    push_cast at h
    exact h
  apply Complex.ofReal_injective
  rw [← complexMGF_ofReal,liClockPairedEtaContiguousSymmetrizedMeasure_complexMGF_eq_source hL.le,
    liClockPairedEtaContiguousPartition_eq_div hmc,
    liClockPairedEtaContiguousPartition_eq_div hpc]
  push_cast
  rfl

private theorem sc_cosh_mgf_eq {L : ℝ} (hL : 0<L) {v : ℝ}
    (hm : 1/2-v≠0) (hp : 1/2+v≠0) :
    (∫p:ℝ×ℝ,Real.cosh (v*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) =
      ((1-Real.exp (-L*(1/2-v)))/(1/2-v))*
      ((1-Real.exp (-L*(1/2+v)))/(1/2+v)) /
        liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  have hi1:=sc_exp_integrable hL v
  have hi2:=sc_exp_integrable hL (-v)
  have heq : (fun p:ℝ×ℝ=>Real.cosh (v*(p.1-p.2))) =
      (fun p:ℝ×ℝ=>(Real.exp (v*(p.1-p.2))+Real.exp ((-v)*(p.1-p.2)))/2) := by
    funext p
    rw [Real.cosh_eq]
    congr 2
    congr 1
    ring
  rw [heq,integral_div,integral_add hi1 hi2]
  change (mgf _ _ v+mgf _ _ (-v))/2=_
  rw [sc_mgf_eq hL hm hp,sc_mgf_eq hL (by simpa only [sub_neg_eq_add] using hp)
    (by simpa only [sub_eq_add_neg] using hm)]
  simp only [sub_eq_add_neg]
  ring_nf

private theorem sc_moment_le_cosh {L : ℝ} (hL : 0<L) (v : ℝ) (j : ℕ) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment L j*v^(2*j)/((2*j).factorial:ℝ) ≤
      ∫p:ℝ×ℝ,Real.cosh (v*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L := by
  have hi := (integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment L j).const_mul
    (v^(2*j)/((2*j).factorial:ℝ))
  have heq (p:ℝ×ℝ) : (v^(2*j)/((2*j).factorial:ℝ))*(p.1-p.2)^(2*j) =
      (v*(p.1-p.2))^(2*j)/((2*j).factorial:ℝ) := by
    rw [mul_pow]
    ring
  have h := integral_mono hi (sc_cosh_integrable hL v) (fun p=>by
    rw [heq]
    simpa only [←Real.cosh_eq_tsum] using
      (Real.hasSum_cosh (v*(p.1-p.2))).summable.le_tsum j
        (fun n _=>div_nonneg (by rw [pow_mul]; positivity) (by positivity)))
  rw [integral_const_mul] at h
  change (v^(2*j)/((2*j).factorial:ℝ))*liClockPairedEtaContiguousSymmetrizedEvenMoment L j≤_ at h
  calc
    liClockPairedEtaContiguousSymmetrizedEvenMoment L j*v^(2*j)/((2*j).factorial:ℝ) =
      (v^(2*j)/((2*j).factorial:ℝ))*liClockPairedEtaContiguousSymmetrizedEvenMoment L j := by ring
    _≤_ := h

private theorem sc_cosh_rawfactor_eq {L a : ℝ} (hL : 0<L) (ha : 0<a) :
    (∫p:ℝ×ℝ,Real.cosh ((a+1/2)*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) =
      (((Real.exp (a*L)-1)/a)*((1-Real.exp (-((a+1)*L)))/(a+1))) /
        liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  rw [sc_cosh_mgf_eq hL (by linarith) (by linarith),
    show (1/2:ℝ)-(a+1/2)=-a by ring,show (1/2:ℝ)+(a+1/2)=a+1 by ring,
    show -L*(-a)=a*L by ring,show -L*(a+1)=-((a+1)*L) by ring,div_neg]
  ring

private theorem sc_exterior_exponent {c L τ : ℝ}
    (hc : (1/4 : ℝ) < c) (_hL : 0 ≤ L) (hτ : c*L ≤ τ) :
    (Real.sqrt c-1/2)*L+(1/Real.sqrt c-2)*τ ≤
      -2*(Real.sqrt c-1/2)^2*L := by
  have hc0 : 0 ≤ c := by linarith
  set a : ℝ := Real.sqrt c
  have hsq : a^2 = c := Real.sq_sqrt hc0
  have hnonneg : 0 ≤ a := Real.sqrt_nonneg c
  have hhalf : (1/2 : ℝ) < a := by nlinarith
  have ha : 0 < a := by linarith
  have hane : a ≠ 0 := by linarith
  have hcoef : 1-2*a ≤ 0 := by linarith
  have horder := mul_le_mul_of_nonpos_left hτ hcoef
  apply (mul_le_mul_iff_of_pos_left ha).mp
  calc
    a*((a-1/2)*L+(1/a-2)*τ)
        = a*(a-1/2)*L+(1-2*a)*τ := by field_simp [hane]
    _ ≤ a*(a-1/2)*L+(1-2*a)*(c*L) := by linarith only [horder]
    _ = a*(-2*(a-1/2)^2*L) := by rw [← hsq]; ring

private theorem sc_series_le_cosh
    {d : ℕ → ℝ} {theta tau M : ℝ}
    (htheta : 0 < theta) (htau : 0 ≤ tau)
    (hcoef : ∀ j, d j * theta^(2*j) / ((2*j).factorial : ℝ) ≤ M)
    (hs : Summable (fun j => d j * tau^(2*j) / ((2*j).factorial : ℝ)^2)) :
    (∑' j, d j * tau^(2*j) / ((2*j).factorial : ℝ)^2) ≤
      M * Real.cosh (tau/theta) := by
  have hcosh := (Real.hasSum_cosh (tau/theta)).mul_left M
  calc
    (∑' j, d j * tau^(2*j) / ((2*j).factorial : ℝ)^2) ≤
        ∑' j, M * ((tau/theta)^(2*j) / ((2*j).factorial : ℝ)) := by
      apply Summable.tsum_le_tsum _ hs hcosh.summable
      intro j
      have htheta_ne : theta ≠ 0 := by linarith
      have hfactorial_ne : ((2*j).factorial : ℝ) ≠ 0 := by positivity
      have hweight : 0 ≤ (tau/theta)^(2*j) / ((2*j).factorial : ℝ) := by positivity
      have hterm := mul_le_mul_of_nonneg_right (hcoef j) hweight
      have heq :
          (d j * theta^(2*j) / ((2*j).factorial : ℝ)) *
              ((tau/theta)^(2*j) / ((2*j).factorial : ℝ)) =
            d j * tau^(2*j) / ((2*j).factorial : ℝ)^2 := by
        rw [div_pow]
        field_simp [htheta_ne, hfactorial_ne]
      rw [heq] at hterm
      exact hterm
    _ = M * Real.cosh (tau/theta) := hcosh.tsum_eq

private theorem sc_log_tendsto :
    Tendsto (fun N:ℕ=>Real.log (2*(N:ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))

/-- Exact positive decay rate beyond the strict quarter scale. -/
def liClockPairedEtaInfinitePartitionSupercriticalRate (c : ℝ) : ℝ :=
  2*(Real.sqrt c-1/2)^2

/-- Source-independent exterior envelope, with the literal first-interval mass. -/
def liClockPairedEtaInfinitePartitionSupercriticalEnvelope (c : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
    ((2-Real.sqrt 2)^2*(c-1/4))

theorem liClockPairedEtaInfinitePartitionSupercriticalRate_pos {c : ℝ}
    (hc : (1/4:ℝ)<c) : 0<liClockPairedEtaInfinitePartitionSupercriticalRate c := by
  have h:=sc_sqrt_half hc
  unfold liClockPairedEtaInfinitePartitionSupercriticalRate
  positivity

theorem liClockPairedEtaInfinitePartitionSupercriticalEnvelope_nonneg {c : ℝ}
    (hc : (1/4:ℝ)<c) (N : ℕ) :
    0≤liClockPairedEtaInfinitePartitionSupercriticalEnvelope c N := by
  have h : 0<c-1/4 := by linarith
  unfold liClockPairedEtaInfinitePartitionSupercriticalEnvelope
  positivity

theorem tendsto_liClockPairedEtaInfinitePartitionSupercriticalEnvelope_zero {c : ℝ}
    (hc : (1/4:ℝ)<c) :
    Tendsto (liClockPairedEtaInfinitePartitionSupercriticalEnvelope c) atTop (nhds 0) := by
  have hrate:=liClockPairedEtaInfinitePartitionSupercriticalRate_pos hc
  have ht:=Real.tendsto_exp_atBot.comp
    (sc_log_tendsto.const_mul_atTop_of_neg (show -liClockPairedEtaInfinitePartitionSupercriticalRate c<0 by linarith))
  change Tendsto (fun N:ℕ=>Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*
    Real.log (2*(N:ℝ)))/((2-Real.sqrt 2)^2*(c-1/4))) atTop (nhds 0)
  simpa only [Function.comp_apply,zero_div]
    using ht.div_const ((2-Real.sqrt 2)^2*(c-1/4))

private theorem sc_cosh_le_exp {x : ℝ} (hx : 0≤x) : Real.cosh x≤Real.exp x := by
  rw [Real.cosh_eq]
  have he:=Real.exp_le_exp.mpr (show -x≤x by linarith)
  linarith

private theorem sc_contiguous_le_cosh {L theta tau : ℝ}
    (hL : 0<L) (htheta : 0<theta) (htau : 0≤tau) :
    liClockPairedEtaContiguousBorelKernel L tau ≤
      (∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.cosh (tau/theta) := by
  rw [liClockPairedEtaContiguousBorelKernel_eq_tsum]
  apply sc_series_le_cosh htheta htau (fun j=>sc_moment_le_cosh hL theta j)
  convert summable_liClockPairedEtaContiguousBorelTerm hL tau using 1
  funext j
  unfold liClockPairedEtaContiguousBorelCoefficient
  ring

private theorem sc_actual_radial {N : ℕ} (hN : 0<N) (z : ℂ) :
    ‖liClockPairedEtaPartitionBorelKernelComplex N z‖≤liClockPairedEtaPartitionBorelKernel N ‖z‖ := by
  calc
    _≤∑'j:ℕ,‖(liClockPairedEtaPartitionBorelCoefficient N j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_liClockPairedEtaPartitionBorelTermComplex hN z)
    _=_ := by
      rw [liClockPairedEtaPartitionBorelKernel_eq_tsum]
      apply tsum_congr
      intro j
      have hc : 0≤liClockPairedEtaPartitionBorelCoefficient N j :=
        div_nonneg (liClockPairedEtaSymmetrizedEvenMoment_pos hN j).le (sq_nonneg _)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc,norm_pow]
      unfold liClockPairedEtaPartitionBorelCoefficient
      ring

private theorem sc_contiguous_radial {L : ℝ} (hL : 0<L) (z : ℂ) :
    ‖liClockPairedEtaContiguousBorelKernelComplex L z‖≤liClockPairedEtaContiguousBorelKernel L ‖z‖ := by
  calc
    _≤∑'j:ℕ,‖(liClockPairedEtaContiguousBorelCoefficient L j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_liClockPairedEtaContiguousBorelTermComplex hL z)
    _=_ := by
      rw [liClockPairedEtaContiguousBorelKernel_eq_tsum]
      apply tsum_congr
      intro j
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (liClockPairedEtaContiguousBorelCoefficient_pos hL j),norm_pow]
      unfold liClockPairedEtaContiguousBorelCoefficient
      ring

private lemma sc_scalar_one_sub_exp_neg_pos_lt_one {x : ℝ} (hx : 0<x) :
    0<1-Real.exp (-x) ∧ 1-Real.exp (-x)<1 := by
  have hlt : Real.exp (-x)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-x)
  constructor <;> linarith

private lemma sc_scalar_jplus_pos_le {a L : ℝ} (ha : 0<a) (hL : 0<L) :
    0<(Real.exp (a*L)-1)/a ∧
      (Real.exp (a*L)-1)/a≤L*Real.exp (a*L) := by
  have hx : 0<a*L := mul_pos ha hL
  have hpos : 0<Real.exp (a*L)-1 := by
    have he := Real.one_lt_exp_iff.mpr hx
    linarith
  have hmul : Real.exp (a*L)*Real.exp (-(a*L))=1 := by
    have he := Real.exp_add (a*L) (-(a*L))
    norm_num at he
    exact he.symm
  have hlinear : 1-Real.exp (-(a*L))≤a*L := by
    have he := Real.add_one_le_exp (-(a*L))
    linarith
  refine ⟨div_pos hpos ha, (div_le_iff₀ ha).mpr ?_⟩
  calc
    Real.exp (a*L)-1 = Real.exp (a*L)*(1-Real.exp (-(a*L))) := by nlinarith [hmul]
    _ ≤ Real.exp (a*L)*(a*L) :=
      mul_le_mul_of_nonneg_left hlinear (Real.exp_pos (a*L)).le
    _ = L*Real.exp (a*L)*a := by ring

private lemma sc_scalar_jminus_pos_le {a L : ℝ} (ha : 0<a) (hL : 0<L) :
    0<(1-Real.exp (-((a+1)*L)))/(a+1) ∧
      (1-Real.exp (-((a+1)*L)))/(a+1)≤1/(a+1) := by
  have hap : 0<a+1 := by linarith
  have hx := sc_scalar_one_sub_exp_neg_pos_lt_one (mul_pos hap hL)
  exact ⟨div_pos hx.1 hap, div_le_div_of_nonneg_right hx.2.le hap.le⟩

/-- The exact positive finite numerator is strictly below one. -/
private theorem sc_scalar_numerator_pos_lt_one {a L : ℝ}
    (ha : 0<a) (hL : 0<L) :
    0<(1-Real.exp (-(a*L)))*(1-Real.exp (-((a+1)*L))) ∧
      (1-Real.exp (-(a*L)))*(1-Real.exp (-((a+1)*L)))<1 := by
  have hfirst := sc_scalar_one_sub_exp_neg_pos_lt_one (mul_pos ha hL)
  have hsecond := sc_scalar_one_sub_exp_neg_pos_lt_one
    (mul_pos (by linarith : 0<a+1) hL)
  refine ⟨mul_pos hfirst.1 hsecond.1, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hfirst.2 hsecond.1
  nlinarith

/-- Exact exponential re-expression of both finite scalar factors. -/
private theorem sc_scalar_factor_eq {a L : ℝ}
    (_ha : 0<a) (_hL : 0<L) :
    (Real.exp (a*L)-1)*(1-Real.exp (-((a+1)*L)))/(a*(a+1)) =
      Real.exp (a*L)*((1-Real.exp (-(a*L)))*(1-Real.exp (-((a+1)*L))))/(a*(a+1)) := by
  have hmul : Real.exp (a*L)*Real.exp (-(a*L))=1 := by
    have he := Real.exp_add (a*L) (-(a*L))
    norm_num at he
    exact he.symm
  have he : Real.exp (a*L)-1 = Real.exp (a*L)*(1-Real.exp (-(a*L))) := by
    nlinarith [hmul]
  rw [he]
  ring

/-- Dropping only the exact finite numerator gives the constant envelope. -/
private theorem sc_scalar_constant_le {a L : ℝ}
    (ha : 0<a) (hL : 0<L) :
    (Real.exp (a*L)-1)*(1-Real.exp (-((a+1)*L)))/(a*(a+1)) ≤
      Real.exp (a*L)/(a*(a+1)) := by
  have hP := sc_scalar_numerator_pos_lt_one ha hL
  rw [sc_scalar_factor_eq ha hL]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hP.2.le (Real.exp_pos (a*L)).le
  nlinarith

/-- Both positive scalar factor bounds retain the polynomial refinement. -/
private theorem sc_scalar_polynomial_le {a L : ℝ}
    (ha : 0<a) (hL : 0<L) :
    (Real.exp (a*L)-1)*(1-Real.exp (-((a+1)*L)))/(a*(a+1)) ≤
      L*Real.exp (a*L)/(a+1) := by
  have hplus := sc_scalar_jplus_pos_le ha hL
  have hminus := sc_scalar_jminus_pos_le ha hL
  have hap : 0<a+1 := by linarith
  calc
    (Real.exp (a*L)-1)*(1-Real.exp (-((a+1)*L)))/(a*(a+1)) =
        ((Real.exp (a*L)-1)/a)*((1-Real.exp (-((a+1)*L)))/(a+1)) := by
      field_simp [ha.ne',hap.ne']
    _ ≤ (L*Real.exp (a*L))*(1/(a+1)) :=
      mul_le_mul hplus.2 hminus.2 hminus.1.le (by positivity)
    _ = L*Real.exp (a*L)/(a+1) := by ring

private theorem sc_cosh_rawfactor_combined {L a : ℝ} (hL : 0<L) (ha : 0<a) :
    (∫p:ℝ×ℝ,Real.cosh ((a+1/2)*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) =
      ((Real.exp (a*L)-1)*(1-Real.exp (-((a+1)*L)))/(a*(a+1))) /
        liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  rw [sc_cosh_rawfactor_eq hL ha]
  congr 1
  field_simp [ha.ne',show a+1≠0 by linarith]

private theorem sc_cosh_expectation_exact {L a : ℝ} (hL : 0<L) (ha : 0<a) :
    (∫p:ℝ×ℝ,Real.cosh ((a+1/2)*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) =
      Real.exp (a*L)*((1-Real.exp (-(a*L)))*(1-Real.exp (-((a+1)*L)))) /
        (liClockPairedEtaContiguousPartitionNormalizer L^2*(a*(a+1))) := by
  rw [sc_cosh_rawfactor_combined hL ha,sc_scalar_factor_eq ha hL,div_div]
  congr 1
  ring

private theorem sc_cosh_expectation_const_le {L a : ℝ} (hL : 0<L) (ha : 0<a) :
    (∫p:ℝ×ℝ,Real.cosh ((a+1/2)*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) ≤
      Real.exp (a*L)/(liClockPairedEtaContiguousPartitionNormalizer L^2*(a*(a+1))) := by
  rw [sc_cosh_rawfactor_combined hL ha]
  calc
    _≤(Real.exp (a*L)/(a*(a+1)))/liClockPairedEtaContiguousPartitionNormalizer L^2 :=
      div_le_div_of_nonneg_right (sc_scalar_constant_le ha hL) (sq_nonneg _)
    _=_ := by rw [div_div]; congr 1; ring

private theorem sc_cosh_expectation_polynomial_le {L a : ℝ} (hL : 0<L) (ha : 0<a) :
    (∫p:ℝ×ℝ,Real.cosh ((a+1/2)*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) ≤
      L*Real.exp (a*L)/(liClockPairedEtaContiguousPartitionNormalizer L^2*(a+1)) := by
  rw [sc_cosh_rawfactor_combined hL ha]
  calc
    _≤(L*Real.exp (a*L)/(a+1))/liClockPairedEtaContiguousPartitionNormalizer L^2 :=
      div_le_div_of_nonneg_right (sc_scalar_polynomial_le ha hL) (sq_nonneg _)
    _=_ := by rw [div_div]; congr 1; ring

private theorem sc_contiguous_real_bound {L theta tau : ℝ}
    (hL : 0<L) (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaContiguousBorelKernel L tau ≤
      Real.exp ((theta-1/2)*L+tau/theta) /
        (liClockPairedEtaContiguousPartitionNormalizer L^2*(theta^2-1/4)) := by
  have htheta0 : 0<theta := by linarith
  have hm:=sc_cosh_expectation_const_le hL (show 0<theta-1/2 by linarith)
  rw [show theta-1/2+1/2=theta by ring,
    show (theta-1/2)*((theta-1/2)+1)=theta^2-1/4 by ring] at hm
  have hm0 : 0≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2))
      ∂liClockPairedEtaContiguousSymmetrizedMeasure L) :=
    integral_nonneg (fun p=>(Real.cosh_pos _).le)
  calc
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.cosh (tau/theta) := sc_contiguous_le_cosh hL htheta0 htau
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.exp (tau/theta) := mul_le_mul_of_nonneg_left
          (sc_cosh_le_exp (div_nonneg htau htheta0.le)) hm0
    _≤(Real.exp ((theta-1/2)*L)/(liClockPairedEtaContiguousPartitionNormalizer L^2*(theta^2-1/4)))*
        Real.exp (tau/theta) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _=_ := by rw [Real.exp_add]; ring

private theorem sc_contiguous_real_polynomial_bound {L theta tau : ℝ}
    (hL : 0<L) (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaContiguousBorelKernel L tau ≤
      (L/(liClockPairedEtaContiguousPartitionNormalizer L^2*(theta+1/2)))*
        Real.exp ((theta-1/2)*L+tau/theta) := by
  have htheta0 : 0<theta := by linarith
  have hm:=sc_cosh_expectation_polynomial_le hL (show 0<theta-1/2 by linarith)
  rw [show theta-1/2+1/2=theta by ring,show theta-1/2+1=theta+1/2 by ring] at hm
  have hm0 : 0≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2))
      ∂liClockPairedEtaContiguousSymmetrizedMeasure L) :=
    integral_nonneg (fun p=>(Real.cosh_pos _).le)
  calc
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.cosh (tau/theta) := sc_contiguous_le_cosh hL htheta0 htau
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.exp (tau/theta) := mul_le_mul_of_nonneg_left
          (sc_cosh_le_exp (div_nonneg htau htheta0.le)) hm0
    _≤(L*Real.exp ((theta-1/2)*L)/(liClockPairedEtaContiguousPartitionNormalizer L^2*(theta+1/2)))*
        Real.exp (tau/theta) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _=_ := by rw [Real.exp_add]; ring

private theorem sc_actual_real_bound {N : ℕ} (hN : 0<N) {theta tau : ℝ}
    (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaPartitionBorelKernel N tau ≤
      Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta) /
        (liClockPairedEtaPartitionNormalizer N^2*(theta^2-1/4)) := by
  have hL:=sc_log_pos hN
  have hZA:=(liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have hZU:=(liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne'
  have hd : theta^2-1/4≠0 := by
    have hprod:=mul_pos (show 0<theta-1/2 by linarith) (show 0<theta+1/2 by linarith)
    nlinarith
  calc
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) tau :=
      liClockPairedEtaPartitionEndpoint_borel_le_ceiling hN htau
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      (Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta)/
        (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(theta^2-1/4))) :=
      mul_le_mul_of_nonneg_left (sc_contiguous_real_bound hL htheta htau) (sq_nonneg _)
    _=_ := by field_simp [hZA,hZU,hd]

private theorem sc_actual_real_polynomial_bound {N : ℕ} (hN : 0<N) {theta tau : ℝ}
    (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaPartitionBorelKernel N tau ≤
      (Real.log (2*(N:ℝ))/(liClockPairedEtaPartitionNormalizer N^2*(theta+1/2)))*
        Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta) := by
  have hL:=sc_log_pos hN
  have hZA:=(liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have hZU:=(liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne'
  have hd : theta+1/2≠0 := by linarith
  calc
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) tau :=
      liClockPairedEtaPartitionEndpoint_borel_le_ceiling hN htau
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      ((Real.log (2*(N:ℝ))/(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(theta+1/2)))*
        Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta)) :=
      mul_le_mul_of_nonneg_left (sc_contiguous_real_polynomial_bound hL htheta htau) (sq_nonneg _)
    _=_ := by field_simp [hZA,hZU,hd]

private theorem sc_scaled_exterior {c L tau K F : ℝ} (hc : (1/4:ℝ)<c)
    (hL : 0≤L) (htau : c*L≤tau) (hK : 0≤K)
    (hF : F≤K*Real.exp ((Real.sqrt c-1/2)*L+tau/Real.sqrt c)) :
    Real.exp (-2*tau)*F≤K*Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*L) := by
  calc
    _≤Real.exp (-2*tau)*(K*Real.exp ((Real.sqrt c-1/2)*L+tau/Real.sqrt c)) :=
      mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _=K*(Real.exp (-2*tau)*Real.exp ((Real.sqrt c-1/2)*L+tau/Real.sqrt c)) := by ring
    _=K*Real.exp (-2*tau+((Real.sqrt c-1/2)*L+tau/Real.sqrt c)) :=
      congrArg (fun x:ℝ=>K*x) (Real.exp_add (-2*tau) ((Real.sqrt c-1/2)*L+tau/Real.sqrt c)).symm
    _=K*Real.exp ((Real.sqrt c-1/2)*L+(1/Real.sqrt c-2)*tau) := by congr 2; ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.exp_le_exp.mpr
      calc
        _≤-2*(Real.sqrt c-1/2)^2*L := sc_exterior_exponent hc hL htau
        _=_ := by unfold liClockPairedEtaInfinitePartitionSupercriticalRate; ring

theorem norm_liClockPairedEtaPartitionBorelKernelComplex_supercritical_le_normalizer
    {c : ℝ} (hc : (1/4:ℝ)<c) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
        (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaPartitionNormalizer_pos hN
  have htheta:=sc_sqrt_half hc
  have hs:=Real.sq_sqrt (show 0≤c by linarith)
  have hd : 0<c-1/4 := by linarith
  have hb : ‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      (1/(liClockPairedEtaPartitionNormalizer N^2*(c-1/4)))*
        Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c) := by
    calc
      _≤liClockPairedEtaPartitionBorelKernel N ‖z‖ := sc_actual_radial hN z
      _≤Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c)/
          (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)) := by
        simpa only [hs] using sc_actual_real_bound hN htheta (norm_nonneg z)
      _=_ := by ring
  calc
    _≤(1/(liClockPairedEtaPartitionNormalizer N^2*(c-1/4)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) :=
      sc_scaled_exterior hc hL.le hz (by positivity) hb
    _=_ := by ring

theorem norm_liClockPairedEtaContiguousBorelKernelComplex_supercritical_le_normalizer
    {c : ℝ} (hc : (1/4:ℝ)<c) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
        (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaContiguousPartitionNormalizer_pos hL
  have htheta:=sc_sqrt_half hc
  have hs:=Real.sq_sqrt (show 0≤c by linarith)
  have hd : 0<c-1/4 := by linarith
  have hb : ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      (1/(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)))*
        Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c) := by
    calc
      _≤liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) ‖z‖ := sc_contiguous_radial hL z
      _≤Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c)/
          (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)) := by
        simpa only [hs] using sc_contiguous_real_bound hL htheta (norm_nonneg z)
      _=_ := by ring
  calc
    _≤(1/(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) :=
      sc_scaled_exterior hc hL.le hz (by positivity) hb
    _=_ := by ring

private theorem sc_first_mass_pos : 0<2-Real.sqrt 2 := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn:=Real.sqrt_nonneg 2
  nlinarith

private theorem sc_mass_square_le {Z : ℝ} (hZ : 2-Real.sqrt 2≤Z) :
    (2-Real.sqrt 2)^2≤Z^2 := by
  have hs:=sc_first_mass_pos
  nlinarith [mul_nonneg (show 0≤Z-(2-Real.sqrt 2) by linarith)
    (show 0≤Z+(2-Real.sqrt 2) by linarith)]

private theorem sc_normalizer_envelope_le {c Z : ℝ} (hc : (1/4:ℝ)<c)
    (hZ : 2-Real.sqrt 2≤Z) (N : ℕ) :
    Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
      (Z^2*(c-1/4)) ≤ liClockPairedEtaInfinitePartitionSupercriticalEnvelope c N := by
  unfold liClockPairedEtaInfinitePartitionSupercriticalEnvelope
  have hd : 0<c-1/4 := by linarith
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le
    (mul_pos (sq_pos_of_pos sc_first_mass_pos) hd)
    (mul_le_mul_of_nonneg_right (sc_mass_square_le hZ) hd.le)

theorem liClockPairedEtaInfinitePartitionSupercriticalWindow_norm_le
    {c : ℝ} (hc : (1/4:ℝ)<c) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      liClockPairedEtaInfinitePartitionSupercriticalEnvelope c N ∧
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      liClockPairedEtaInfinitePartitionSupercriticalEnvelope c N := by
  exact ⟨(norm_liClockPairedEtaPartitionBorelKernelComplex_supercritical_le_normalizer hc hN hz).trans
      (sc_normalizer_envelope_le hc (liClockPairedEtaPartitionNormalizer_ge_first hN) N),
    (norm_liClockPairedEtaContiguousBorelKernelComplex_supercritical_le_normalizer hc hN hz).trans
      (sc_normalizer_envelope_le hc (liClockPairedEtaContiguousPartitionNormalizer_ge_first hN) N)⟩

private theorem sc_polynomial_coefficient_le {c L Z : ℝ} (hc : (1/4:ℝ)<c)
    (hL : 0≤L) (hZ : 2-Real.sqrt 2≤Z) :
    L/(Z^2*(Real.sqrt c+1/2))≤2*L/(2-Real.sqrt 2)^2 := by
  have hs:=sc_first_mass_pos
  have htheta:=sc_sqrt_half hc
  have hsq:=sc_mass_square_le hZ
  have hden : (2-Real.sqrt 2)^2≤Z^2*(Real.sqrt c+1/2) := by
    have hm:=mul_nonneg (sq_nonneg Z) (show 0≤Real.sqrt c+1/2-1 by linarith)
    nlinarith
  calc
    _≤L/(2-Real.sqrt 2)^2 :=
      div_le_div_of_nonneg_left hL (sq_pos_of_pos hs) hden
    _≤2*(L/(2-Real.sqrt 2)^2) := by
      have hq : 0≤L/(2-Real.sqrt 2)^2 := div_nonneg hL (sq_nonneg _)
      linarith
    _=_ := by ring

private theorem sc_actual_complex_polynomial_bound {c : ℝ} (hc : (1/4:ℝ)<c)
    {N : ℕ} (hN : 0<N) {z : ℂ} (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      (Real.log (2*(N:ℝ))/(liClockPairedEtaPartitionNormalizer N^2*(Real.sqrt c+1/2)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaPartitionNormalizer_pos hN
  have htheta:=sc_sqrt_half hc
  apply sc_scaled_exterior hc hL.le hz (by positivity)
  exact (sc_actual_radial hN z).trans
    (sc_actual_real_polynomial_bound hN htheta (norm_nonneg z))

private theorem sc_contiguous_complex_polynomial_bound {c : ℝ} (hc : (1/4:ℝ)<c)
    {N : ℕ} (hN : 0<N) {z : ℂ} (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      (Real.log (2*(N:ℝ))/(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(Real.sqrt c+1/2)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaContiguousPartitionNormalizer_pos hL
  have htheta:=sc_sqrt_half hc
  apply sc_scaled_exterior hc hL.le hz (by positivity)
  exact (sc_contiguous_radial hL z).trans
    (sc_contiguous_real_polynomial_bound hL htheta (norm_nonneg z))

theorem liClockPairedEtaInfinitePartitionSupercriticalWindow_norm_le_polynomial
    {c : ℝ} (hc : (1/4:ℝ)<c) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    let bound := (2*Real.log (2*(N:ℝ))/(2-Real.sqrt 2)^2)*
      Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ)))
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖≤bound ∧
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖≤bound := by
  constructor
  · exact (sc_actual_complex_polynomial_bound hc hN hz).trans
      (mul_le_mul_of_nonneg_right
        (sc_polynomial_coefficient_le hc (sc_log_pos hN).le (liClockPairedEtaPartitionNormalizer_ge_first hN))
        (Real.exp_pos _).le)
  · exact (sc_contiguous_complex_polynomial_bound hc hN hz).trans
      (mul_le_mul_of_nonneg_right
        (sc_polynomial_coefficient_le hc (sc_log_pos hN).le (liClockPairedEtaContiguousPartitionNormalizer_ge_first hN))
        (Real.exp_pos _).le)

private def sc_finite_numerator (theta L : ℝ) : ℝ :=
  (1-Real.exp (-((theta-1/2)*L)))*(1-Real.exp (-((theta+1/2)*L)))

private theorem sc_finite_numerator_pos_lt_one {theta L : ℝ}
    (htheta : (1/2:ℝ)<theta) (hL : 0<L) :
    0<sc_finite_numerator theta L ∧ sc_finite_numerator theta L<1 := by
  have h:=sc_scalar_numerator_pos_lt_one (show 0<theta-1/2 by linarith) hL
  rw [show theta-1/2+1=theta+1/2 by ring] at h
  exact h

private theorem sc_cosh_expectation_refined {theta L : ℝ}
    (htheta : (1/2:ℝ)<theta) (hL : 0<L) :
    (∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L) =
      Real.exp ((theta-1/2)*L)*sc_finite_numerator theta L /
        (liClockPairedEtaContiguousPartitionNormalizer L^2*(theta^2-1/4)) := by
  have h:=sc_cosh_expectation_exact hL (show 0<theta-1/2 by linarith)
  rw [show theta-1/2+1/2=theta by ring,
    show (theta-1/2)*((theta-1/2)+1)=theta^2-1/4 by ring,
    show theta-1/2+1=theta+1/2 by ring] at h
  exact h

private theorem sc_contiguous_real_refined_bound {L theta tau : ℝ}
    (hL : 0<L) (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaContiguousBorelKernel L tau ≤
      sc_finite_numerator theta L*Real.exp ((theta-1/2)*L+tau/theta) /
        (liClockPairedEtaContiguousPartitionNormalizer L^2*(theta^2-1/4)) := by
  have htheta0 : 0<theta := by linarith
  have hm0 : 0≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2))
      ∂liClockPairedEtaContiguousSymmetrizedMeasure L) :=
    integral_nonneg (fun p=>(Real.cosh_pos _).le)
  calc
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.cosh (tau/theta) := sc_contiguous_le_cosh hL htheta0 htau
    _≤(∫p:ℝ×ℝ,Real.cosh (theta*(p.1-p.2)) ∂liClockPairedEtaContiguousSymmetrizedMeasure L)*
        Real.exp (tau/theta) := mul_le_mul_of_nonneg_left
          (sc_cosh_le_exp (div_nonneg htau htheta0.le)) hm0
    _=_ := by rw [sc_cosh_expectation_refined htheta hL,Real.exp_add]; ring

private theorem sc_actual_real_refined_bound {N : ℕ} (hN : 0<N) {theta tau : ℝ}
    (htheta : (1/2:ℝ)<theta) (htau : 0≤tau) :
    liClockPairedEtaPartitionBorelKernel N tau ≤
      sc_finite_numerator theta (Real.log (2*(N:ℝ)))*
        Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta) /
          (liClockPairedEtaPartitionNormalizer N^2*(theta^2-1/4)) := by
  have hL:=sc_log_pos hN
  have hZA:=(liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have hZU:=(liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne'
  have hd : theta^2-1/4≠0 := by
    have hprod:=mul_pos (show 0<theta-1/2 by linarith) (show 0<theta+1/2 by linarith)
    nlinarith
  calc
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) tau :=
      liClockPairedEtaPartitionEndpoint_borel_le_ceiling hN htau
    _≤(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      (sc_finite_numerator theta (Real.log (2*(N:ℝ)))*
        Real.exp ((theta-1/2)*Real.log (2*(N:ℝ))+tau/theta)/
          (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(theta^2-1/4))) :=
      mul_le_mul_of_nonneg_left (sc_contiguous_real_refined_bound hL htheta htau) (sq_nonneg _)
    _=_ := by field_simp [hZA,hZU,hd]

private theorem sc_actual_complex_refined_bound {c : ℝ} (hc : (1/4:ℝ)<c)
    {N : ℕ} (hN : 0<N) {z : ℂ} (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
          (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaPartitionNormalizer_pos hN
  have htheta:=sc_sqrt_half hc
  have hP:=(sc_finite_numerator_pos_lt_one htheta hL).1
  have hs:=Real.sq_sqrt (show 0≤c by linarith)
  have hd : 0<c-1/4 := by linarith
  have hb : ‖liClockPairedEtaPartitionBorelKernelComplex N z‖ ≤
      (sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))/
        (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)))*
          Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c) := by
    calc
      _≤liClockPairedEtaPartitionBorelKernel N ‖z‖ := sc_actual_radial hN z
      _ ≤ sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))*
        Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c)/
          (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)) := by
        simpa only [hs] using sc_actual_real_refined_bound hN htheta (norm_nonneg z)
      _=_ := by ring
  calc
    _≤(sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))/
        (liClockPairedEtaPartitionNormalizer N^2*(c-1/4)))*
          Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) :=
      sc_scaled_exterior hc hL.le hz (by positivity) hb
    _=_ := by ring

private theorem sc_contiguous_complex_refined_bound {c : ℝ} (hc : (1/4:ℝ)<c)
    {N : ℕ} (hN : 0<N) {z : ℂ} (hz : c*Real.log (2*(N:ℝ))≤‖z‖) :
    Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))*
        Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) /
          (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)) := by
  have hL:=sc_log_pos hN
  have hZ:=liClockPairedEtaContiguousPartitionNormalizer_pos hL
  have htheta:=sc_sqrt_half hc
  have hP:=(sc_finite_numerator_pos_lt_one htheta hL).1
  have hs:=Real.sq_sqrt (show 0≤c by linarith)
  have hd : 0<c-1/4 := by linarith
  have hb : ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖ ≤
      (sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))/
        (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)))*
          Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c) := by
    calc
      _≤liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) ‖z‖ := sc_contiguous_radial hL z
      _ ≤ sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))*
        Real.exp ((Real.sqrt c-1/2)*Real.log (2*(N:ℝ))+‖z‖/Real.sqrt c)/
          (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)) := by
        simpa only [hs] using sc_contiguous_real_refined_bound hL htheta (norm_nonneg z)
      _=_ := by ring
  calc
    _≤(sc_finite_numerator (Real.sqrt c) (Real.log (2*(N:ℝ)))/
        (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*(c-1/4)))*
          Real.exp (-liClockPairedEtaInfinitePartitionSupercriticalRate c*Real.log (2*(N:ℝ))) :=
      sc_scaled_exterior hc hL.le hz (by positivity) hb
    _=_ := by ring

theorem liClockPairedEtaInfinitePartitionSupercriticalWindow_eventually_uniform
    {c : ℝ} (hc : (1/4:ℝ)<c) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, c*Real.log (2*(N:ℝ))≤‖z‖ →
      Real.exp (-2*‖z‖)*‖liClockPairedEtaPartitionBorelKernelComplex N z‖<epsilon ∧
      Real.exp (-2*‖z‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z‖<epsilon := by
  have he:=(tendsto_liClockPairedEtaInfinitePartitionSupercriticalEnvelope_zero hc).eventually
    (eventually_lt_nhds hepsilon)
  filter_upwards [eventually_ge_atTop 1,he] with N hN heN
  intro z hz
  have h:=liClockPairedEtaInfinitePartitionSupercriticalWindow_norm_le hc (by omega : 0<N) hz
  exact ⟨h.1.trans_lt heN,h.2.trans_lt heN⟩

theorem liClockPairedEtaInfinitePartitionSupercriticalWindow_qualified
    {c : ℝ} (hc : (1/4:ℝ)<c) {nu : ℕ→ℕ} {z : ℕ→ℂ}
    (hnu : Tendsto nu atTop atTop)
    (hz : ∀ᶠ n : ℕ in atTop, c*Real.log (2*(nu n:ℝ))≤‖z n‖) :
    Tendsto (fun n : ℕ=>Real.exp (-2*‖z n‖)*‖liClockPairedEtaPartitionBorelKernelComplex (nu n) (z n)‖)
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ=>Real.exp (-2*‖z n‖)*
      ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(nu n:ℝ))) (z n)‖)
      atTop (nhds 0) := by
  have he : Tendsto (fun n:ℕ=>liClockPairedEtaInfinitePartitionSupercriticalEnvelope c (nu n))
      atTop (nhds 0) := (tendsto_liClockPairedEtaInfinitePartitionSupercriticalEnvelope_zero hc).comp hnu
  have hn:=hnu.eventually (eventually_ge_atTop 1)
  have hb : ∀ᶠ n:ℕ in atTop,
      Real.exp (-2*‖z n‖)*‖liClockPairedEtaPartitionBorelKernelComplex (nu n) (z n)‖≤
        liClockPairedEtaInfinitePartitionSupercriticalEnvelope c (nu n) ∧
      Real.exp (-2*‖z n‖)*‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(nu n:ℝ))) (z n)‖≤
        liClockPairedEtaInfinitePartitionSupercriticalEnvelope c (nu n) := by
    filter_upwards [hn,hz] with n hn hz
    exact liClockPairedEtaInfinitePartitionSupercriticalWindow_norm_le hc (by omega : 0<nu n) hz
  constructor
  · exact squeeze_zero' (Eventually.of_forall fun n=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (hb.mono fun _ h=>h.1) he
  · exact squeeze_zero' (Eventually.of_forall fun n=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (hb.mono fun _ h=>h.2) he

private theorem sc_actual_nonneg {N : ℕ} (hN : 0<N) (t : ℝ) :
    0≤liClockPairedEtaPartitionBorelKernel N t := by
  rw [liClockPairedEtaPartitionBorelKernel_eq_tsum]
  apply tsum_nonneg
  intro j
  exact div_nonneg (mul_nonneg (liClockPairedEtaSymmetrizedEvenMoment_pos hN j).le
    (by rw [pow_mul]; positivity)) (sq_nonneg _)

private theorem sc_reference_scaled_limit :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*liClockPairedEtaHalfLineBorelKernel t)
      atTop (nhds (1/2)) := by
  have h:=tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite_scaled.add
    tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled
  have he : (1-liClockPairedEtaInfinitePartitionComparisonLimit)/2+
      liClockPairedEtaInfinitePartitionComparisonLimit/2=(1/2:ℝ) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards with t
  ring

theorem liClockPairedEtaInfinitePartitionSupercriticalRay_finite_scaled
    {c : ℝ} (hc : (1/4:ℝ)<c) :
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ));
      Real.exp (-2*t)*liClockPairedEtaPartitionBorelKernel N t) atTop (nhds 0) ∧
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ));
      Real.exp (-2*t)*liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t)
      atTop (nhds 0) := by
  have h:=liClockPairedEtaInfinitePartitionSupercriticalWindow_qualified hc
    (nu:=id) (z:=fun N:ℕ=>((c*Real.log (2*(N:ℝ)):ℝ):ℂ)) tendsto_id
    (Eventually.of_forall fun N=>by
      simpa only [id_eq,Complex.norm_real,Real.norm_eq_abs] using le_abs_self (c*Real.log (2*(N:ℝ))))
  constructor
  · apply h.1.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : 0<N := by omega
    have ht0 : 0≤c*Real.log (2*(N:ℝ)) := mul_nonneg (by linarith) (sc_log_pos hN0).le
    dsimp only [id_eq]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,
      liClockPairedEtaPartitionBorelKernelComplex_ofReal hN0,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sc_actual_nonneg hN0 _)]
  · apply h.2.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : 0<N := by omega
    have hL:=sc_log_pos hN0
    have ht0 : 0≤c*Real.log (2*(N:ℝ)) := mul_nonneg (by linarith) hL.le
    have hu0 : 0≤liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ)))
        (c*Real.log (2*(N:ℝ))) := (by norm_num : (0:ℝ)≤1).trans
      (liClockPairedEtaContiguousBorelKernel_ge_one hL _)
    dsimp only [id_eq]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,
      liClockPairedEtaContiguousBorelKernelComplex_ofReal hL,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu0]

theorem liClockPairedEtaInfinitePartitionSupercriticalRay_signed_error
    {c : ℝ} (hc : (1/4:ℝ)<c) :
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      (liClockPairedEtaPartitionBorelKernel N t-liClockPairedEtaInfinitePartitionBorelKernel t))
      atTop (nhds (-liClockPairedEtaInfinitePartitionComparisonLimit/2)) ∧
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      (liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-liClockPairedEtaHalfLineBorelKernel t))
      atTop (nhds (-1/2)) := by
  have hf:=liClockPairedEtaInfinitePartitionSupercriticalRay_finite_scaled hc
  have ht : Tendsto (fun N:ℕ=>c*Real.log (2*(N:ℝ))) atTop atTop :=
    sc_log_tendsto.const_mul_atTop (by linarith)
  constructor
  · have h:=hf.1.sub (tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled.comp ht)
    have he : 0-liClockPairedEtaInfinitePartitionComparisonLimit/2 =
        -liClockPairedEtaInfinitePartitionComparisonLimit/2 := by ring
    rw [he] at h
    apply h.congr'
    filter_upwards with N
    dsimp only [Function.comp_apply]
    ring
  · have h:=hf.2.sub (sc_reference_scaled_limit.comp ht)
    have he : (0:ℝ)-(1/2:ℝ)=(-1:ℝ)/2 := by ring
    rw [he] at h
    apply h.congr'
    filter_upwards with N
    dsimp only [Function.comp_apply]
    ring

theorem liClockPairedEtaInfinitePartitionSupercriticalRay_absolute_error
    {c : ℝ} (hc : (1/4:ℝ)<c) :
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      |liClockPairedEtaPartitionBorelKernel N t-liClockPairedEtaInfinitePartitionBorelKernel t|)
      atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2)) ∧
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      |liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-liClockPairedEtaHalfLineBorelKernel t|)
      atTop (nhds (1/2)) := by
  have hs:=liClockPairedEtaInfinitePartitionSupercriticalRay_signed_error hc
  have hl:=liClockPairedEtaInfinitePartitionComparisonLimit_pos
  constructor
  · have h:=hs.1.abs
    have he : |-liClockPairedEtaInfinitePartitionComparisonLimit/2|=
        liClockPairedEtaInfinitePartitionComparisonLimit/2 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [he] at h
    apply h.congr'
    filter_upwards with N
    dsimp only
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  · have h:=hs.2.abs
    have he : |(-1:ℝ)/2|=(1/2:ℝ) := by norm_num
    rw [he] at h
    apply h.congr'
    filter_upwards with N
    dsimp only
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]

private theorem sc_complex_norm_error_limits {c : ℝ} (hc : (1/4:ℝ)<c) :
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      ‖liClockPairedEtaPartitionBorelKernelComplex N (t:ℂ)-
        liClockPairedEtaInfinitePartitionBorelKernelComplex (t:ℂ)‖)
      atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2)) ∧
    Tendsto (fun N : ℕ=>let t:=c*Real.log (2*(N:ℝ)); Real.exp (-2*t)*
      ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) (t:ℂ)-
        liClockPairedEtaHalfLineBorelKernelComplex (t:ℂ)‖)
      atTop (nhds (1/2)) := by
  have h:=liClockPairedEtaInfinitePartitionSupercriticalRay_absolute_error hc
  constructor
  · apply h.1.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : 0<N := by omega
    dsimp only
    rw [liClockPairedEtaPartitionBorelKernelComplex_ofReal hN0,
      liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
  · apply h.2.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : 0<N := by omega
    dsimp only
    rw [liClockPairedEtaContiguousBorelKernelComplex_ofReal (sc_log_pos hN0),
      liClockPairedEtaHalfLineBorelKernelComplex_ofReal,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]

theorem liClockPairedEtaInfinitePartitionSupercriticalRay_eventually_error_floor
    {c : ℝ} (hc : (1/4:ℝ)<c) :
    ∀ᶠ N : ℕ in atTop, 0<N ∧ let t:=c*Real.log (2*(N:ℝ));
      liClockPairedEtaInfinitePartitionComparisonLimit/4 ≤ Real.exp (-2*t)*
        ‖liClockPairedEtaPartitionBorelKernelComplex N (t:ℂ)-
          liClockPairedEtaInfinitePartitionBorelKernelComplex (t:ℂ)‖ ∧
      (1/4:ℝ) ≤ Real.exp (-2*t)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) (t:ℂ)-
          liClockPairedEtaHalfLineBorelKernelComplex (t:ℂ)‖ := by
  have h:=sc_complex_norm_error_limits hc
  have hl:=liClockPairedEtaInfinitePartitionComparisonLimit_pos
  have ha:=h.1.eventually (eventually_gt_nhds (show
    liClockPairedEtaInfinitePartitionComparisonLimit/4<liClockPairedEtaInfinitePartitionComparisonLimit/2 by linarith))
  have hu:=h.2.eventually (eventually_gt_nhds (by norm_num : (1/4:ℝ)<1/2))
  filter_upwards [eventually_ge_atTop 1,ha,hu] with N hN ha hu
  exact ⟨by omega,ha.le,hu.le⟩

theorem liClockPairedEtaInfinitePartitionSupercriticalDisk_eventually_interior_witness
    {C : ℝ} (hC : (1/4:ℝ)<C) :
    ∃ d : ℝ, (1/4:ℝ)<d ∧ d<C ∧ ∀ᶠ N : ℕ in atTop,
      0<N ∧ let z : ℂ:=((d*Real.log (2*(N:ℝ)):ℝ):ℂ);
        ‖z‖<C*Real.log (2*(N:ℝ)) ∧
        liClockPairedEtaInfinitePartitionComparisonLimit/4 ≤ Real.exp (-2*‖z‖)*
          ‖liClockPairedEtaPartitionBorelKernelComplex N z-liClockPairedEtaInfinitePartitionBorelKernelComplex z‖ ∧
        (1/4:ℝ) ≤ Real.exp (-2*‖z‖)*
          ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-liClockPairedEtaHalfLineBorelKernelComplex z‖ := by
  let d : ℝ:=(C+1/4)/2
  have hd : (1/4:ℝ)<d := by dsimp [d]; linarith
  have hdC : d<C := by dsimp [d]; linarith
  refine ⟨d,hd,hdC,?_⟩
  filter_upwards [liClockPairedEtaInfinitePartitionSupercriticalRay_eventually_error_floor hd]
    with N hN
  have hL:=sc_log_pos hN.1
  have ht : 0≤d*Real.log (2*(N:ℝ)) := mul_nonneg (by linarith) hL.le
  have hz : ‖((d*Real.log (2*(N:ℝ)):ℝ):ℂ)‖=d*Real.log (2*(N:ℝ)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  refine ⟨hN.1,?_⟩
  dsimp only
  rw [hz]
  exact ⟨mul_lt_mul_of_pos_right hdC hL,hN.2.1,hN.2.2⟩

theorem liClockPairedEtaInfinitePartitionSupercriticalDisk_no_vanishing_closed_bound
    {C : ℝ} (hC : (1/4:ℝ)<C) :
    (¬∃ e : ℕ→ℝ, Tendsto e atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ z : ℂ, ‖z‖≤C*Real.log (2*(N:ℝ)) → Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaPartitionBorelKernelComplex N z-liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤e N) ∧
    (¬∃ e : ℕ→ℝ, Tendsto e atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ z : ℂ, ‖z‖≤C*Real.log (2*(N:ℝ)) → Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-liClockPairedEtaHalfLineBorelKernelComplex z‖≤e N) := by
  obtain ⟨d,_,_,hw⟩:=
    liClockPairedEtaInfinitePartitionSupercriticalDisk_eventually_interior_witness hC
  constructor
  · rintro ⟨e,he,hbound⟩
    have hsmall:=he.eventually (eventually_lt_nhds (show
      (0:ℝ)<liClockPairedEtaInfinitePartitionComparisonLimit/4 by
        have := liClockPairedEtaInfinitePartitionComparisonLimit_pos; linarith))
    obtain ⟨N,hwN,hboundN,heN⟩:=(hw.and (hbound.and hsmall)).exists
    have hcap:=hboundN ((d*Real.log (2*(N:ℝ)):ℝ):ℂ) hwN.2.1.le
    exact (not_lt_of_ge (hwN.2.2.1.trans hcap)) heN
  · rintro ⟨e,he,hbound⟩
    have hsmall:=he.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4))
    obtain ⟨N,hwN,hboundN,heN⟩:=(hw.and (hbound.and hsmall)).exists
    have hcap:=hboundN ((d*Real.log (2*(N:ℝ)):ℝ):ℂ) hwN.2.1.le
    exact (not_lt_of_ge (hwN.2.2.2.trans hcap)) heN

theorem liClockPairedEtaInfinitePartitionSupercriticalDisk_no_vanishing_open_bound
    {C : ℝ} (hC : (1/4:ℝ)<C) :
    (¬∃ e : ℕ→ℝ, Tendsto e atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ z : ℂ, ‖z‖<C*Real.log (2*(N:ℝ)) → Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaPartitionBorelKernelComplex N z-liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤e N) ∧
    (¬∃ e : ℕ→ℝ, Tendsto e atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ z : ℂ, ‖z‖<C*Real.log (2*(N:ℝ)) → Real.exp (-2*‖z‖)*
        ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-liClockPairedEtaHalfLineBorelKernelComplex z‖≤e N) := by
  obtain ⟨d,_,_,hw⟩:=
    liClockPairedEtaInfinitePartitionSupercriticalDisk_eventually_interior_witness hC
  constructor
  · rintro ⟨e,he,hbound⟩
    have hsmall:=he.eventually (eventually_lt_nhds (show
      (0:ℝ)<liClockPairedEtaInfinitePartitionComparisonLimit/4 by
        have := liClockPairedEtaInfinitePartitionComparisonLimit_pos; linarith))
    obtain ⟨N,hwN,hboundN,heN⟩:=(hw.and (hbound.and hsmall)).exists
    have hcap:=hboundN ((d*Real.log (2*(N:ℝ)):ℝ):ℂ) hwN.2.1
    exact (not_lt_of_ge (hwN.2.2.1.trans hcap)) heN
  · rintro ⟨e,he,hbound⟩
    have hsmall:=he.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4))
    obtain ⟨N,hwN,hboundN,heN⟩:=(hw.and (hbound.and hsmall)).exists
    have hcap:=hboundN ((d*Real.log (2*(N:ℝ)):ℝ):ℂ) hwN.2.1
    exact (not_lt_of_ge (hwN.2.2.2.trans hcap)) heN

end
end RHTower
