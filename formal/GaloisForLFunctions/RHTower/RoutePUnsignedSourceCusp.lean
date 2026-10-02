import GaloisForLFunctions.RHTower.DivisorContinuousUnitMoment
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Exact arithmetic cusps of the unsigned Route-P dilation source

The multiplicative midpoint minor has right slope
`sqrt(n) * U(n) * (log(n) - tau(n) + 2*gamma)` at every integer n >= 2.
The unsigned head is strictly positive there. Prime centers and powers of two
therefore give opposite signs on arbitrarily short windows arbitrarily late.

This excludes eventual continuous log-concavity and its opposite midpoint
inequality for the actual kernel. It does not decide an arithmetic-only
prime-grid pair inequality, bound the joint signed action, or settle RH.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Set
namespace RHTower

theorem routeP_unit_head_nat_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < divisorContinuousUnitHead N := by
  have hfirst : 0 < primeFreeDivisorDefect 1 := by
    have h := divisorContinuousUnitHead_pos_first
      (x := (3/2 : ℝ)) (by constructor <;> norm_num)
    rw [divisorContinuousUnitHead_between (k := 1) le_rfl (by norm_num) (by norm_num)] at h
    have hz : divisorUnsignedDilationChannel 1 1 = 0 := by simp [divisorUnsignedDilationChannel]
    rw [hz, zero_add] at h
    have hs : 0 ≤ Real.sqrt (3/2 : ℝ)-Real.sqrt 1 := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
    exact pos_of_mul_pos_right h (by simpa using hs)
  rw [divisorContinuousUnitHead_nat]
  have he : divisorUnsignedDilationChannel N 1 =
      ∑ k ∈ Icc 1 (N-1), primeFreeDivisorDefect k * HTGeometry.halfOrderAbelStep 0 k := by
    unfold divisorUnsignedDilationChannel
    simp only [Nat.div_one, HTGeometry.halfOrderAbelStep, Nat.zero_add, mul_comm]
  rw [he, HTGeometry.sum_mul_eq_partial_mul_diff_ring]
  have hnon (k : ℕ) : 0 ≤ (∑ n ∈ Icc 1 k, primeFreeDivisorDefect n) *
      (HTGeometry.halfOrderAbelStep 0 k-HTGeometry.halfOrderAbelStep 0 (k+1)) :=
    mul_nonneg (sum_primeFreeDivisorDefect_nonneg k)
      (sub_nonneg.mpr (HTGeometry.halfOrderAbelStep_antitone 0 (by omega)))
  have hgap : 0 < HTGeometry.halfOrderAbelStep 0 1-HTGeometry.halfOrderAbelStep 0 2 := by
    rw [show (2:ℕ)=1+1 by rfl, HTGeometry.halfOrderAbelStep_gap_eq]
    positivity
  have hsingle := single_le_sum (fun k _ => hnon k)
    (show 1 ∈ Finset.Icc 1 (N-1) from mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hpos : 0 < ∑ k ∈ Icc 1 (N-1), (∑ n ∈ Icc 1 k, primeFreeDivisorDefect n) *
      (HTGeometry.halfOrderAbelStep 0 k-HTGeometry.halfOrderAbelStep 0 (k+1)) := by
    apply lt_of_lt_of_le _ hsingle
    simpa using mul_pos hfirst hgap
  exact add_pos_of_pos_of_nonneg hpos (mul_nonneg
    (sum_primeFreeDivisorDefect_nonneg (N-1)) (HTGeometry.halfOrderAbelStep_nonneg 0 _))

private theorem unit_left_cell {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx0 : (n-1 : ℕ) ≤ x) (hxn : x ≤ n) :
    divisorContinuousUnitHead x = divisorContinuousUnitHead n +
      (Real.sqrt x-Real.sqrt n)*primeFreeDivisorDefect (n-1) := by
  have hn1 : n-1+1=n := by omega
  have hx := divisorContinuousUnitHead_between (k := n-1) (by omega) hx0 (by simpa [hn1] using hxn)
  have he := divisorContinuousUnitHead_between (k := n-1) (by omega)
    (x := n) (by exact_mod_cast Nat.sub_le n 1) (by simp [hn1])
  rw [hx, he]
  ring

private theorem unit_right_cell {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hnx : (n : ℝ) ≤ x) (hx1 : x ≤ (n+1 : ℕ)) :
    divisorContinuousUnitHead x = divisorContinuousUnitHead n +
      (Real.sqrt x-Real.sqrt n)*primeFreeDivisorDefect n := by
  rw [divisorContinuousUnitHead_between hn hnx hx1, divisorContinuousUnitHead_nat]

def routePUnitMultiplicativeMinor (n : ℕ) (t : ℝ) : ℝ :=
  divisorContinuousUnitHead ((n:ℝ)*Real.exp (-2*t)) *
    divisorContinuousUnitHead ((n:ℝ)*Real.exp (2*t)) - divisorContinuousUnitHead n ^ 2

private def cuspModel (n : ℕ) (t : ℝ) : ℝ :=
  (divisorContinuousUnitHead n + Real.sqrt n*primeFreeDivisorDefect (n-1)*(Real.exp (-t)-1)) *
    (divisorContinuousUnitHead n + Real.sqrt n*primeFreeDivisorDefect n*(Real.exp t-1)) -
      divisorContinuousUnitHead n ^ 2

private theorem cuspModel_deriv {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (cuspModel n)
      (Real.sqrt n*divisorContinuousUnitHead n*primeFreeDivisorIncrement n) 0 := by
  have hminus := (((hasDerivAt_id (0:ℝ)).neg.exp.sub_const 1).const_mul
    (Real.sqrt n*primeFreeDivisorDefect (n-1))).const_add (divisorContinuousUnitHead n)
  have hplus := (((hasDerivAt_id (0:ℝ)).exp.sub_const 1).const_mul
    (Real.sqrt n*primeFreeDivisorDefect n)).const_add (divisorContinuousUnitHead n)
  have h : HasDerivAt (cuspModel n)
      (-(Real.sqrt n*primeFreeDivisorDefect (n-1))*divisorContinuousUnitHead n +
        divisorContinuousUnitHead n*(Real.sqrt n*primeFreeDivisorDefect n)) 0 := by
    have hr := (hminus.mul hplus).sub_const (divisorContinuousUnitHead n ^ 2)
    change HasDerivAt (cuspModel n) _ (0:ℝ) at hr
    simpa only [id_eq,Pi.neg_apply,neg_zero,Real.exp_zero,sub_self,mul_zero,add_zero,
      mul_one,mul_neg,one_mul] using hr
  have he : Real.sqrt n*divisorContinuousUnitHead n*primeFreeDivisorIncrement n =
      -(Real.sqrt n*primeFreeDivisorDefect (n-1))*divisorContinuousUnitHead n +
        divisorContinuousUnitHead n*(Real.sqrt n*primeFreeDivisorDefect n) := by
    rw [← primeFreeDivisorDefect_sub_pred hn]
    ring
  rw [he]
  exact h

private theorem minor_eq_model {n : ℕ} (hn : 2 ≤ n) :
    routePUnitMultiplicativeMinor n =ᶠ[𝓝[>] (0:ℝ)] cuspModel n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlo : ((n-1:ℕ):ℝ)<n := by exact_mod_cast (by omega : n-1<n)
  have hhi : (n:ℝ)<(n+1:ℕ) := by exact_mod_cast Nat.lt_succ_self n
  have hm : Tendsto (fun t : ℝ => (n:ℝ)*Real.exp (-2*t)) (𝓝[>] 0) (𝓝 (n:ℝ)) := by
    have hc : Continuous (fun t : ℝ => (n:ℝ)*Real.exp (-2*t)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun t : ℝ => (n:ℝ)*Real.exp (2*t)) (𝓝[>] 0) (𝓝 (n:ℝ)) := by
    have hc : Continuous (fun t : ℝ => (n:ℝ)*Real.exp (2*t)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hm.eventually (eventually_gt_nhds hlo), hp.eventually (eventually_lt_nhds hhi),
    self_mem_nhdsWithin] with t htlo hthi ht
  have ht0 : 0<t := ht
  have hl : (n:ℝ)*Real.exp (-2*t) ≤ n := by
    nlinarith [Real.exp_le_one_iff.mpr (by linarith : -2*t≤0)]
  have hr : (n:ℝ) ≤ n*Real.exp (2*t) := by
    nlinarith [Real.one_le_exp (by linarith : 0≤2*t)]
  have hsm : Real.sqrt ((n:ℝ)*Real.exp (-2*t)) = Real.sqrt n*Real.exp (-t) := by
    rw [Real.sqrt_mul hnR.le, ← Real.exp_half]
    congr 2
    ring
  have hsp : Real.sqrt ((n:ℝ)*Real.exp (2*t)) = Real.sqrt n*Real.exp t := by
    rw [Real.sqrt_mul hnR.le, ← Real.exp_half]
    congr 2
    ring
  rw [routePUnitMultiplicativeMinor, unit_left_cell hn htlo.le hl,
    unit_right_cell (by omega : 1≤n) hr hthi.le, hsm, hsp, cuspModel]
  ring

theorem routeP_unit_multiplicative_minor_cusp {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt (routePUnitMultiplicativeMinor n)
      (Real.sqrt n*divisorContinuousUnitHead n*primeFreeDivisorIncrement n) (Ioi 0) 0 := by
  apply (cuspModel_deriv (by omega : 1≤n)).hasDerivWithinAt.congr_of_eventuallyEq (minor_eq_model hn)
  simp [routePUnitMultiplicativeMinor,cuspModel,pow_two]

theorem routeP_unit_multiplicative_minor_slope {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun t : ℝ => routePUnitMultiplicativeMinor n t / t) (𝓝[>] 0)
      (𝓝 (Real.sqrt n*divisorContinuousUnitHead n*primeFreeDivisorIncrement n)) := by
  have h := (cuspModel_deriv (by omega : 1≤n)).tendsto_slope_zero_right
  have hz : cuspModel n 0 = 0 := by simp [cuspModel,pow_two]
  simp only [zero_add,hz,sub_zero,smul_eq_mul,← div_eq_inv_mul] at h
  apply h.congr'
  filter_upwards [minor_eq_model hn] with t ht
  rw [ht]

theorem routeP_unit_minor_eventually_pos {n : ℕ} (hn : 2 ≤ n)
    (hinc : 0 < primeFreeDivisorIncrement n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < routePUnitMultiplicativeMinor n t := by
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n))
  have hderiv := mul_pos (mul_pos hroot (routeP_unit_head_nat_pos hn)) hinc
  have hs := (routeP_unit_multiplicative_minor_slope hn).eventually (eventually_gt_nhds hderiv)
  filter_upwards [hs,self_mem_nhdsWithin] with t ht ht0
  have hh := mul_pos ht ht0
  rwa [div_mul_cancel₀ _ (ne_of_gt ht0)] at hh

theorem routeP_unit_minor_eventually_neg {n : ℕ} (hn : 2 ≤ n)
    (hinc : primeFreeDivisorIncrement n < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, routePUnitMultiplicativeMinor n t < 0 := by
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n))
  have hderiv := mul_neg_of_pos_of_neg (mul_pos hroot (routeP_unit_head_nat_pos hn)) hinc
  have hs := (routeP_unit_multiplicative_minor_slope hn).eventually (eventually_lt_nhds hderiv)
  filter_upwards [hs,self_mem_nhdsWithin] with t ht ht0
  have hh := mul_neg_of_neg_of_pos ht ht0
  rwa [div_mul_cancel₀ _ (ne_of_gt ht0)] at hh

theorem routeP_unit_prime_minor_positive_cofinal (N : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ p : ℕ, p.Prime ∧ N ≤ p ∧ ∃ t : ℝ, 0<t ∧ t<ε ∧
      divisorContinuousUnitHead p ^ 2 <
        divisorContinuousUnitHead ((p:ℝ)*Real.exp (-2*t)) *
          divisorContinuousUnitHead ((p:ℝ)*Real.exp (2*t)) := by
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop
      (2-2*Real.eulerMascheroniConstant)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hl
  obtain ⟨p,hpT,hp⟩ := Nat.exists_infinite_primes (max T N)
  have hlog := hT p ((le_max_left _ _).trans hpT)
  change 2-2*Real.eulerMascheroniConstant < Real.log (p:ℝ) at hlog
  have hinc : 0 < primeFreeDivisorIncrement p := by
    simp only [primeFreeDivisorIncrement, hp.divisors]
    have hcard : ({1,p}:Finset ℕ).card = 2 := by simp [Ne.symm hp.ne_one]
    rw [hcard]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hs := routeP_unit_minor_eventually_pos hp.two_le hinc
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t<ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,ht0,htε⟩ := (hs.and (htpos.and he)).exists
  refine ⟨p,hp,(le_max_right _ _).trans hpT,t,ht0,htε,?_⟩
  exact sub_pos.mp ht

theorem routeP_unit_two_power_minor_negative_cofinal (N : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ, N ≤ 2^k ∧ ∃ t : ℝ, 0<t ∧ t<ε ∧
      divisorContinuousUnitHead ((2^k:ℕ):ℝ) ^ 2 >
        divisorContinuousUnitHead (((2^k:ℕ):ℝ)*Real.exp (-2*t)) *
          divisorContinuousUnitHead (((2^k:ℕ):ℝ)*Real.exp (2*t)) := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2:ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hgap : 0 < 1-Real.log 2 := by linarith
  obtain ⟨k₀,hk₀⟩ := exists_nat_gt ((2*Real.eulerMascheroniConstant-1)/(1-Real.log 2))
  let k := max k₀ (max N 1)
  have hk₀le : k₀ ≤ k := le_max_left _ _
  have hkN : N ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hk1 : 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hpow : k < 2^k := Nat.lt_two_pow_self
  have hinc : primeFreeDivisorIncrement (2^k) < 0 := by
    have hkr : (2*Real.eulerMascheroniConstant-1)/(1-Real.log 2) < (k:ℝ) :=
      hk₀.trans_le (by exact_mod_cast hk₀le)
    have hb := (div_lt_iff₀ hgap).mp hkr
    simp only [primeFreeDivisorIncrement, Nat.divisors_prime_pow Nat.prime_two,
      Finset.card_map,Finset.card_range,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hs := routeP_unit_minor_eventually_neg (n := 2^k) (by omega) hinc
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t<ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,ht0,htε⟩ := (hs.and (htpos.and he)).exists
  refine ⟨k,hkN.trans hpow.le,t,ht0,htε,?_⟩
  exact sub_neg.mp ht

end RHTower

