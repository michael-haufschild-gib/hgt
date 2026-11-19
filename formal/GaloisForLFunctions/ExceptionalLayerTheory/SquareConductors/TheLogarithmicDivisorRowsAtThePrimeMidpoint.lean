import GaloisForLFunctions.RHTower.MobiusSquareDivisorKernel
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic divisor rows at sharp prime intervals

Dirichlet's divisor error extends through each fractional endpoint. On an
interval of ratio at most two, summation by parts replaces the divisor row
by the logarithmic density with square-root error times one logarithm.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def divisorPrimitive (x : ℝ) : ℝ :=
  x*Real.log x+(2*Real.eulerMascheroniConstant-1)*x

private def divisorCount (x : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊x⌋₊,(k.divisors.card:ℝ)

private def divisorErrorConstant : ℝ := 23+|2*Real.eulerMascheroniConstant-1|

private theorem divisor_count_real {x : ℝ} (hx : 1 ≤ x) :
    |divisorCount x-divisorPrimitive x| ≤ divisorErrorConstant*Real.sqrt x := by
  let m := ⌊x⌋₊
  let c := 2*Real.eulerMascheroniConstant-1
  have hx0 := zero_lt_one.trans_le hx
  have hm : 1 ≤ m := Nat.le_floor (by simpa using hx)
  have hm0 := (Nat.cast_pos (α:=ℝ)).mpr hm
  have hmx : (m:ℝ) ≤ x := Nat.floor_le hx0.le
  have hxm : x < (m:ℝ)+1 := Nat.lt_floor_add_one x
  have hcount : divisorCount x=_root_.RHTower.mobiusSquareDivisorSummatory m := by
    simp only [divisorCount,_root_.RHTower.mobiusSquareDivisorSummatory,m]
    rw [Icc_eq_cons_Ioc (Nat.zero_le _),sum_cons]
    have hset : Ioc 0 ⌊x⌋₊=Icc 1 ⌊x⌋₊ := by ext k; simp only [mem_Ioc,mem_Icc]; omega
    simp [hset]
  have he : |divisorCount x-divisorPrimitive m| ≤ 20*Real.sqrt m := by
    simpa only [_root_.RHTower.mobiusSquareDivisorRemainder,←hcount,
      _root_.RHTower.mobiusSquareDivisorMainTerm,divisorPrimitive] using
      _root_.RHTower.abs_mobiusSquareDivisorRemainder_le m
  have hlog := Real.log_le_log hm0 hmx
  have hlx := Real.log_nonneg hx
  have hquad := Real.log_le_rpow_div hx0.le (by norm_num : (0:ℝ)<1/2)
  rw [←Real.sqrt_eq_rpow] at hquad
  have hr := Real.log_le_sub_one_of_pos (div_pos hx0 hm0)
  rw [Real.log_div hx0.ne' hm0.ne'] at hr
  have hprod := mul_le_mul_of_nonneg_right hr hm0.le
  rw [sub_mul,div_mul_cancel₀ _ hm0.ne',one_mul] at hprod
  have hdiff : |divisorPrimitive x-divisorPrimitive m| ≤ Real.log x+1+|c| := by
    rw [show divisorPrimitive x-divisorPrimitive m=
      (x-m)*Real.log x+(Real.log x-Real.log m)*m+c*(x-m) by unfold divisorPrimitive; dsimp only [c]; ring]
    have ha := mul_le_mul_of_nonneg_right (show x-m ≤ 1 by linarith only [hxm]) hlx
    have hb := mul_nonneg (sub_nonneg.mpr hlog) hm0.le
    have hc : |c*(x-m)| ≤ |c| := by
      rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hmx)]
      exact mul_le_of_le_one_right (abs_nonneg _) (by linarith only [hxm])
    rw [abs_le]
    constructor <;> linarith only [ha,hprod,hb,(abs_le.mp hc).1,(abs_le.mp hc).2,
      mul_nonneg (sub_nonneg.mpr hmx) hlx,abs_nonneg c,hxm,hlx]
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have htriangle := abs_sub_le (divisorCount x) (divisorPrimitive m) (divisorPrimitive x)
  rw [abs_sub_comm (divisorPrimitive m)] at htriangle
  change _ ≤ (23+|c|)*Real.sqrt x
  linarith only [htriangle,he,hdiff,hquad,hs,Real.sqrt_le_sqrt hmx,
    le_mul_of_one_le_right (abs_nonneg c) hs]

private theorem divisor_primitive_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt divisorPrimitive (Real.log x+2*Real.eulerMascheroniConstant) x := by
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).add
    ((hasDerivAt_id x).const_mul (2*Real.eulerMascheroniConstant-1))
  apply h.congr_deriv
  simp only [id_eq,one_mul,mul_one,mul_inv_cancel₀ hx.ne']
  ring

/-- The complete logarithmically weighted divisor row on (a,b], including
both floor endpoints, has density log(t)+2γ before applying the log price. -/
theorem sharp_divisor_log_row (d : ℕ) (hd : 1 ≤ d) {a b : ℝ} (ha : 1 ≤ a)
    (hab : a ≤ b) (hshort : b ≤ 2*a) :
    |(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,Real.log (d*k:ℕ)*(k.divisors.card:ℝ))-
      (∫ t in a..b,(Real.log d+Real.log t)*(Real.log t+2*Real.eulerMascheroniConstant))| ≤
      (23+|2*Real.eulerMascheroniConstant-1|)*Real.sqrt b*(2*(Real.log d+Real.log b)+1) := by
  let F := fun t : ℝ => Real.log d+Real.log t
  let E := fun t : ℝ => divisorCount t-divisorPrimitive t
  let B := divisorErrorConstant*Real.sqrt b
  have hB : 0 ≤ B := by dsimp [B,divisorErrorConstant]; positivity
  have h0 := zero_lt_one.trans_le ha
  have hp {t : ℝ} (ht : t ∈ Set.Icc a b) : 0<t := h0.trans_le ht.1
  have he {t : ℝ} (ht : t ∈ Set.Icc a b) : |E t| ≤ B :=
    (divisor_count_real (ha.trans ht.1)).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt ht.2) (by dsimp [divisorErrorConstant]; positivity))
  have hf (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F t⁻¹ t :=
    (Real.hasDerivAt_log (hp ht).ne').const_add _
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) :=
    continuousOn_id.inv₀ fun t ht => (hp ht).ne'
  have hdF : Set.EqOn (deriv F) (fun t : ℝ => t⁻¹) (Set.Icc a b) := fun t ht => (hf t ht).deriv
  have hint := (hcont.congr hdF).integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => (k.divisors.card:ℝ)) h0.le hab
    (fun t ht => (hf t ht).differentiableAt) hint
  have hcount : IntervalIntegrable (fun t : ℝ => t⁻¹*divisorCount t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (integrableOn_mul_sum_Icc (fun k : ℕ => (k.divisors.card:ℝ)) h0.le
      hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hG : ContinuousOn divisorPrimitive (Set.Icc a b) :=
    fun t ht => (divisor_primitive_deriv (hp ht)).continuousAt.continuousWithinAt
  have hIG : IntervalIntegrable (fun t : ℝ => t⁻¹*divisorPrimitive t) volume a b :=
    ((hcont.mul hG).mono (Set.uIcc_of_le hab).subset).intervalIntegrable
  have hderInt : (∫ t in Set.Ioc a b,deriv F t*divisorCount t)=
      ∫ t in a..b,t⁻¹*divisorCount t := by
    rw [intervalIntegral.integral_of_le hab]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    exact fun t ht => congrArg (· * divisorCount t) (hdF (Set.Ioc_subset_Icc_self ht))
  change _=F b*divisorCount b-F a*divisorCount a-_ at hAbel
  rw [hderInt] at hAbel
  have hG' : ContinuousOn (fun t : ℝ => Real.log t+2*Real.eulerMascheroniConstant) (Set.Icc a b) :=
    (Real.continuousOn_log.mono fun _ ht => (hp ht).ne').add continuousOn_const
  have hmain := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=a) (b:=b)
    (u:=F) (v:=divisorPrimitive) (u':=fun t => t⁻¹)
    (v':=fun t => Real.log t+2*Real.eulerMascheroniConstant)
    (fun t ht => hf t ((Set.uIcc_of_le hab) ▸ ht))
    (fun t ht => divisor_primitive_deriv (hp ((Set.uIcc_of_le hab) ▸ ht)))
    ((hcont.mono (Set.uIcc_of_le hab).subset).intervalIntegrable)
    ((hG'.mono (Set.uIcc_of_le hab).subset).intervalIntegrable)
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => t⁻¹*E t) (C:=a⁻¹*B) (a:=a) (b:=b) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht' := Set.Ioc_subset_Icc_self ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (inv_pos.mpr (hp ht'))]
      exact mul_le_mul (inv_anti₀ h0 ht.1.le) (he ht') (abs_nonneg _) (inv_nonneg.mpr h0.le))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hI
  have hsize : a⁻¹*B*(b-a) ≤ B := by
    calc _ ≤ a⁻¹*B*a := mul_le_mul_of_nonneg_left (by linarith only [hshort]) (by positivity)
         _ = B := by field_simp
  have hexact : (∫ t in a..b,t⁻¹*E t)=
      (∫ t in a..b,t⁻¹*divisorCount t)-(∫ t in a..b,t⁻¹*divisorPrimitive t) := by
    simp only [E,mul_sub,intervalIntegral.integral_sub hcount hIG]
  have hF0 := Real.log_natCast_nonneg d
  have hfa : 0 ≤ F a := add_nonneg hF0 (Real.log_nonneg ha)
  have hfab : F a ≤ F b := add_le_add_left (Real.log_le_log h0 hab) _
  have hterm {t : ℝ} (ht : t ∈ Set.Icc a b) (ht0 : 0 ≤ F t) (htb : F t ≤ F b) :
      |F t*E t| ≤ F b*B := by
    rw [abs_mul,abs_of_nonneg ht0]
    exact mul_le_mul htb (he ht) (abs_nonneg _) (hfa.trans hfab)
  have hea := abs_le.mp (hterm ⟨le_rfl,hab⟩ hfa hfab)
  have heb := abs_le.mp (hterm ⟨hab,le_rfl⟩ (hfa.trans hfab) le_rfl)
  have hi := abs_le.mp (hI.trans hsize)
  have hweight (k : ℕ) (hk : k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊) :
      Real.log (d*k:ℕ)*(k.divisors.card:ℝ)=F k*(k.divisors.card:ℝ) := by
    have hk0 := (Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
      (Nat.cast_ne_zero.mpr hk0.ne')]
  rw [sum_congr rfl hweight]
  change |(∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,F k*(k.divisors.card:ℝ))-
    (∫ t in a..b,F t*(Real.log t+2*Real.eulerMascheroniConstant))| ≤ B*(2*F b+1)
  rw [hAbel,hmain,abs_le]
  dsimp only [E] at hea heb
  constructor <;> linarith only [hea.1,hea.2,heb.1,heb.2,hi.1,hi.2,hexact]

#print axioms sharp_divisor_log_row

/-- Difference of the logarithmic moments on the two unit intervals. -/
def midpointLogMoment (j : ℕ) : ℝ :=
  (∫ u in (3:ℝ)..4,Real.log u^j)-(∫ u in (2:ℝ)..3,Real.log u^j)

theorem first_midpoint_log_moment : midpointLogMoment 1=10*Real.log 2-6*Real.log 3 := by
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  simp only [midpointLogMoment,pow_one,integral_log,h4]
  ring

private theorem scaled_divisor_log_integral (d : ℝ) {Y l r : ℝ} (hY : 0<Y)
    (hl : 0<l) (hlr : l ≤ r) :
    (∫ t in Y*l..Y*r,(Real.log d+Real.log t)*(Real.log t+2*Real.eulerMascheroniConstant))=
      Y*((r-l)*(Real.log d+Real.log Y)*(Real.log Y+2*Real.eulerMascheroniConstant)+
        (Real.log d+2*Real.log Y+2*Real.eulerMascheroniConstant)*(∫ u in l..r,Real.log u)+
        ∫ u in l..r,Real.log u^2) := by
  let F := fun t => (Real.log d+Real.log t)*(Real.log t+2*Real.eulerMascheroniConstant)
  let A := Real.log d+Real.log Y
  let B := Real.log Y+2*Real.eulerMascheroniConstant
  have hlog : ContinuousOn Real.log (Set.uIcc l r) := by
    rw [Set.uIcc_of_le hlr]
    exact Real.continuousOn_log.mono fun u hu => (hl.trans_le hu.1).ne'
  have h1 := (continuousOn_const.mul hlog : ContinuousOn (fun u => (A+B)*Real.log u)
    (Set.uIcc l r)).intervalIntegrable (μ:=volume)
  have h2 := (hlog.pow 2).intervalIntegrable (μ:=volume)
  have hs := intervalIntegral.integral_comp_mul_left (a:=l) (b:=r) F hY.ne'
  simp only [smul_eq_mul] at hs
  have he : (∫ u in l..r,F (Y*u))=
      (∫ u in l..r,(A*B+(A+B)*Real.log u)+Real.log u^2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hlr] at hu
    have hu0 := hl.trans_le hu.1
    dsimp only [F,A,B]
    rw [Real.log_mul hY.ne' hu0.ne']
    ring
  rw [he,intervalIntegral.integral_add (intervalIntegrable_const.add h1) h2,
    intervalIntegral.integral_add intervalIntegrable_const h1,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,smul_eq_mul] at hs
  have hh := congrArg (fun t : ℝ => Y*t) hs
  dsimp only at hh
  rw [←mul_assoc,mul_inv_cancel₀ hY.ne',one_mul] at hh
  change (∫ t in Y*l..Y*r,F t)=_
  rw [←hh]
  dsimp only [A,B]
  ring

/-- After adding the right interval and subtracting the left, the constant
density term cancels exactly. Both logarithmic moments retain the same cut. -/
theorem signed_divisor_log_integral {n d : ℝ} (hn : 0<n) (hd : 0<d) :
    let Y := n/d
    let F := fun t => (Real.log d+Real.log t)*(Real.log t+2*Real.eulerMascheroniConstant)
    (∫ t in Y*3..Y*4,F t)-(∫ t in Y*2..Y*3,F t)=
      Y*(midpointLogMoment 2+midpointLogMoment 1*(2*Real.log n+2*Real.eulerMascheroniConstant-Real.log d)) := by
  dsimp only
  rw [scaled_divisor_log_integral d (div_pos hn hd) (by norm_num) (by norm_num),
    scaled_divisor_log_integral d (div_pos hn hd) (by norm_num) (by norm_num),
    Real.log_div hn.ne' hd.ne']
  simp only [midpointLogMoment,pow_one]
  ring

#print axioms first_midpoint_log_moment
#print axioms signed_divisor_log_integral

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
