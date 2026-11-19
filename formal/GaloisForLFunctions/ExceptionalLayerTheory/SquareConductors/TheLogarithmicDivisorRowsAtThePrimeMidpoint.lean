import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFactorialCenterOfTheSmallUnitaryDivisors
import GaloisForLFunctions.RHTower.MobiusSquareDivisorKernel
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OppositePrimeTriplesAtTheCubeRootOfTheMidpoint
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
  simp only [sub_mul,div_mul_cancel₀ _ hm0.ne',one_mul] at hprod
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
  have hint : IntegrableOn (deriv F) (Set.Icc a b) volume := (hcont.congr hdF).integrableOn_Icc
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
  change (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,F k*(k.divisors.card:ℝ))=
    F b*divisorCount b-F a*divisorCount a-(∫ t in Set.Ioc a b,deriv F t*divisorCount t) at hAbel
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
  have hfab : F a ≤ F b := add_le_add le_rfl (Real.log_le_log h0 hab)
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
  rw [he,intervalIntegral.integral_add
    (f:=fun u : ℝ => A*B+(A+B)*Real.log u) (g:=fun u : ℝ => Real.log u^2)
    (intervalIntegrable_const.add h1) h2,
    intervalIntegral.integral_add (f:=fun _ : ℝ => A*B) (g:=fun u : ℝ => (A+B)*Real.log u)
      intervalIntegrable_const h1,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,smul_eq_mul] at hs
  change (∫ t in Y*l..Y*r,F t)=_
  calc
    _ = Y * (Y⁻¹ * ∫ t in Y*l..Y*r,F t) := by rw [←mul_assoc,mul_inv_cancel₀ hY.ne',one_mul]
    _ = _ := by rw [←hs]; dsimp only [A,B]; ring

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

/-- Logarithmic divisor price in the multiple-of-d row of (in,(i+1)n]. -/
def midpointDivisorRow (n d i : ℕ) : ℝ :=
  let Y := (n:ℝ)/d
  ∑ k ∈ Ioc ⌊Y*i⌋₊ ⌊Y*((i:ℝ)+1)⌋₊, Real.log (d*k:ℕ)*(k.divisors.card:ℝ)

/-- Difference between the two divisor rows and their common signed integral. -/
def midpointDivisorRemainder (n d : ℕ) : ℝ :=
  midpointDivisorRow n d 3-midpointDivisorRow n d 2-
    ((n:ℝ)/d)*(midpointLogMoment 2+
      midpointLogMoment 1*(2*Real.log n+2*Real.eulerMascheroniConstant-Real.log d))

private theorem midpoint_divisor_remainder_le {n d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    |midpointDivisorRemainder n d| ≤
      4*divisorErrorConstant*Real.sqrt n*(2*Real.log (4*(n:ℝ))+1)*(1/Real.sqrt d) := by
  let Y := (n:ℝ)/d
  let F := fun t : ℝ => (Real.log d+Real.log t)*(Real.log t+2*Real.eulerMascheroniConstant)
  have hd0 := (Nat.cast_pos (α:=ℝ)).mpr hd
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr (hd.trans hdn)
  have hY : 1 ≤ Y := (one_le_div hd0).mpr (by exact_mod_cast hdn)
  have hY0 := zero_lt_one.trans_le hY
  have hC : 0 ≤ divisorErrorConstant := by unfold divisorErrorConstant; positivity
  have hlog4 : Real.log d+Real.log (Y*4)=Real.log (4*(n:ℝ)) := by
    rw [←Real.log_mul hd0.ne' (by positivity : Y*4≠0)]
    congr 1
    dsimp only [Y]
    field_simp
  have he (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 3) :
      |midpointDivisorRow n d i-(∫ t in Y*i..Y*((i:ℝ)+1),F t)| ≤
        divisorErrorConstant*Real.sqrt (Y*4)*(2*Real.log (4*(n:ℝ))+1) := by
    have hi1 : (1:ℝ) ≤ i := Nat.one_le_cast.mpr (by omega)
    have hi3 : (i:ℝ) ≤ 3 := by exact_mod_cast hi'
    have hp := one_le_mul_of_one_le_of_one_le hY hi1
    have hv : Y*((i:ℝ)+1) ≤ Y*4 :=
      mul_le_mul_of_nonneg_left (by linarith only [hi3]) hY0.le
    have hab : Y*(i:ℝ) ≤ Y*((i:ℝ)+1) := by linarith only [hY0]
    have hshort : Y*((i:ℝ)+1) ≤ 2*(Y*i) := by
      linarith only [mul_le_mul_of_nonneg_left hi1 hY0.le]
    have h := sharp_divisor_log_row d hd hp hab hshort
    apply h.trans
    have hlog := Real.log_le_log (zero_lt_one.trans_le (hp.trans hab)) hv
    have hprice : 0 ≤ 2*(Real.log d+Real.log (Y*((i:ℝ)+1)))+1 := by
      linarith only [Real.log_natCast_nonneg d,Real.log_nonneg (hp.trans hab)]
    rw [←hlog4]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) hC)
      (by linarith only [hlog]) hprice (mul_nonneg hC (Real.sqrt_nonneg _))
  have h3 := he 3 (by decide) le_rfl
  have h2 := he 2 le_rfl (by decide)
  norm_num only [Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num,show (2:ℝ)+1=3 by norm_num] at h3 h2
  have hmain := signed_divisor_log_integral hn0 hd0
  change (∫ t in Y*3..Y*4,F t)-(∫ t in Y*2..Y*3,F t)=_ at hmain
  have herr : |midpointDivisorRemainder n d| ≤
      2*divisorErrorConstant*Real.sqrt (Y*4)*(2*Real.log (4*(n:ℝ))+1) := by
    unfold midpointDivisorRemainder
    rw [←hmain,abs_le]
    constructor <;> linarith only [(abs_le.mp h2).1,(abs_le.mp h2).2,(abs_le.mp h3).1,(abs_le.mp h3).2]
  apply herr.trans_eq
  rw [Real.sqrt_mul hY0.le,show Real.sqrt 4=2 by norm_num]
  dsimp only [Y]
  rw [Real.sqrt_div hn0.le]
  ring

private theorem cubic_moebius_bound (Y k : ℕ) : |cubicSmoothMoebius Y k| ≤ 1 := by
  change |if k ∣ primorial Y then (ArithmeticFunction.moebius k:ℝ) else 0| ≤ 1
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=k)
  · norm_num

private theorem cubic_moebius_square_bound (Y d : ℕ) :
    |(cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d| ≤ (d.divisors.card:ℝ) := by
  rw [pow_two,ArithmeticFunction.mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _ ∈ d.divisorsAntidiagonal,(1:ℝ) := by
             apply sum_le_sum
             intro x _
             rw [abs_mul]
             exact (mul_le_mul (cubic_moebius_bound Y x.1) (cubic_moebius_bound Y x.2) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
       _ = _ := by rw [←Nat.map_div_right_divisors]; simp

private theorem cubic_divisor_cut_le {n : ℕ} (hn : 0 < n) :
    ((4*n/(cubicMidpointCut n+1):ℕ):ℝ) ≤ 4*(n:ℝ)^(2/3:ℝ) := by
  let Y := cubicMidpointCut n
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hfloor : (n:ℝ)^(1/3:ℝ) ≤ ((Y+1:ℕ):ℝ) := by
    rw [Nat.cast_succ]
    exact (Real.rpow_le_rpow hn0.le (by linarith only [hn0] : (n:ℝ)≤3*n) (by norm_num)).trans
      (Nat.lt_floor_add_one ((3*(n:ℝ))^(1/3:ℝ))).le
  have hbase : ((4*n/(Y+1):ℕ):ℝ) ≤ ((4*n:ℕ):ℝ)/(Y+1:ℕ) := Nat.cast_div_le
  have h := hbase.trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hn0 _) hfloor)
  push_cast at h
  apply h.trans_eq
  rw [div_eq_mul_inv,←Real.rpow_neg hn0.le]
  calc 4*(n:ℝ)*(n:ℝ)^(-(1/3:ℝ)) = 4*((n:ℝ)^(1:ℝ)*(n:ℝ)^(-(1/3:ℝ))) := by rw [Real.rpow_one]; ring
       _ = _ := by rw [←Real.rpow_add hn0]; norm_num

/-- Total replacement error for the Möbius-square divisor rows at the
actual cube-root cutoff. The exponent includes both sharp endpoints. -/
theorem cubic_divisor_replacement_error {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n : ℕ}, 3 ≤ cubicMidpointCut n →
      |∑ d ∈ Icc 1 (4*n/(cubicMidpointCut n+1)),
        (cubicSmoothMoebius (cubicMidpointCut n)^2 : ArithmeticFunction ℝ) d*
          midpointDivisorRemainder n d| ≤ C*(n:ℝ)^(5/6+ε) := by
  let e := ε/2
  let K := _root_.RHTower.Sieve.divisorBoundConst e
  let L := 2*(4:ℝ)^e/e+1
  have he : 0<e := half_pos hε
  have hK : 0≤K := (_root_.RHTower.Sieve.divisorBoundConst_pos he).le
  have hC : 0≤divisorErrorConstant := by unfold divisorErrorConstant; positivity
  refine ⟨16*K*divisorErrorConstant*L,?_⟩
  intro n hY
  let Y := cubicMidpointCut n
  let D := 4*n/(Y+1)
  have hn : 0<n := by
    by_contra! hn
    have hzero : n=0 := by omega
    subst n
    norm_num [cubicMidpointCut,Real.zero_rpow] at hY
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hDn : D ≤ n := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos Y)).mpr
    exact (show 4*n < (n+1)*4 by omega).trans_le
      (Nat.mul_le_mul_left (n+1) (show 4 ≤ Y+1 by omega))
  have hD : (D:ℝ) ≤ 4*(n:ℝ)^(2/3:ℝ) := cubic_divisor_cut_le hn
  have hroot : Real.sqrt D ≤ 2*(n:ℝ)^(1/3:ℝ) := by
    apply (Real.sqrt_le_sqrt hD).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),show Real.sqrt 4=2 by norm_num,
      Real.sqrt_eq_rpow,←Real.rpow_mul hn0.le]
    norm_num
  have hln := Real.log_le_rpow_div (show 0≤4*(n:ℝ) by positivity) he
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hn0.le] at hln
  have hl : 2*Real.log (4*(n:ℝ))+1 ≤ L*(n:ℝ)^e := by
    change 2*Real.log (4*(n:ℝ))+1 ≤ (2*(4:ℝ)^e/e+1)*(n:ℝ)^e
    simp only [div_eq_mul_inv] at hln ⊢
    linarith only [hln,Real.one_le_rpow hn1 he.le]
  have hl0 : 0≤2*Real.log (4*(n:ℝ))+1 := by
    have := Real.log_nonneg (show 1≤4*(n:ℝ) by linarith only [hn1]); linarith only [this]
  let B := (K*(n:ℝ)^e)*(4*divisorErrorConstant*Real.sqrt n*(2*Real.log (4*(n:ℝ))+1))
  have hB : 0≤B := by dsimp [B]; positivity
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ Icc 1 D,B*(1/Real.sqrt d) := by
             apply sum_le_sum
             intro d hd
             obtain ⟨hd1,hdD⟩ := mem_Icc.mp hd
             have hdn := hdD.trans hDn
             have hc := (cubic_moebius_square_bound Y d).trans
               ((_root_.RHTower.Sieve.card_divisors_le_rpow he (Nat.ne_of_gt hd1)).trans
                 (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg d)
                   (Nat.cast_le.mpr hdn) he.le) hK))
             rw [abs_mul]
             exact (mul_le_mul hc (midpoint_divisor_remainder_le hd1 hdn) (abs_nonneg _)
               (mul_nonneg hK (Real.rpow_nonneg hn0.le _))).trans_eq (by dsimp only [B]; ring)
       _ ≤ B*(2*Real.sqrt D) := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le D) hB
       _ ≤ B*(2*(2*(n:ℝ)^(1/3:ℝ))) := mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_left hroot (by norm_num)) hB
       _ ≤ 16*K*divisorErrorConstant*(Real.sqrt n*(n:ℝ)^e*(n:ℝ)^(1/3:ℝ))*(L*(n:ℝ)^e) := by
         calc _ = 16*K*divisorErrorConstant*(Real.sqrt n*(n:ℝ)^e*(n:ℝ)^(1/3:ℝ))*
                    (2*Real.log (4*(n:ℝ))+1) := by dsimp only [B]; ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
       _ = _ := by
         rw [Real.sqrt_eq_rpow]
         calc _ = (16*K*divisorErrorConstant*L)*(((n:ℝ)^(1/2:ℝ)*(n:ℝ)^e)*(n:ℝ)^(1/3:ℝ)*(n:ℝ)^e) := by ring
              _ = _ := by rw [←Real.rpow_add hn0,←Real.rpow_add hn0,←Real.rpow_add hn0]; dsimp only [e]; ring_nf

/-- Error of the ordinary multiple-of-d log row relative to its signed density. -/
def ordinaryMidpointRowRemainder (n d : ℕ) : ℝ :=
  progressionLogFactorial d (4*n)-2*progressionLogFactorial d (3*n)+
    progressionLogFactorial d (2*n)-(n:ℝ)/d*midpointLogMoment 1

private theorem ordinary_midpoint_row_error {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    |ordinaryMidpointRowRemainder n d| ≤ 4*(3+4*Real.log (4*(n:ℝ))) := by
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  let B := 3+4*Real.log (4*(n:ℝ))
  have row (i : ℕ) (hi : 0 < i) (h4 : i ≤ 4) :
      |progressionLogFactorial d (i*n)-(i*(n:ℝ))/d*(Real.log i+Real.log n-1)| ≤ B := by
    have h := progression_log_factorial_error hd (i*n)
    have hip := (Nat.cast_pos (α:=ℝ)).mpr hi
    have hl := Real.log_le_log (mul_pos hip hn0)
      (mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ 4 by exact_mod_cast h4) hn0.le)
    push_cast at h
    rw [Real.log_mul hip.ne' hn0.ne'] at h hl
    exact h.trans (by dsimp only [B]; linarith only [hl])
  have h4 := abs_le.mp (row 4 (by decide) le_rfl)
  have h3 := abs_le.mp (row 3 (by decide) (by decide))
  have h2 := abs_le.mp (row 2 (by decide) (by decide))
  have hl4 : Real.log 4=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  simp only [Nat.cast_ofNat,hl4] at h4 h3 h2
  unfold ordinaryMidpointRowRemainder
  rw [first_midpoint_log_moment,abs_le]
  change -(4*B) ≤ _ ∧ _ ≤ 4*B
  simp only [div_eq_mul_inv] at h4 h3 h2 ⊢
  constructor <;> linarith only [h4.1,h4.2,h3.1,h3.2,h2.1,h2.2]

/-- The two completed rows together have the prescribed signed center through
the cube-root divisor cutoff, with error of order five sixths plus epsilon. -/
theorem cubic_complete_row_replacement {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n : ℕ}, 3 ≤ cubicMidpointCut n →
      let Y := cubicMidpointCut n
      let S := Icc 1 (4*n/(Y+1))
      |∑ d ∈ S,(2*cubicSmoothMoebius Y d*ordinaryMidpointRowRemainder n d-
        (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d*midpointDivisorRemainder n d/2)| ≤
        C*(n:ℝ)^(5/6+ε) := by
  obtain ⟨C,hC⟩ := cubic_divisor_replacement_error hε
  let J := 4*(3+24*(4:ℝ)^(1/6:ℝ))
  refine ⟨8*J+C/2,?_⟩
  intro n hY
  let Y := cubicMidpointCut n
  let D := 4*n/(Y+1)
  let S := Icc 1 D
  let P := (n:ℝ)^(5/6+ε)
  have hn : 0 < n := by
    by_contra! hz
    obtain rfl : n=0 := by omega
    norm_num [cubicMidpointCut,Real.zero_rpow] at hY
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hlog := Real.log_le_rpow_div (show 0 ≤ 4*(n:ℝ) by positivity) (by norm_num : (0:ℝ)<1/6)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hn0.le] at hlog
  have hj : 4*(3+4*Real.log (4*(n:ℝ))) ≤ J*(n:ℝ)^(1/6:ℝ) := by
    dsimp only [J]
    linarith only [hlog,Real.one_le_rpow hn1 (by norm_num : (0:ℝ)≤1/6)]
  let F := fun d => cubicSmoothMoebius Y d*ordinaryMidpointRowRemainder n d
  let G := fun d => (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d*midpointDivisorRemainder n d
  have hF : |∑ d ∈ S,F d| ≤ 4*J*P := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _ ∈ S,J*(n:ℝ)^(1/6:ℝ) := by
               apply sum_le_sum
               intro d hd
               dsimp only [F]
               rw [abs_mul]
               exact (mul_le_mul (cubic_moebius_bound Y d)
                 ((ordinary_midpoint_row_error hn (mem_Icc.mp hd).1).trans hj) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
         _ ≤ (4*(n:ℝ)^(2/3:ℝ))*(J*(n:ℝ)^(1/6:ℝ)) := by
               simp only [S,sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]
               exact mul_le_mul_of_nonneg_right (cubic_divisor_cut_le hn) (by dsimp only [J]; positivity)
         _ = (4*J)*(n:ℝ)^(5/6:ℝ) := by
               rw [show (5/6:ℝ)=2/3+1/6 by norm_num,Real.rpow_add hn0]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
           (by dsimp only [J]; positivity)
  have hG : |∑ d ∈ S,G d| ≤ C*P := hC hY
  change |∑ d ∈ S,(2*cubicSmoothMoebius Y d*ordinaryMidpointRowRemainder n d-G d/2)| ≤ _
  simp only [mul_assoc,sum_sub_distrib,←mul_sum,←sum_div]
  change |2*(∑ d ∈ S,F d)-(∑ d ∈ S,G d)/2| ≤ (8*J+C/2)*P
  rw [abs_le]
  constructor <;> linarith only [(abs_le.mp hF).1,(abs_le.mp hF).2,(abs_le.mp hG).1,(abs_le.mp hG).2]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
