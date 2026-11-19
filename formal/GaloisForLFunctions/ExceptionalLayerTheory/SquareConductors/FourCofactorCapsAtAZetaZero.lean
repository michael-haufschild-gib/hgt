import GaloisForLFunctions.ExceptionalLayerTheory.LargeComplementsInTheCoprimeProduct
import GaloisForLFunctions.RHTower.DQPTPartialSumRate

/-!
# Four adjacent cofactor caps at a zeta zero

The unit cofactor stencil splits into two alternating sequences and a
unit correction. At a zeta zero its response tends to one. In the
average of four consecutive caps the leading alternating tails cancel.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
open RHTower.DQPT
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Coefficient of the second alternating sequence, read at divisor four. -/
def cofactorDyadicCoefficient : ℝ := -(stencil 2 (fun d => if d=4 then 1 else 0))/2

private theorem stencil_at_two (f : ℕ → ℝ) :
    stencil 2 f = f 1+(cofactorDyadicCoefficient-2)*f 2-2*cofactorDyadicCoefficient*f 4 := by
  let a := stencil 2 (fun d => if d=2 then 1 else 0)
  let b := stencil 2 (fun d => if d=4 then 1 else 0)
  let u := stencil 2 (fun d => if d=1 then 1 else 0)
  have hu : u=1 := by
    have he (d : ℕ) : (if d=1 then (1:ℝ) else 0)=((1/d:ℕ):ℝ) := by
      by_cases h : d=1
      · subst d; simp
      by_cases hz : d=0
      · subst d; simp
      rw [if_neg h,Nat.div_eq_of_lt (by omega : 1<d),Nat.cast_zero]
    dsimp only [u]
    simp_rw [he]
    exact prefix_one (by decide : 1≤1) (by decide : 1<2)
  have basis (w : ℕ → ℝ) : stencil 2 w = u*w 1+a*w 2+b*w 4 := by
    have hi : Icc 1 2 = ({1,2} : Finset ℕ) := by decide
    dsimp only [u,a,b,stencil]
    simp only [hi,sum_insert (by decide : 1∉({2} : Finset ℕ)),sum_singleton,
      show 2*2=4 by decide,if_true,if_neg (by decide : (1:ℕ)≠2),
      if_neg (by decide : (2:ℕ)≠1),if_neg (by decide : (4:ℕ)≠1),
      if_neg (by decide : (1:ℕ)≠4),if_neg (by decide : (2:ℕ)≠4),
      if_neg (by decide : (4:ℕ)≠2),mul_zero,mul_one,zero_add,add_zero,sub_zero]
    ring
  have expand (w : ℕ → ℝ) : stencil 2 w=w 1+a*w 2+b*w 4 := by rw [basis,hu,one_mul]
  have hz := expand (fun d => 1/d)
  rw [stencil_linear_quotient (by decide : 1≤2) 1] at hz
  norm_num only [Nat.cast_one,Nat.cast_ofNat,div_one] at hz
  change stencil 2 f = f 1+(-b/2-2)*f 2-2*(-b/2)*f 4
  rw [expand]
  linear_combination -2*f 2*hz

/-- Two cofactor increments. The unit is the only exception in the odd
sequence. On the even sequence the sign alternates at half the index. -/
theorem innerJump_dyadic_pair (k : ℕ) :
    innerJump 1 (2*k+1) = (if k=0 then 1 else 0)-1 ∧
    innerJump 1 (2*k+2) = 1-cofactorDyadicCoefficient*(-1:ℝ)^k := by
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num [innerJump_small (le_refl 1)]
    · rw [innerJump_divisor_stencil (by omega : 2≤2*k+1) 1,stencil_at_two]
      simp [hk.ne',show ¬2 ∣ 2*k+1 by omega,show ¬4 ∣ 2*k+1 by omega]
  · rw [innerJump_divisor_stencil (by omega : 2≤2*k+2) 1,stencil_at_two]
    have he : 2 ∣ 2*k+2 := ⟨k+1,by omega⟩
    simp only [one_dvd,if_true,if_pos he,mul_one]
    rcases Nat.even_or_odd k with ⟨j,hj⟩ | ⟨j,hj⟩
    · rw [if_neg (by omega : ¬4 ∣ 2*k+2),show k=2*j by omega,pow_mul]
      norm_num; ring
    · rw [if_pos (by omega : 4 ∣ 2*k+2),show k=2*j+1 by omega,pow_succ,pow_mul]
      norm_num; ring

/-- Actual signed cofactor response through its sharp cap. -/
def cofactorDirichletPrefix (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, (innerJump 1 (k+1):ℂ)*dqptRp s ((k:ℝ)+1)

private theorem rp_double (s : ℂ) (k : ℕ) :
    dqptRp s (2*((k:ℝ)+1)) = dqptRp s 2*dqptRp s ((k:ℝ)+1) := by
  simp only [dqptRp,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity) _

/-- Exact alternating-prefix formula, including the unit correction and
the lower member of each dyadic pair for an odd cap. -/
theorem cofactorDirichletPrefix_eq (s : ℂ) (N : ℕ) :
    cofactorDirichletPrefix s N = (if N=0 then 0 else 1)-dqptAltPartialSum s N-
      cofactorDyadicCoefficient*dqptRp s 2*dqptAltPartialSum s (N/2) := by
  induction N with
  | zero => simp [cofactorDirichletPrefix]
  | succ N ih =>
    rw [show cofactorDirichletPrefix s (N+1)=cofactorDirichletPrefix s N+
      (innerJump 1 (N+1):ℂ)*dqptRp s ((N:ℝ)+1) from sum_range_succ _ _,ih,dqptAltPartialSum_succ]
    rcases Nat.even_or_odd N with ⟨k,hk⟩ | ⟨k,hk⟩
    · rw [show N=2*k by omega,(innerJump_dyadic_pair k).1,pow_mul]
      have hdiv : (2*k+1)/2=k := by omega
      simp only [hdiv,Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.succ_ne_zero,if_false,
        Complex.ofReal_sub,Complex.ofReal_one]
      by_cases h : k=0
      · subst k
        norm_num [dqptRp]
      · simp [h,show 2*k≠0 by omega]; ring
    · rw [show N=2*k+1 by omega,show 2*k+1+1=2*k+2 by omega,(innerJump_dyadic_pair k).2,
        show (2*k+2)/2=k+1 by omega,show (2*k+1)/2=k by omega,dqptAltPartialSum_succ s k,
        pow_succ (-1:ℂ) (2*k),pow_mul]
      push_cast
      rw [show (2:ℝ)*k+1+1=2*((k:ℝ)+1) by ring,rp_double]
      simp only [neg_one_sq,one_pow,one_mul,neg_mul]
      ring

/-- The full cofactor multiplier in the positive half-plane. Its departure
from one is exactly a two-term Dirichlet polynomial times the eta function. -/
theorem cofactorDirichletPrefix_tendsto {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) :
    Tendsto (cofactorDirichletPrefix s) atTop
      (𝓝 (1-(1+cofactorDyadicCoefficient*dqptRp s 2)*((1-(2:ℂ)^(1-s))*riemannZeta s))) := by
  let η := (1-(2:ℂ)^(1-s))*riemannZeta s
  let a : ℂ := cofactorDyadicCoefficient*dqptRp s 2
  have h : Tendsto (dqptAltPartialSum s) atTop (𝓝 η) := dqpt_altPartialSum_tendsto hs hs1
  have hdiv : Tendsto (fun n : ℕ => n/2) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (2*b)] with n hn
    omega
  have hc : Tendsto (fun n : ℕ => if n=0 then (0:ℂ) else 1) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (by filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn; simp [Nat.ne_of_gt hn])
  change Tendsto (cofactorDirichletPrefix s) atTop (𝓝 (1-(1+a)*η))
  rw [funext (cofactorDirichletPrefix_eq s),show 1-(1+a)*η=1-η-a*η by ring]
  exact (hc.sub h).sub ((tendsto_const_nhds (x := a)).mul (h.comp hdiv))

/-- Every right zero sees unit mass in the limit of the original cofactor
coefficients. -/
theorem cofactorDirichletPrefix_at_zero {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) (hz : riemannZeta s=0) :
    Tendsto (cofactorDirichletPrefix s) atTop (𝓝 1) := by
  simpa only [hz,mul_zero,sub_zero] using cofactorDirichletPrefix_tendsto hs hs1

/-- The Dirichlet probe of the actual clipped cofactor interval for one prime. -/
def cofactorDirichletWindow (s : ℂ) (k U n p : ℕ) : ℂ :=
  ∑ v ∈ Ioc (max (productLower 1 k) U/p) (min (k/p) n) with p.Coprime v,
    (innerJump 1 v:ℂ)*dqptRp s v

private theorem cofactorDirichletWindow_eq {p n : ℕ} (hp : p.Prime) (hnp : n<p)
    (s : ℂ) (k U : ℕ) :
    cofactorDirichletWindow s k U n p =
      let m := min (k/p) n
      cofactorDirichletPrefix s m-cofactorDirichletPrefix s (min (max (productLower 1 k) U/p) m) := by
  let l := max (productLower 1 k) U/p
  let m := min (k/p) n
  let f (v : ℕ) := (innerJump 1 v:ℂ)*dqptRp s v
  have he : ((Ioc l m).filter (p.Coprime ·))=Ioc l m := by
    apply filter_true_of_mem
    intro v hv
    have h := mem_Ioc.mp hv
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ((Nat.zero_le l).trans_lt h.1)
      ((h.2.trans (min_le_right _ _)).trans_lt hnp))
  have hG (V : ℕ) : ∑ v ∈ Ioc 0 V, f v = cofactorDirichletPrefix s V := by
    rw [show Ioc 0 V=Icc 1 V by ext v; simp only [mem_Ioc,mem_Icc]; omega,
      ←Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right,cofactorDirichletPrefix,f,Nat.add_comm 1,Nat.cast_add,Nat.cast_one]
  change (∑ v ∈ (Ioc l m).filter (p.Coprime ·), f v) = cofactorDirichletPrefix s m-cofactorDirichletPrefix s (min l m)
  rw [he]
  by_cases hl : l ≤ m
  · have h := sum_Ioc_consecutive f (Nat.zero_le l) hl
    rw [hG,hG] at h
    rw [min_eq_left hl,←h,add_sub_cancel_left]
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hl),sum_empty,min_eq_right (le_of_not_ge hl),sub_self]

/-- Uniform selection by the *original* product cut. If both cofactor
endpoints exceed d, the zero probe vanishes in the limit. If the lower
cut omits at most the unit cofactor, the probe instead retains unit mass. -/
theorem cofactor_zero_selection_at_the_product_cut {s : ℂ} (hs : 0<s.re) (hs1 : s≠1)
    (hz : riemannZeta s=0) {ε : ℝ} (hε : 0<ε) :
    ∃ d : ℕ, 2≤d ∧ ∀ {p n : ℕ}, p.Prime → n<p → ∀ k U : ℕ, d≤n → d*p≤k →
      (d*p ≤ max (productLower 1 k) U → ‖cofactorDirichletWindow s k U n p‖<ε) ∧
      (max (productLower 1 k) U<2*p → ‖cofactorDirichletWindow s k U n p-1‖<ε) := by
  have hlim := cofactorDirichletPrefix_at_zero hs hs1 hz
  obtain ⟨b,hb⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) (ε/2) (half_pos hε))
  refine ⟨max 2 b,le_max_left _ _,fun {p n} hp hnp k U hdn hdk => ?_⟩
  let m := min (k/p) n
  let l := max (productLower 1 k) U/p
  have hm : max 2 b ≤ m := le_min ((Nat.le_div_iff_mul_le hp.pos).mpr hdk) hdn
  have hm' := hb m ((le_max_right _ _).trans hm)
  rw [dist_eq_norm] at hm'
  rw [cofactorDirichletWindow_eq hp hnp]
  change (max 2 b*p≤_ → ‖cofactorDirichletPrefix s m-cofactorDirichletPrefix s (min l m)‖<ε) ∧ _
  constructor
  · intro hd
    have hl : max 2 b ≤ l := (Nat.le_div_iff_mul_le hp.pos).mpr hd
    have hc := hb (min l m) ((le_max_right _ _).trans (le_min hl hm))
    rw [dist_eq_norm] at hc
    have tri := norm_sub_le (cofactorDirichletPrefix s m-1) (cofactorDirichletPrefix s (min l m)-1)
    rw [sub_sub_sub_cancel_right] at tri
    exact tri.trans_lt ((add_lt_add hm' hc).trans_eq (add_halves ε))
  · intro hd
    have hl : l<2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hd
    have hv : min l m=0 ∨ min l m=1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ ((min_le_left l m).trans_lt hl))
    have hzero : cofactorDirichletPrefix s (min l m)=0 := by
      rcases hv with h | h <;> rw [h] <;> simp [cofactorDirichletPrefix,innerJump_small (le_refl 1)]
    change ‖cofactorDirichletPrefix s m-cofactorDirichletPrefix s (min l m)-1‖<ε
    rw [hzero,sub_zero]
    exact hm'.trans (half_lt_self hε)

private def etaMidpoint (s : ℂ) (k : ℕ) : ℂ :=
  (dqptAltPartialSum s k+dqptAltPartialSum s (k+1))/2

private theorem etaMidpoint_at_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1)
    (hz : riemannZeta s=0) (k : ℕ) :
    ‖etaMidpoint s k‖ ≤ (3/4*(‖s‖*‖s+1‖))*((k:ℝ)+1)^(-s.re-1) := by
  have he := dqptEta_eq_altPartialSum_add_tail hs hs1 k
  rw [hz,mul_zero] at he
  have heq : etaMidpoint s k = -((-1:ℂ)^k)*(dqptAltTail s k-
      (1/2:ℂ)*dqptRp s ((k:ℝ)+1)) := by
    rw [etaMidpoint,dqptAltPartialSum_succ]
    linear_combination -he
  rw [heq,norm_mul,norm_neg,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  exact dqptAltTail_sub_half_norm_le hs k

/-- The four actual adjacent caps remove the leading alternating boundary
at every zeta zero in the positive half-plane, gaining one whole power. -/
theorem mean_four_cofactor_caps_at_zero {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) (hz : riemannZeta s=0)
    {K : ℕ} (hK : 0<K) :
    ‖(cofactorDirichletPrefix s (4*K)+cofactorDirichletPrefix s (4*K+1)+
      cofactorDirichletPrefix s (4*K+2)+cofactorDirichletPrefix s (4*K+3))/4-1‖ ≤
      (1+|cofactorDyadicCoefficient|)*(3/4*(‖s‖*‖s+1‖))*((K:ℝ)+1)^(-s.re-1) := by
  let a : ℂ := cofactorDyadicCoefficient*dqptRp s 2
  let H : ℝ := 3/4*(‖s‖*‖s+1‖)
  have hH : 0≤H := by dsimp only [H]; positivity
  have ha : ‖a‖ ≤ |cofactorDyadicCoefficient| := by
    change ‖(cofactorDyadicCoefficient:ℂ)*dqptRp s 2‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,dqptRp_norm (by norm_num : (0:ℝ)<2)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hs.le))
  let E := ((K:ℝ)+1)^(-s.re-1)
  have bound {j : ℕ} (hj : K≤j) : ‖etaMidpoint s j‖ ≤ H*E := by
    apply (etaMidpoint_at_zero hs hs1 hz j).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (Nat.cast_le.mpr hj) le_rfl) (by linarith only [hs])) hH
  let P := etaMidpoint s
  have he : (cofactorDirichletPrefix s (4*K)+cofactorDirichletPrefix s (4*K+1)+
        cofactorDirichletPrefix s (4*K+2)+cofactorDirichletPrefix s (4*K+3))/4-1 =
      -((P (4*K)+P (4*K+2))/2+a*P (2*K)) := by
    simp only [cofactorDirichletPrefix_eq,if_neg (by omega : 4*K≠0),if_neg (by omega : 4*K+1≠0),
      if_neg (by omega : 4*K+2≠0),if_neg (by omega : 4*K+3≠0),
      show 4*K/2=2*K by omega,show (4*K+1)/2=2*K by omega,
      show (4*K+2)/2=2*K+1 by omega,show (4*K+3)/2=2*K+1 by omega,
      P,etaMidpoint,a]
    ring
  rw [he,norm_neg]
  apply (norm_add_le _ _).trans
  have h₁ := (norm_add_le (P (4*K)) (P (4*K+2))).trans
    (add_le_add (bound (by omega : K≤4*K)) (bound (by omega : K≤4*K+2)))
  rw [norm_div,norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact (add_le_add (div_le_div_of_nonneg_right h₁ (by norm_num : (0:ℝ)≤2))
      (mul_le_mul ha (bound (by omega : K≤2*K)) (norm_nonneg _) (abs_nonneg _))).trans_eq
      (by dsimp only [H,E]; ring)

/-- The logarithmic stencil moment cancels the full harmonic density. -/
theorem cofactor_density_normalization :
    (1+cofactorDyadicCoefficient/2)*Real.log 2=1 := by
  have h := stencil_log_quotient (by decide : 1≤2) 1 0
  rw [stencil_at_two] at h
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  norm_num [h4] at h
  linarith only [h]

#print axioms cofactor_density_normalization
#print axioms innerJump_dyadic_pair
#print axioms cofactorDirichletPrefix_eq
#print axioms cofactorDirichletPrefix_tendsto
#print axioms cofactorDirichletPrefix_at_zero
#print axioms cofactor_zero_selection_at_the_product_cut
#print axioms mean_four_cofactor_caps_at_zero
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
