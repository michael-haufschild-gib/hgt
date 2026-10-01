import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionMixedLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Complete mixed-kernel profile and stable sign boundary

The complete actual and half-line partition source supplies a geometric moment-ratio error.
Its signed sum and complete signed tails give an exact entire profile for the literal mixed
Borel kernel, with exponential control of every fixed derivative order. The profile proves
three limits for its genuine logarithmic derivative, including the scaled derivative limit
`-1`. Fixed-compact convergence then preserves one strict decrease in every sufficiently
large finite logarithmic window.
-/

open Filter Set Topology Complex Metric
open scoped BigOperators
noncomputable section
namespace RHTower

private def msFactorialSeries (b : ℕ→ℝ) (z : ℂ) : ℂ :=
  ∑' n:ℕ,(b n:ℂ)*z^n/(n.factorial:ℂ)

private theorem ms_exp_hasSum (x : ℝ) :
    HasSum (fun n:ℕ=>x^n/(n.factorial:ℝ)) (Real.exp x) := by
  simpa only [←Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

private theorem ms_factorial_term_bound {b : ℕ→ℝ} {C r T : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n)
    {z : ℂ} (hz : ‖z‖ ≤ T) (n : ℕ) :
    ‖(b n:ℂ)*z^n/(n.factorial:ℂ)‖ ≤ C*(r*T)^n/(n.factorial:ℝ) := by
  simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ (C*r^n)*T^n := mul_le_mul (hb n)
      (pow_le_pow_left₀ (norm_nonneg z) hz n) (pow_nonneg (norm_nonneg z) n)
      (mul_nonneg hC (pow_nonneg hr n))
    _ = _ := by rw [mul_pow]; ring1

private theorem ms_factorial_summable {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (z : ℂ) :
    Summable (fun n:ℕ=>‖(b n:ℂ)*z^n/(n.factorial:ℂ)‖) := by
  exact ((ms_exp_hasSum (r*‖z‖)).summable.mul_left C).of_nonneg_of_le
    (fun _=>norm_nonneg _) (fun n=>by
      simpa only [mul_div_assoc] using ms_factorial_term_bound hC hr hb (le_refl _) n)

private theorem ms_factorial_norm_le {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (z : ℂ) :
    ‖msFactorialSeries b z‖ ≤ C*Real.exp (r*‖z‖) := by
  calc
    _ ≤ ∑'n:ℕ,‖(b n:ℂ)*z^n/(n.factorial:ℂ)‖ :=
      norm_tsum_le_tsum_norm (ms_factorial_summable hC hr hb z)
    _ ≤ ∑'n:ℕ,C*((r*‖z‖)^n/(n.factorial:ℝ)) :=
      (ms_factorial_summable hC hr hb z).tsum_le_tsum
        (fun n=>by simpa only [mul_div_assoc] using
          ms_factorial_term_bound hC hr hb (le_refl _) n)
        ((ms_exp_hasSum _).summable.mul_left C)
    _ = _ := by rw [tsum_mul_left,←(ms_exp_hasSum _).tsum_eq]

private theorem ms_factorial_analyticAt {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (z : ℂ) :
    AnalyticAt ℂ (msFactorialSeries b) z := by
  let T : ℝ := ‖z‖+1
  have hd : DifferentiableOn ℂ (msFactorialSeries b) (ball 0 T) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((ms_exp_hasSum (r*T)).summable.mul_left C) ?_ isOpen_ball ?_
    · intro n
      fun_prop
    · intro n w hw
      simpa only [mul_div_assoc] using ms_factorial_term_bound hC hr hb
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) n
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simp [T]))

private theorem ms_factorial_deriv {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (z : ℂ) :
    deriv (msFactorialSeries b) z=msFactorialSeries (fun n=>b (n+1)) z := by
  let T : ℝ := ‖z‖+1
  have hh := Complex.hasSum_deriv_of_summable_norm
    ((ms_exp_hasSum (r*T)).summable.mul_left C)
    (F:=fun n:ℕ=>fun w:ℂ=>(b n:ℂ)*w^n/(n.factorial:ℂ))
    (fun n=>by fun_prop) isOpen_ball
    (fun n w hw=>by
      simpa only [mul_div_assoc] using ms_factorial_term_bound hC hr hb
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) n)
    (by simp [T] : z∈ball (0:ℂ) T)
  have h0 : deriv (fun w:ℂ=>(b 0:ℂ)*w^0/(Nat.factorial 0:ℂ)) z=0 := by simp
  have hsucc (n : ℕ) :
      deriv (fun w:ℂ=>(b (n+1):ℂ)*w^(n+1)/((n+1).factorial:ℂ)) z=
        (b (n+1):ℂ)*z^n/(n.factorial:ℂ) := by
    rw [deriv_div_const,deriv_const_mul_field,deriv_pow_field]
    simp only [Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hn : (n+1:ℂ)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hf : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  unfold msFactorialSeries
  rw [←hh.tsum_eq,hh.summable.tsum_eq_zero_add,h0,zero_add]
  apply tsum_congr
  exact hsucc

private theorem ms_factorial_iterated {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (m : ℕ) :
    iteratedDeriv m (msFactorialSeries b)=msFactorialSeries (fun n=>b (n+m)) := by
  induction m with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    have hs (n : ℕ) : |b (n+m)| ≤ (C*r^m)*r^n := by
      exact (hb _).trans_eq (by rw [pow_add]; ring1)
    rw [ms_factorial_deriv (mul_nonneg hC (pow_nonneg hr m)) hr hs]
    apply congrArg (fun a:ℕ→ℝ=>msFactorialSeries a z)
    funext n
    congr 1
    omega

private theorem ms_factorial_iterated_norm_le {b : ℕ→ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hb : ∀n,|b n| ≤ C*r^n) (m : ℕ) (z : ℂ) :
    ‖iteratedDeriv m (msFactorialSeries b) z‖ ≤ (C*r^m)*Real.exp (r*‖z‖) := by
  rw [ms_factorial_iterated hC hr hb]
  apply ms_factorial_norm_le (mul_nonneg hC (pow_nonneg hr m)) hr
  intro n
  exact (hb _).trans_eq (by rw [pow_add]; ring1)

private theorem ms_geometric_abs_summable {v : ℕ→ℝ} {E : ℝ}
    (_hE : 0 ≤ E) (hv : ∀j,|v j| ≤ E*(1/9:ℝ)^j) :
    Summable (fun j:ℕ=>|v j|) := by
  exact ((hasSum_geometric_of_abs_lt_one (by norm_num : |(1/9:ℝ)| < 1)).summable.mul_left E).of_nonneg_of_le (fun _=>abs_nonneg _) hv

private theorem ms_geometric_tsum_bound {v : ℕ→ℝ} {E : ℝ}
    (hE : 0 ≤ E) (hv : ∀j,|v j| ≤ E*(1/9:ℝ)^j) :
    |∑'j:ℕ,v j| ≤ 9*E/8 := by
  have hs := ms_geometric_abs_summable hE hv
  have hns : Summable (fun j:ℕ=>‖v j‖) := by simpa only [Real.norm_eq_abs] using hs
  have hg := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1/9:ℝ)| < 1)).mul_left E
  calc
    _ ≤ ∑'j:ℕ,|v j| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hns
    _ ≤ ∑'j:ℕ,E*(1/9:ℝ)^j := hs.tsum_le_tsum hv hg.summable
    _ = _ := by rw [hg.tsum_eq]; norm_num; ring1

private theorem ms_geometric_tail_bound {v : ℕ→ℝ} {E : ℝ}
    (hE : 0 ≤ E) (hv : ∀j,|v j| ≤ E*(1/9:ℝ)^j) (j : ℕ) :
    |∑'k:ℕ,v (j+1+k)| ≤ (E/8)*(1/9:ℝ)^j := by
  have hh (k : ℕ) : |v (j+1+k)| ≤ (E*(1/9:ℝ)^(j+1))*(1/9:ℝ)^k := by
    exact (hv _).trans_eq (by rw [pow_add]; ring1)
  have he : 0 ≤ E*(1/9:ℝ)^(j+1) := by positivity
  calc
    _ ≤ 9*(E*(1/9:ℝ)^(j+1))/8 := ms_geometric_tsum_bound he hh
    _ = _ := by rw [pow_succ]; ring1

private theorem ms_geometric_split {v : ℕ→ℝ} {E : ℝ}
    (hE : 0 ≤ E) (hv : ∀j,|v j| ≤ E*(1/9:ℝ)^j) (j : ℕ) :
    (∑'k:ℕ,v k)=(∑a∈Finset.range (j+1),v a)+(∑'k:ℕ,v (j+1+k)) := by
  have hs : Summable v := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using ms_geometric_abs_summable hE hv
  simpa only [Nat.add_comm] using (hs.sum_add_tsum_nat_add (j+1)).symm


private def msEvenSeries (a : ℕ→ℝ) (z : ℂ) : ℂ :=
  ∑'j:ℕ,(a j:ℂ)*z^(2*j)

private theorem ms_evenTerm_norm_le {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ T) (j : ℕ) :
    ‖(a j:ℂ)*z^(2*j)‖ ≤ K*((R*T)^(2*j)/((2*j).factorial:ℝ)) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
  calc
    _  ≤  (K*R^(2*j)/((2*j).factorial:ℝ))*T^(2*j) :=
      mul_le_mul (ha j) (pow_le_pow_left₀ (norm_nonneg z) hz _)
        (pow_nonneg (norm_nonneg z) _) (div_nonneg (mul_nonneg hK (by
          rw [pow_mul]; positivity)) (Nat.cast_nonneg _))
    _ = _ := by rw [mul_pow]; ring1

private theorem ms_even_summable_norm {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    Summable (fun j:ℕ=>‖(a j:ℂ)*z^(2*j)‖) := by
  exact ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K).of_nonneg_of_le
    (fun _=>norm_nonneg _) (ms_evenTerm_norm_le hK ha (le_refl _) )

private theorem ms_even_norm_le {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    ‖msEvenSeries a z‖ ≤ K*Real.cosh (R*‖z‖) := by
  calc
    _  ≤  ∑'j:ℕ,‖(a j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (ms_even_summable_norm hK ha z)
    _  ≤  ∑'j:ℕ,K*((R*‖z‖)^(2*j)/((2*j).factorial:ℝ)) :=
      (ms_even_summable_norm hK ha z).tsum_le_tsum
        (ms_evenTerm_norm_le hK ha (le_refl _))
        ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K)
    _ = _ := by rw [tsum_mul_left,← (Real.hasSum_cosh _).tsum_eq]

private theorem ms_even_uniform {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j))
      (msEvenSeries a) (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    ((Real.hasSum_cosh (R*T)).summable.mul_left K)
    (fun j z hz=>ms_evenTerm_norm_le hK ha
      (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

private theorem ms_even_locallyUniform {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro S hS hSc
  obtain ⟨T,hT⟩ := hSc.bddAbove_image continuous_norm.continuousOn
  refine ⟨_,(Real.hasSum_cosh (R*T)).summable.mul_left K,?_⟩
  intro j z hz
  exact ms_evenTerm_norm_le hK ha (hT ⟨z,hz,rfl⟩) j

private theorem ms_even_analyticAt {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    AnalyticAt ℂ (msEvenSeries a) z := by
  let T : ℝ := ‖z‖+1
  have hd : DifferentiableOn ℂ (msEvenSeries a) (ball 0 T) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((Real.hasSum_cosh (R*T)).summable.mul_left K) ?_ isOpen_ball ?_
    · intro j
      fun_prop
    · intro j w hw
      exact ms_evenTerm_norm_le hK ha
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) j
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simp [T]))

private theorem ms_even_ofReal (a : ℕ→ℝ) (t : ℝ) :
    msEvenSeries a (t:ℂ)=(∑'j:ℕ,a j*t^(2*j):ℝ) := by
  unfold msEvenSeries
  simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
  exact (Complex.ofReal_tsum _).symm

private theorem ms_even_realSummable {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (t : ℝ) :
    Summable (fun j:ℕ=>a j*t^(2*j)) := by
  have h := (ms_even_summable_norm hK ha (t:ℂ)).of_norm
  have hre := h.mapL Complex.reCLM
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.reCLM_apply,Complex.ofReal_re] using hre

private theorem ms_even_ge_one {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (ha0 : a 0=1) (haPos : ∀j,0 ≤ a j) (t : ℝ) :
    1 ≤ ∑'j:ℕ,a j*t^(2*j) := by
  have h := (ms_even_realSummable hK ha t).le_tsum 0
    (fun j _=>mul_nonneg (haPos j) (by rw [pow_mul]; positivity))
  simpa only [ha0,mul_zero,pow_zero,mul_one] using h


private def msRemainder (c : ℕ→ℝ) (z : ℂ) : ℂ :=
  ∑'j:ℕ,(c j:ℂ)*(2*z)^(2*j)/((2*j).factorial:ℂ)

private def msEvenCoeff (c : ℕ→ℝ) (j : ℕ) : ℝ :=
  c j*2^(2*j)/((2*j).factorial:ℝ)

private theorem ms_evenCoeff_bound {c : ℕ→ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (hc : ∀j,|c j| ≤ C*(1/9:ℝ)^j) (j : ℕ) :
    |msEvenCoeff c j| ≤ C*(2/3:ℝ)^(2*j)/((2*j).factorial:ℝ) := by
  have hp : (1/9:ℝ)^j*2^(2*j)=(2/3:ℝ)^(2*j) := by
    rw [pow_mul,pow_mul,←mul_pow]
    norm_num
  unfold msEvenCoeff
  rw [abs_div,abs_mul,abs_of_nonneg (by positivity:0 ≤ (2:ℝ)^(2*j)),
    abs_of_nonneg (show (0:ℝ) ≤ ((2*j).factorial:ℝ) from Nat.cast_nonneg _)]
  calc
    _ ≤ (C*(1/9:ℝ)^j)*2^(2*j)/((2*j).factorial:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hc j) (by positivity))
        (Nat.cast_nonneg _)
    _ = _ := by rw [mul_assoc,hp]

private theorem ms_remainder_eq_even (c : ℕ→ℝ) :
    msRemainder c=msEvenSeries (msEvenCoeff c) := by
  funext z
  unfold msRemainder msEvenSeries msEvenCoeff
  apply tsum_congr
  intro j
  push_cast
  rw [mul_pow]
  ring1

private def msFullCoeff (c : ℕ→ℝ) (n : ℕ) : ℝ :=
  if n%2=0 then c (n/2)*2^n else 0

private theorem ms_fullCoeff_bound {c : ℕ→ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀j,|c j| ≤ C*(1/9:ℝ)^j) (n : ℕ) :
    |msFullCoeff c n| ≤ C*(2/3:ℝ)^n := by
  by_cases hn : n%2=0
  · have he : n=2*(n/2) := by omega
    simp only [msFullCoeff,hn,if_true,abs_mul,abs_of_nonneg (by positivity:0 ≤ (2:ℝ)^n)]
    calc
      _ ≤ (C*(1/9:ℝ)^(n/2))*2^n :=
        mul_le_mul_of_nonneg_right (hc _) (by positivity)
      _ = _ := by
        have hp : (1/9:ℝ)^(n/2)*2^n=(2/3:ℝ)^n := by
          rw [he,show 2*(n/2)/2=n/2 by omega]
          rw [pow_mul,pow_mul,←mul_pow]
          norm_num
        rw [mul_assoc,hp]
  · simp only [msFullCoeff,hn,if_false,abs_zero]
    positivity

private theorem ms_remainder_eq_factorial {c : ℕ→ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀j,|c j| ≤ C*(1/9:ℝ)^j) :
    msRemainder c=msFactorialSeries (msFullCoeff c) := by
  funext z
  have hs := (ms_even_summable_norm hC (ms_evenCoeff_bound hC hc) z).of_norm
  have he : HasSum
      (fun j:ℕ=>(msFullCoeff c (2*j):ℂ)*z^(2*j)/((2*j).factorial:ℂ))
      (msRemainder c z) := by
    rw [ms_remainder_eq_even]
    apply hs.hasSum.congr_fun
    intro j
    simp [msFullCoeff,msEvenCoeff]
    ring1
  have ho : HasSum
      (fun j:ℕ=>(msFullCoeff c (2*j+1):ℂ)*z^(2*j+1)/((2*j+1).factorial:ℂ)) 0 := by
    simp [msFullCoeff]
  have h : HasSum (fun n:ℕ=>(msFullCoeff c n:ℂ)*z^n/(n.factorial:ℂ))
      (msRemainder c z+0) := he.even_add_odd ho
  simpa only [add_zero,msFactorialSeries] using h.tsum_eq.symm

private theorem ms_remainder_iterated_norm_le {c : ℕ→ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀j,|c j| ≤ C*(1/9:ℝ)^j) (m : ℕ) (z : ℂ) :
    ‖iteratedDeriv m (msRemainder c) z‖  ≤
      (C*(2/3:ℝ)^m)*Real.exp ((2/3)*‖z‖) := by
  rw [ms_remainder_eq_factorial hC hc]
  exact ms_factorial_iterated_norm_le hC (by norm_num) (ms_fullCoeff_bound hC hc) m z

private theorem ms_hasSum_weighted_cosh (z : ℂ) :
    HasSum (fun j:ℕ=>(j+1:ℂ)*(2*z)^(2*j)/((2*j).factorial:ℂ))
      (Complex.cosh (2*z)+z*Complex.sinh (2*z)) := by
  have hs : HasSum
      (fun n:ℕ=>(n+1:ℂ)*(2*z)^(2*(n+1))/((2*(n+1)).factorial:ℂ))
      (z*Complex.sinh (2*z)) := by
    apply ((Complex.hasSum_sinh (2*z)).mul_left z).congr_fun
    intro n
    have he : 2*(n+1)=2*n+1+1 := by omega
    rw [he,Nat.factorial_succ,pow_succ]
    push_cast
    have hn : (2*(n:ℂ)+1+1)≠0 := by
      exact_mod_cast (show 2*n+1+1≠0 by omega)
    have hf : ((2*n+1).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hh : (2*(n:ℂ)+1+1)=2*((n:ℂ)+1) := by ring1
    rw [hh]
    have hn1 : (n:ℂ)+1≠0 := by exact_mod_cast (show n+1≠0 by omega)
    field_simp [hf,hn1]
  have hzero : HasSum
      (fun n:ℕ=>(n:ℂ)*(2*z)^(2*n)/((2*n).factorial:ℂ))
      (z*Complex.sinh (2*z)) := by
    have hh : HasSum
        (fun n:ℕ=>((n+1:ℕ):ℂ)*(2*z)^(2*(n+1))/((2*(n+1)).factorial:ℂ))
        (z*Complex.sinh (2*z)) := by simpa only [Nat.cast_add,Nat.cast_one] using hs
    have hz := HasSum.zero_add
      (f:=fun n:ℕ=>(n:ℂ)*(2*z)^(2*n)/((2*n).factorial:ℂ)) hh
    simpa only [Nat.cast_zero,zero_mul,zero_div,zero_add] using hz
  have hadd := hzero.add (Complex.hasSum_cosh (2*z))
  have hout : HasSum (fun j:ℕ=>(j+1:ℂ)*(2*z)^(2*j)/((2*j).factorial:ℂ))
      (z*Complex.sinh (2*z)+Complex.cosh (2*z)) := by
    apply hadd.congr_fun
    intro n
    ring1
  simpa only [add_comm] using hout

/-- Signed sum of complete actual moment-ratio discrepancies from their limiting value. -/
def liClockPairedEtaInfinitePartitionMixedMomentErrorSum : ℝ :=
  ∑'j:ℕ,(liClockPairedEtaInfinitePartitionMomentRatio j-
    liClockPairedEtaInfinitePartitionComparisonLimit)

/-- Complete signed discrepancy tail after the first `j + 1` moment ratios. -/
def liClockPairedEtaInfinitePartitionMixedMomentErrorTail (j : ℕ) : ℝ :=
  ∑'k:ℕ,(liClockPairedEtaInfinitePartitionMomentRatio (j+1+k)-
    liClockPairedEtaInfinitePartitionComparisonLimit)

/-- Entire factorial series of the complete signed moment-error tails. -/
def liClockPairedEtaInfinitePartitionMixedRemainderComplex (z : ℂ) : ℂ :=
  ∑'j:ℕ,(liClockPairedEtaInfinitePartitionMixedMomentErrorTail j:ℂ)*
    (2*z)^(2*j)/((2*j).factorial:ℂ)

/-- Real restriction of the signed entire moment-error remainder. -/
def liClockPairedEtaInfinitePartitionMixedRemainder (t : ℝ) : ℝ :=
  ∑'j:ℕ,liClockPairedEtaInfinitePartitionMixedMomentErrorTail j*
    (2*t)^(2*j)/((2*j).factorial:ℝ)

/-- Literal mixed Borel kernel with its leading exponential growth removed. -/
def liClockPairedEtaInfinitePartitionMixedScaledKernel (t : ℝ) : ℝ :=
  Real.exp (-2*t)*liClockPairedEtaInfinitePartitionMixedBorelKernel t

/-- Real logarithmic derivative of the literal finite mixed Borel kernel. -/
def liClockPairedEtaPartitionMixedLogDerivative (N : ℕ) (t : ℝ) : ℝ :=
  deriv (liClockPairedEtaPartitionMixedBorelKernel N) t/
    liClockPairedEtaPartitionMixedBorelKernel N t

/-- Real logarithmic derivative of the literal complete mixed Borel kernel. -/
def liClockPairedEtaInfinitePartitionMixedLogDerivative (t : ℝ) : ℝ :=
  deriv liClockPairedEtaInfinitePartitionMixedBorelKernel t/
    liClockPairedEtaInfinitePartitionMixedBorelKernel t

private abbrev msE : ℝ := liClockPairedEtaInfinitePartitionMomentErrorScale
private abbrev msLambda : ℝ := liClockPairedEtaInfinitePartitionComparisonLimit
private abbrev msSigma : ℝ := liClockPairedEtaInfinitePartitionMixedMomentErrorSum
private abbrev msTail := liClockPairedEtaInfinitePartitionMixedMomentErrorTail

private theorem ms_error_bound (j : ℕ) :
    |liClockPairedEtaInfinitePartitionMomentRatio j-msLambda| ≤ msE*(1/9:ℝ)^j :=
  liClockPairedEtaInfinitePartitionMomentRatio_error_le j

private theorem msE_nonneg : 0 ≤ msE :=
  liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg

/-- Absolute summability and exact signed sum, with the complete geometric error bound. -/
theorem liClockPairedEtaInfinitePartitionMixedMomentErrorSum_spec :
    Summable (fun j:ℕ=>|liClockPairedEtaInfinitePartitionMomentRatio j-
      liClockPairedEtaInfinitePartitionComparisonLimit|) ∧
    HasSum (fun j:ℕ=>liClockPairedEtaInfinitePartitionMomentRatio j-
      liClockPairedEtaInfinitePartitionComparisonLimit)
      liClockPairedEtaInfinitePartitionMixedMomentErrorSum ∧
    |liClockPairedEtaInfinitePartitionMixedMomentErrorSum|  ≤
      9*liClockPairedEtaInfinitePartitionMomentErrorScale/8 := by
  unfold liClockPairedEtaInfinitePartitionMixedMomentErrorSum
  have hs := ms_geometric_abs_summable msE_nonneg ms_error_bound
  refine ⟨hs,?_,ms_geometric_tsum_bound msE_nonneg ms_error_bound⟩
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using hs

/-- Exact prefix-tail splitting and the geometric bound for every complete signed tail. -/
theorem liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec (j : ℕ) :
    |liClockPairedEtaInfinitePartitionMixedMomentErrorTail j|  ≤
      (liClockPairedEtaInfinitePartitionMomentErrorScale/8)*(1/9:ℝ)^j ∧
    liClockPairedEtaInfinitePartitionMixedMomentErrorSum=
      (∑a∈Finset.range (j+1),(liClockPairedEtaInfinitePartitionMomentRatio a-
        liClockPairedEtaInfinitePartitionComparisonLimit))+
      liClockPairedEtaInfinitePartitionMixedMomentErrorTail j := by
  unfold liClockPairedEtaInfinitePartitionMixedMomentErrorSum
    liClockPairedEtaInfinitePartitionMixedMomentErrorTail
  exact ⟨ms_geometric_tail_bound msE_nonneg ms_error_bound j,
    ms_geometric_split msE_nonneg ms_error_bound j⟩

private theorem ms_tail_bound (j : ℕ) : |msTail j| ≤ (msE/8)*(1/9:ℝ)^j :=
  (liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec j).1

private theorem ms_HC_eq_even :
    liClockPairedEtaInfinitePartitionMixedRemainderComplex=
      msEvenSeries (msEvenCoeff msTail) := ms_remainder_eq_even msTail

private theorem ms_H_term (j : ℕ) (z : ℂ) :
    (msTail j:ℂ)*(2*z)^(2*j)/((2*j).factorial:ℂ)=
      (msEvenCoeff msTail j:ℂ)*z^(2*j) := by
  unfold msEvenCoeff
  push_cast
  rw [mul_pow]
  ring1

/-- Absolute convergence of the signed remainder series at every complex clock. -/
theorem summable_norm_liClockPairedEtaInfinitePartitionMixedRemainderTerm (z : ℂ) :
    Summable (fun j:ℕ=>‖(liClockPairedEtaInfinitePartitionMixedMomentErrorTail j:ℂ)*
      (2*z)^(2*j)/((2*j).factorial:ℂ)‖) := by
  simp_rw [ms_H_term]
  exact ms_even_summable_norm (div_nonneg msE_nonneg (by norm_num))
    (ms_evenCoeff_bound (div_nonneg msE_nonneg (by norm_num)) ms_tail_bound) z

/-- Uniform convergence of the complete remainder series on each fixed complex disk. -/
theorem hasSumUniformlyOn_liClockPairedEtaInfinitePartitionMixedRemainderComplex
    (T : ℝ) (_hT : 0 ≤ T) :
    HasSumUniformlyOn
      (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaInfinitePartitionMixedMomentErrorTail j:ℂ)*
        (2*z)^(2*j)/((2*j).factorial:ℂ))
      liClockPairedEtaInfinitePartitionMixedRemainderComplex (closedBall (0:ℂ) T) := by
  simp_rw [ms_H_term]
  rw [ms_HC_eq_even]
  exact ms_even_uniform (div_nonneg msE_nonneg (by norm_num))
    (ms_evenCoeff_bound (div_nonneg msE_nonneg (by norm_num)) ms_tail_bound)

/-- The literal signed remainder is entire. -/
theorem analyticAt_liClockPairedEtaInfinitePartitionMixedRemainderComplex (z : ℂ) :
    AnalyticAt ℂ liClockPairedEtaInfinitePartitionMixedRemainderComplex z := by
  rw [ms_HC_eq_even]
  exact ms_even_analyticAt (div_nonneg msE_nonneg (by norm_num))
    (ms_evenCoeff_bound (div_nonneg msE_nonneg (by norm_num)) ms_tail_bound) z

/-- Exact complex-to-real restriction of the signed remainder. -/
theorem liClockPairedEtaInfinitePartitionMixedRemainderComplex_ofReal (t : ℝ) :
    liClockPairedEtaInfinitePartitionMixedRemainderComplex (t:ℂ)=
      (liClockPairedEtaInfinitePartitionMixedRemainder t:ℂ) := by
  unfold liClockPairedEtaInfinitePartitionMixedRemainderComplex
    liClockPairedEtaInfinitePartitionMixedRemainder
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  push_cast
  rfl

/-- Complete hyperbolic-cosine envelope for every complex clock. -/
theorem norm_liClockPairedEtaInfinitePartitionMixedRemainderComplex_le (z : ℂ) :
    ‖liClockPairedEtaInfinitePartitionMixedRemainderComplex z‖  ≤
      (liClockPairedEtaInfinitePartitionMomentErrorScale/8)*Real.cosh (2*‖z‖/3) := by
  rw [ms_HC_eq_even]
  have he : (2/3:ℝ)*‖z‖=2*‖z‖/3 := by ring1
  simpa only [he] using ms_even_norm_le (div_nonneg msE_nonneg (by norm_num))
    (ms_evenCoeff_bound (div_nonneg msE_nonneg (by norm_num)) ms_tail_bound) z

private theorem ms_entire_smooth {f : ℂ→ℂ} (hf : ∀z,AnalyticAt ℂ f z) :
    ContDiff ℂ ⊤ f :=
  (show AnalyticOnNhd ℂ f univ from fun z _=>hf z).contDiff

private theorem ms_iteratedDeriv_re {f : ℂ→ℂ} {g : ℝ→ℝ}
    (hf : ∀z,AnalyticAt ℂ f z) (he : ∀t:ℝ,(f (t:ℂ)).re=g t) (m : ℕ) (t : ℝ) :
    iteratedDeriv m g t=(iteratedDeriv m f (t:ℂ)).re := by
  induction m generalizing t with
  | zero => simpa only [iteratedDeriv_zero] using (he t).symm
  | succ m ih =>
    rw [iteratedDeriv_succ,iteratedDeriv_succ]
    have hg : iteratedDeriv m g=(fun t:ℝ=>(iteratedDeriv m f (t:ℂ)).re) := funext ih
    rw [hg]
    exact (((ms_entire_smooth hf).differentiable_iteratedDeriv m
      (by simp)).differentiableAt.hasDerivAt.real_of_complex).deriv

/-- Exponential control of every fixed real derivative order of the actual remainder. -/
theorem abs_iteratedDeriv_liClockPairedEtaInfinitePartitionMixedRemainder_le
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv m liClockPairedEtaInfinitePartitionMixedRemainder t|  ≤
      (liClockPairedEtaInfinitePartitionMomentErrorScale/8)*(2/3:ℝ)^m*
        Real.exp (2*t/3) := by
  have he := ms_iteratedDeriv_re
    (g:=liClockPairedEtaInfinitePartitionMixedRemainder)
    analyticAt_liClockPairedEtaInfinitePartitionMixedRemainderComplex
    (fun t=>by rw [liClockPairedEtaInfinitePartitionMixedRemainderComplex_ofReal,Complex.ofReal_re]) m t
  rw [he]
  calc
    _ ≤ ‖iteratedDeriv m liClockPairedEtaInfinitePartitionMixedRemainderComplex (t:ℂ)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ (msE/8)*(2/3:ℝ)^m*Real.exp (2*t/3) := by
      have h := ms_remainder_iterated_norm_le
        (div_nonneg msE_nonneg (by norm_num)) ms_tail_bound m (t:ℂ)
      change ‖iteratedDeriv m (msRemainder msTail) (t:ℂ)‖ ≤ _
      have he : (2/3:ℝ)*t=2*t/3 := by ring1
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,he] using h

private theorem ms_prefix_profile (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j=
      msLambda*((j:ℝ)+1)+msSigma-msTail j := by
  have h := (liClockPairedEtaInfinitePartitionMixedMomentErrorTail_spec j).2
  have he : msSigma=liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j-
      ((j:ℝ)+1)*msLambda+msTail j := by
    simpa [liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix,
      Finset.sum_sub_distrib,Finset.sum_const] using h
  linarith

/-- Exact full-source complex profile, retaining the complete signed entire remainder. -/
theorem liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_eq_profile (z : ℂ) :
    liClockPairedEtaInfinitePartitionMixedBorelKernelComplex z=
      (liClockPairedEtaInfinitePartitionComparisonLimit:ℂ)*z*Complex.sinh (2*z)+
      ((liClockPairedEtaInfinitePartitionComparisonLimit+
        liClockPairedEtaInfinitePartitionMixedMomentErrorSum:ℝ):ℂ)*Complex.cosh (2*z)-
      liClockPairedEtaInfinitePartitionMixedRemainderComplex z := by
  have hH : HasSum
      (fun j:ℕ=>(msTail j:ℂ)*(2*z)^(2*j)/((2*j).factorial:ℂ))
      (liClockPairedEtaInfinitePartitionMixedRemainderComplex z) := by
    unfold liClockPairedEtaInfinitePartitionMixedRemainderComplex
    exact (summable_norm_liClockPairedEtaInfinitePartitionMixedRemainderTerm z).of_norm.hasSum
  have hs := (((ms_hasSum_weighted_cosh z).mul_left (msLambda:ℂ)).add
    ((Complex.hasSum_cosh (2*z)).mul_left (msSigma:ℂ))).sub hH
  have hv : (msLambda:ℂ)*(Complex.cosh (2*z)+z*Complex.sinh (2*z))+
      (msSigma:ℂ)*Complex.cosh (2*z)-liClockPairedEtaInfinitePartitionMixedRemainderComplex z=
      (msLambda:ℂ)*z*Complex.sinh (2*z)+((msLambda+msSigma:ℝ):ℂ)*
        Complex.cosh (2*z)-liClockPairedEtaInfinitePartitionMixedRemainderComplex z := by
    push_cast
    ring1
  rw [hv] at hs
  have hp : HasSum
      (fun j:ℕ=>(liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j:ℂ)*
        (2*z)^(2*j)/((2*j).factorial:ℂ))
      ((msLambda:ℂ)*z*Complex.sinh (2*z)+((msLambda+msSigma:ℝ):ℂ)*
        Complex.cosh (2*z)-liClockPairedEtaInfinitePartitionMixedRemainderComplex z) := by
    apply hs.congr_fun
    intro j
    rw [ms_prefix_profile]
    push_cast
    ring1
  have hterm (j : ℕ) :
      (liClockPairedEtaInfinitePartitionMixedEvenMoment j:ℂ)*z^(2*j)/
        ((2*j).factorial:ℂ)^2=
      (liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j:ℂ)*
        (2*z)^(2*j)/((2*j).factorial:ℂ) := by
    rw [liClockPairedEtaInfinitePartitionMixedEvenMoment_eq_factorial_prefix]
    push_cast
    rw [mul_pow]
    have hf : ((2*j).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hpow : (4:ℂ)^j=2^(2*j) := by rw [pow_mul]; norm_num
    rw [hpow]
    field_simp
  unfold liClockPairedEtaInfinitePartitionMixedBorelKernelComplex
  simp_rw [hterm]
  exact hp.tsum_eq

private def msLinearProfile (a b : ℝ) (H : ℝ→ℝ) (t : ℝ) : ℝ :=
  a*t+b+(-a*t+b)*Real.exp (-4*t)-Real.exp (-2*t)*H t

private def msLinearProfile1 (a b : ℝ) (H : ℝ→ℝ) (t : ℝ) : ℝ :=
  a+(4*a*t-a-4*b)*Real.exp (-4*t)+Real.exp (-2*t)*(2*H t-deriv H t)

private def msLinearProfile2 (a b : ℝ) (H : ℝ→ℝ) (t : ℝ) : ℝ :=
  (-16*a*t+8*a+16*b)*Real.exp (-4*t)-
    Real.exp (-2*t)*(4*H t-4*deriv H t+iteratedDeriv 2 H t)

private theorem ms_exp_neg_hasDeriv (k t : ℝ) :
    HasDerivAt (fun x:ℝ=>Real.exp (-k*x)) (-k*Real.exp (-k*t)) t := by
  have h : HasDerivAt (fun x:ℝ=>Real.exp (-k*x)) (Real.exp (-k*t)*(-k)) t := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (Real.hasDerivAt_exp (-k*t)).comp t ((hasDerivAt_id t).const_mul (-k))
  convert h using 1
  ring1

private theorem ms_linear_profile_hasDeriv (a b : ℝ) {H : ℝ→ℝ}
    (hH : ContDiff ℝ ⊤ H) (t : ℝ) :
    HasDerivAt (msLinearProfile a b H) (msLinearProfile1 a b H t) t := by
  have hh : HasDerivAt H (deriv H t) t := by
    simpa only [iteratedDeriv_zero] using
      (hH.differentiable_iteratedDeriv 0 (by simp)).differentiableAt.hasDerivAt
  have hs := (((hasDerivAt_id t).const_mul a).add_const b).add
    ((((hasDerivAt_id t).const_mul (-a)).add_const b).mul (ms_exp_neg_hasDeriv 4 t))
  have hf := hs.sub ((ms_exp_neg_hasDeriv 2 t).mul hh)
  convert hf using 1 <;> first | rfl | (dsimp only [msLinearProfile1,id_eq]; ring1)

private theorem ms_linear_profile1_hasDeriv (a b : ℝ) {H : ℝ→ℝ}
    (hH : ContDiff ℝ ⊤ H) (t : ℝ) :
    HasDerivAt (msLinearProfile1 a b H) (msLinearProfile2 a b H t) t := by
  have hh : HasDerivAt H (deriv H t) t := by
    simpa only [iteratedDeriv_zero] using
      (hH.differentiable_iteratedDeriv 0 (by simp)).differentiableAt.hasDerivAt
  have hhd : Differentiable ℝ (deriv H) := by
    simpa only [iteratedDeriv_one] using hH.differentiable_iteratedDeriv 1 (by simp)
  have hd : HasDerivAt (deriv H) (iteratedDeriv 2 H t) t := by
    simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
      hhd.differentiableAt.hasDerivAt (x:=t)
  have hlin := (((hasDerivAt_id t).const_mul (4*a)).sub_const a).sub_const (4*b)
  have hs := (hasDerivAt_const t a).add (hlin.mul (ms_exp_neg_hasDeriv 4 t))
  have hf := hs.add ((ms_exp_neg_hasDeriv 2 t).mul ((hh.const_mul 2).sub hd))
  convert hf using 1 <;> first | rfl | (dsimp only [msLinearProfile2,Pi.sub_apply,id_eq]; ring1)

private theorem ms_pow_exp_limit (n : ℕ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t:ℝ=>t^n*Real.exp (-d*t)) atTop (nhds 0) := by
  simpa only [Real.rpow_natCast] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) d hd

private theorem ms_weighted_H_limit {H : ℝ→ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hH : ∀m:ℕ,∀t:ℝ,0 ≤ t→|iteratedDeriv m H t| ≤ C*(2/3:ℝ)^m*Real.exp (2*t/3))
    (m n : ℕ) :
    Tendsto (fun t:ℝ=>t^n*Real.exp (-2*t)*iteratedDeriv m H t) atTop (nhds 0) := by
  have hg : Tendsto (fun t:ℝ=>(C*(2/3:ℝ)^m)*(t^n*Real.exp (-(4/3:ℝ)*t)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (ms_pow_exp_limit n (by norm_num:0 < (4/3:ℝ)))
  apply squeeze_zero_norm' _ hg
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_of_nonneg ht,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-2*t)*Real.exp (2*t/3)=Real.exp (-(4/3:ℝ)*t) := by
    rw [←Real.exp_add]
    congr 1
    ring1
  calc
    _ ≤ t^n*Real.exp (-2*t)*(C*(2/3:ℝ)^m*Real.exp (2*t/3)) :=
      mul_le_mul_of_nonneg_left (hH m t ht)
        (mul_nonneg (pow_nonneg ht n) (Real.exp_pos _).le)
    _ = (C*(2/3:ℝ)^m)*(t^n*(Real.exp (-2*t)*Real.exp (2*t/3))) := by ring1
    _ = _ := by rw [he]

private theorem ms_linear_profile_limits (a b : ℝ) {H : ℝ→ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hH : ∀m:ℕ,∀t:ℝ,0 ≤ t→|iteratedDeriv m H t| ≤ C*(2/3:ℝ)^m*Real.exp (2*t/3)) :
    Tendsto (fun t:ℝ=>msLinearProfile a b H t/t) atTop (nhds a) ∧
    Tendsto (msLinearProfile1 a b H) atTop (nhds a) ∧
    Tendsto (fun t:ℝ=>t*msLinearProfile2 a b H t) atTop (nhds 0) := by
  have e0 : Tendsto (fun t:ℝ=>Real.exp (-4*t)) atTop (nhds 0) := by
    simpa only [pow_zero,one_mul] using ms_pow_exp_limit 0 (by norm_num:0 < (4:ℝ))
  have e1 : Tendsto (fun t:ℝ=>t*Real.exp (-4*t)) atTop (nhds 0) := by
    simpa only [pow_one] using ms_pow_exp_limit 1 (by norm_num:0 < (4:ℝ))
  have e2 : Tendsto (fun t:ℝ=>t^2*Real.exp (-4*t)) atTop (nhds 0) :=
    ms_pow_exp_limit 2 (by norm_num:0 < (4:ℝ))
  have H00 : Tendsto (fun t:ℝ=>Real.exp (-2*t)*H t) atTop (nhds 0) := by
    simpa only [pow_zero,one_mul,iteratedDeriv_zero] using ms_weighted_H_limit hC hH 0 0
  have H10 : Tendsto (fun t:ℝ=>Real.exp (-2*t)*deriv H t) atTop (nhds 0) := by
    simpa only [pow_zero,one_mul,iteratedDeriv_one] using ms_weighted_H_limit hC hH 1 0
  have H01 : Tendsto (fun t:ℝ=>t*Real.exp (-2*t)*H t) atTop (nhds 0) := by
    simpa only [pow_one,iteratedDeriv_zero] using ms_weighted_H_limit hC hH 0 1
  have H11 : Tendsto (fun t:ℝ=>t*Real.exp (-2*t)*deriv H t) atTop (nhds 0) := by
    simpa only [pow_one,iteratedDeriv_one] using ms_weighted_H_limit hC hH 1 1
  have H21 : Tendsto (fun t:ℝ=>t*Real.exp (-2*t)*iteratedDeriv 2 H t) atTop (nhds 0) := by
    simpa only [pow_one] using ms_weighted_H_limit hC hH 2 1
  have eps : Tendsto
      (fun t:ℝ=>-(a*(t*Real.exp (-4*t)))+b*Real.exp (-4*t)-Real.exp (-2*t)*H t)
      atTop (nhds 0) := by
    simpa only [mul_zero,neg_zero,add_zero,sub_zero] using
      ((tendsto_const_nhds.mul e1).neg.add (tendsto_const_nhds.mul e0)).sub H00
  have p : Tendsto (fun t:ℝ=>a+(b+(-(a*(t*Real.exp (-4*t)))+
      b*Real.exp (-4*t)-Real.exp (-2*t)*H t))*t⁻¹) atTop (nhds a) := by
    simpa only [add_zero,mul_zero] using tendsto_const_nhds.add
      ((tendsto_const_nhds.add eps).mul tendsto_inv_atTop_zero)
  have hp : Tendsto (fun t:ℝ=>msLinearProfile a b H t/t) atTop (nhds a) := p.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp [msLinearProfile]
    field_simp [ht.ne']
    ring1)
  have p1 : Tendsto (fun t:ℝ=>a+(4*a)*(t*Real.exp (-4*t))-
      (a+4*b)*Real.exp (-4*t)+2*(Real.exp (-2*t)*H t)-Real.exp (-2*t)*deriv H t)
      atTop (nhds a) := by
    simpa only [mul_zero,add_zero,sub_zero] using
      (((tendsto_const_nhds.add (tendsto_const_nhds.mul e1)).sub
        (tendsto_const_nhds.mul e0)).add (tendsto_const_nhds.mul H00)).sub H10
  have hp1 : Tendsto (msLinearProfile1 a b H) atTop (nhds a) := p1.congr (by
    intro t
    dsimp [msLinearProfile1]
    ring1)
  have p2 : Tendsto
      (fun t:ℝ=>(-16*a)*(t^2*Real.exp (-4*t))+(8*a+16*b)*(t*Real.exp (-4*t))-
        4*(t*Real.exp (-2*t)*H t)+4*(t*Real.exp (-2*t)*deriv H t)-
        t*Real.exp (-2*t)*iteratedDeriv 2 H t) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero,sub_zero] using
      ((((tendsto_const_nhds.mul e2).add (tendsto_const_nhds.mul e1)).sub
        (tendsto_const_nhds.mul H01)).add (tendsto_const_nhds.mul H11)).sub H21
  have hp2 : Tendsto (fun t:ℝ=>t*msLinearProfile2 a b H t) atTop (nhds 0) := p2.congr (by
    intro t
    dsimp [msLinearProfile2]
    ring1)
  exact ⟨hp,hp1,hp2⟩

private abbrev msB := liClockPairedEtaInfinitePartitionMixedBorelKernel
private abbrev msH := liClockPairedEtaInfinitePartitionMixedRemainder
private abbrev msP := liClockPairedEtaInfinitePartitionMixedScaledKernel
private abbrev msA : ℝ := msLambda/2
private abbrev msConst : ℝ := (msLambda+msSigma)/2

private theorem ms_H_smooth : ContDiff ℝ ⊤ msH := by
  have h := (ms_entire_smooth analyticAt_liClockPairedEtaInfinitePartitionMixedRemainderComplex).real_of_complex
  have he : (fun t:ℝ=>(liClockPairedEtaInfinitePartitionMixedRemainderComplex (t:ℂ)).re)=msH := by
    funext t
    rw [liClockPairedEtaInfinitePartitionMixedRemainderComplex_ofReal,Complex.ofReal_re]
  rw [he] at h
  exact h

private theorem ms_B_real_profile (t : ℝ) :
    msB t=msLambda*t*Real.sinh (2*t)+(msLambda+msSigma)*Real.cosh (2*t)-msH t := by
  apply Complex.ofReal_injective
  simpa only [liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_ofReal,
    liClockPairedEtaInfinitePartitionMixedRemainderComplex_ofReal,
    Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_sinh,
    Complex.ofReal_cosh,Complex.ofReal_ofNat] using
    liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_eq_profile (t:ℂ)

private theorem ms_P_profile (t : ℝ) :
    msP t=msA*t+msConst+(-msA*t+msConst)*Real.exp (-4*t)-
      Real.exp (-2*t)*msH t := by
  have hx : Real.exp (-2*t)*Real.exp (2*t)=1 := by
    rw [←Real.exp_add,show -2*t+2*t=0 by ring1,Real.exp_zero]
  have hy : Real.exp (-2*t)*Real.exp (-2*t)=Real.exp (-4*t) := by
    rw [←Real.exp_add]
    congr 1
    ring1
  change Real.exp (-2*t)*msB t=_
  rw [ms_B_real_profile,Real.sinh_eq,Real.cosh_eq,
    show -(2*t)=-2*t by ring1]
  calc
    _ = msA*t*(Real.exp (-2*t)*Real.exp (2*t))+
      msConst*(Real.exp (-2*t)*Real.exp (2*t))+
      (-msA*t+msConst)*(Real.exp (-2*t)*Real.exp (-2*t))-
      Real.exp (-2*t)*msH t := by dsimp [msA,msConst]; ring1
    _ = _ := by rw [hx,hy]; ring1

private theorem ms_scaled_quotient_limits {p p1 p2 q : ℝ→ℝ} {a : ℝ}
    (ha : 0 < a) (hp : Tendsto (fun t:ℝ=>p t/t) atTop (nhds a))
    (h1 : Tendsto p1 atTop (nhds a))
    (h2 : Tendsto (fun t:ℝ=>t*p2 t) atTop (nhds 0))
    (hpn : ∀t,p t≠0)
    (hq : ∀t,q t=2+p1 t/p t)
    (hdq : ∀t,deriv q t=(p2 t*p t-(p1 t)^2)/(p t)^2) :
    Tendsto q atTop (nhds (2:ℝ)) ∧
    Tendsto (fun t:ℝ=>t*(q t-2)) atTop (nhds (1:ℝ)) ∧
    Tendsto (fun t:ℝ=>t^2*deriv q t) atTop (nhds (-1:ℝ)) := by
  have hr : Tendsto (fun t:ℝ=>p1 t/(p t/t)) atTop (nhds (1:ℝ)) := by
    have hh := (h1.div hp ha.ne').congr
      (f₂:=fun t:ℝ=>p1 t/(p t/t)) (fun _=>rfl)
    simpa only [div_self ha.ne'] using hh
  have hq0 : Tendsto (fun t:ℝ=>2+(p1 t/(p t/t))*t⁻¹) atTop (nhds (2:ℝ)) := by
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add
      (hr.mul tendsto_inv_atTop_zero)
  have hq1 : Tendsto q atTop (nhds (2:ℝ)) := hq0.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [hq]
    field_simp [ht.ne',hpn t])
  have hex : Tendsto (fun t:ℝ=>t*(q t-2)) atTop (nhds (1:ℝ)) := hr.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [hq]
    field_simp [ht.ne',hpn t]
    ring1)
  have hz : Tendsto (fun t:ℝ=>(t*p2 t)/(p t/t)-(p1 t/(p t/t))^2)
      atTop (nhds (-1:ℝ)) := by
    simpa only [zero_div,one_pow,zero_sub,Pi.div_apply] using (h2.div hp ha.ne').sub (hr.pow 2)
  have hd : Tendsto (fun t:ℝ=>t^2*deriv q t) atTop (nhds (-1:ℝ)) := hz.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [hdq]
    field_simp [ht.ne',hpn t])
  exact ⟨hq1,hex,hd⟩

private abbrev msP1 := msLinearProfile1 msA msConst msH
private abbrev msP2 := msLinearProfile2 msA msConst msH
private abbrev msQ := liClockPairedEtaInfinitePartitionMixedLogDerivative

private theorem ms_A_pos : 0 < msA :=
  div_pos liClockPairedEtaInfinitePartitionComparisonLimit_pos (by norm_num)

private theorem ms_P_eq_linear : msP=msLinearProfile msA msConst msH :=
  funext ms_P_profile

private theorem ms_P_hasDeriv (t : ℝ) : HasDerivAt msP (msP1 t) t := by
  rw [ms_P_eq_linear]
  exact ms_linear_profile_hasDeriv msA msConst ms_H_smooth t

private theorem ms_P1_hasDeriv (t : ℝ) : HasDerivAt msP1 (msP2 t) t :=
  ms_linear_profile1_hasDeriv msA msConst ms_H_smooth t

private theorem ms_P_limits :
    Tendsto (fun t:ℝ=>msP t/t) atTop (nhds msA) ∧
    Tendsto msP1 atTop (nhds msA) ∧
    Tendsto (fun t:ℝ=>t*msP2 t) atTop (nhds 0) := by
  have hh := ms_linear_profile_limits msA msConst
    (div_nonneg msE_nonneg (by norm_num))
    (fun m t ht=>abs_iteratedDeriv_liClockPairedEtaInfinitePartitionMixedRemainder_le m ht)
  rw [←ms_P_eq_linear] at hh
  exact hh

/-- The leading mixed-kernel amplitude is half the complete moment-ratio limit. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedBorelKernel_div_clock_exp :
    Tendsto (fun t:ℝ=>liClockPairedEtaInfinitePartitionMixedBorelKernel t/
      (t*Real.exp (2*t))) atTop
      (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2)) :=
  ms_P_limits.1.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    change (Real.exp (-2*t)*msB t)/t=msB t/(t*Real.exp (2*t))
    rw [show -2*t=-(2*t) by ring1,Real.exp_neg]
    field_simp [ht.ne',Real.exp_ne_zero (2*t)])

private theorem ms_P_pos (t : ℝ) : 0 < msP t := by
  change 0 < Real.exp (-2*t)*msB t
  exact mul_pos (Real.exp_pos _) ((by norm_num: (0:ℝ) < 1).trans_le
    (one_le_liClockPairedEtaInfinitePartitionMixedBorelKernel t))

private theorem ms_Q_eq_scaled (t : ℝ) : msQ t=2+msP1 t/msP t := by
  have hb : HasDerivAt msB (deriv msB t) t := by
    simpa only [iteratedDeriv_zero] using
      (contDiff_liClockPairedEtaInfinitePartitionMixedBorelKernel.differentiable_iteratedDeriv 0 (by simp)).differentiableAt.hasDerivAt
  have hh : HasDerivAt msP
      ((-2*Real.exp (-2*t))*msB t+Real.exp (-2*t)*deriv msB t) t := by
    convert (ms_exp_neg_hasDeriv 2 t).mul hb using 1 <;> rfl
  have hP1 : msP1 t=(-2*Real.exp (-2*t))*msB t+Real.exp (-2*t)*deriv msB t := by
    rw [←(ms_P_hasDeriv t).deriv,hh.deriv]
  rw [hP1]
  change deriv msB t/msB t=2+
    ((-2*Real.exp (-2*t))*msB t+Real.exp (-2*t)*deriv msB t)/
      (Real.exp (-2*t)*msB t)
  have hB : msB t≠0 := ne_of_gt ((by norm_num:(0:ℝ) < 1).trans_le
    (one_le_liClockPairedEtaInfinitePartitionMixedBorelKernel t))
  field_simp [hB,Real.exp_ne_zero (-2*t)]
  ring1

private theorem ms_Q_hasDeriv (t : ℝ) :
    HasDerivAt msQ ((msP2 t*msP t-(msP1 t)^2)/(msP t)^2) t := by
  have he : msQ=(fun x:ℝ=>2+msP1 x/msP x) := funext ms_Q_eq_scaled
  rw [he]
  have h := (hasDerivAt_const t (2:ℝ)).add
    ((ms_P1_hasDeriv t).div (ms_P_hasDeriv t) (ms_P_pos t).ne')
  convert h using 1 <;> first | rfl | ring1

private theorem ms_Q_limits :
    Tendsto msQ atTop (nhds (2:ℝ)) ∧
    Tendsto (fun t:ℝ=>t*(msQ t-2)) atTop (nhds (1:ℝ)) ∧
    Tendsto (fun t:ℝ=>t^2*deriv msQ t) atTop (nhds (-1:ℝ)) :=
  ms_scaled_quotient_limits ms_A_pos ms_P_limits.1 ms_P_limits.2.1 ms_P_limits.2.2
    (fun t=>(ms_P_pos t).ne') ms_Q_eq_scaled (fun t=>(ms_Q_hasDeriv t).deriv)

/-- The complete mixed logarithmic derivative tends to two. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedLogDerivative :
    Tendsto liClockPairedEtaInfinitePartitionMixedLogDerivative atTop (nhds (2:ℝ)) :=
  ms_Q_limits.1

/-- The first scaled excess of the complete logarithmic derivative tends to one. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedLogDerivative_scaled_excess :
    Tendsto (fun t:ℝ=>t*(liClockPairedEtaInfinitePartitionMixedLogDerivative t-2))
      atTop (nhds (1:ℝ)) := ms_Q_limits.2.1

/-- The true derivative has scaled limit minus one. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMixedLogDerivative_scaled_deriv :
    Tendsto (fun t:ℝ=>t^2*deriv liClockPairedEtaInfinitePartitionMixedLogDerivative t)
      atTop (nhds (-1:ℝ)) := ms_Q_limits.2.2

/-- The complete logarithmic derivative is eventually above two and strictly decreasing. -/
theorem liClockPairedEtaInfinitePartitionMixedLogDerivative_eventually_above_two_decreasing :
    ∀ᶠt:ℝ in atTop,2 < liClockPairedEtaInfinitePartitionMixedLogDerivative t ∧
      deriv liClockPairedEtaInfinitePartitionMixedLogDerivative t < 0 := by
  have h1 := ms_Q_limits.2.1.eventually (eventually_gt_nhds (by norm_num:(0:ℝ) < 1))
  have h2 := ms_Q_limits.2.2.eventually (eventually_lt_nhds (by norm_num:(-1:ℝ) < 0))
  filter_upwards [h1,h2,eventually_gt_atTop (0:ℝ)] with t ht1 ht2 ht
  constructor
  · nlinarith
  · nlinarith [sq_pos_of_pos ht]

private theorem ms_quotient_error_bound (a b x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |a/x-b/y| ≤ |a-b|+|b| * |x-y| := by
  have hxp : 0 < x := (by norm_num:(0:ℝ) < 1).trans_le hx
  have hyp : 0 < y := (by norm_num:(0:ℝ) < 1).trans_le hy
  have hxy : 1 ≤ x*y := by nlinarith
  have he : a/x-b/y=(a-b)/x+b*(y-x)/(x*y) := by
    field_simp [hxp.ne',hyp.ne']
    ring1
  rw [he]
  calc
    _ ≤ |(a-b)/x|+|b*(y-x)/(x*y)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_add_le ((a-b)/x) (b*(y-x)/(x*y)))
    _ = |a-b|/x+(|b| * |x-y|)/(x*y) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hxp,
        abs_of_pos (mul_pos hxp hyp),abs_sub_comm y x]
    _ ≤ |a-b|+|b| * |x-y| := by
      apply add_le_add
      · apply (div_le_iff₀ hxp).2
        nlinarith [mul_nonneg (abs_nonneg (a-b)) (sub_nonneg.mpr hx)]
      · apply (div_le_iff₀ (mul_pos hxp hyp)).2
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg b) (abs_nonneg (x-y)))
          (sub_nonneg.mpr hxy)]

/-- Uniform convergence of finite logarithmic derivatives on each fixed real compact disk. -/
theorem tendstoUniformlyOn_liClockPairedEtaPartitionMixedLogDerivative
    (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn liClockPairedEtaPartitionMixedLogDerivative
      liClockPairedEtaInfinitePartitionMixedLogDerivative atTop (closedBall (0:ℝ) T) := by
  have hc : Continuous (deriv msB) := by
    simpa only [iteratedDeriv_one] using
      (contDiff_liClockPairedEtaInfinitePartitionMixedBorelKernel.differentiable_iteratedDeriv 1 (by simp)).continuous
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℝ) T).bddAbove_image hc.abs.continuousOn
  have hC0 : 0 ≤ C := (abs_nonneg (deriv msB 0)).trans
    (hC ⟨0,by simpa only [mem_closedBall,dist_self] using hT,rfl⟩)
  have h0 := tendstoUniformlyOn_liClockPairedEtaPartitionMixedBorelKernel_iteratedDeriv 0 T hT
  have h1 := tendstoUniformlyOn_liClockPairedEtaPartitionMixedBorelKernel_iteratedDeriv 1 T hT
  simp only [iteratedDeriv_zero,iteratedDeriv_one] at h0 h1
  rw [Metric.tendstoUniformlyOn_iff] at h0 h1 ⊢
  intro ε hε
  have hd : 0 < ε/(C+1) := div_pos hε (by linarith)
  filter_upwards [h0 (ε/(C+1)) hd,h1 (ε/(C+1)) hd,eventually_ge_atTop 1] with N hn0 hn1 hN
  intro t ht
  have hnpos : 0 < N := by omega
  have hbn := one_le_liClockPairedEtaPartitionMixedBorelKernel hnpos t
  have hbi := one_le_liClockPairedEtaInfinitePartitionMixedBorelKernel t
  have hd0 : |liClockPairedEtaPartitionMixedBorelKernel N t-msB t| < ε/(C+1) := by
    simpa only [Real.dist_eq,abs_sub_comm] using hn0 t ht
  have hd1 : |deriv (liClockPairedEtaPartitionMixedBorelKernel N) t-deriv msB t| < ε/(C+1) := by
    simpa only [Real.dist_eq,abs_sub_comm] using hn1 t ht
  have hdC : |deriv msB t| ≤ C := hC ⟨t,ht,rfl⟩
  rw [Real.dist_eq,abs_sub_comm]
  change |deriv (liClockPairedEtaPartitionMixedBorelKernel N) t/
      liClockPairedEtaPartitionMixedBorelKernel N t-deriv msB t/msB t| < ε
  calc
    _ ≤ |deriv (liClockPairedEtaPartitionMixedBorelKernel N) t-deriv msB t|+
      |deriv msB t| * |liClockPairedEtaPartitionMixedBorelKernel N t-msB t| :=
      ms_quotient_error_bound _ _ _ _ hbn hbi
    _ ≤ |deriv (liClockPairedEtaPartitionMixedBorelKernel N) t-deriv msB t|+
      C*|liClockPairedEtaPartitionMixedBorelKernel N t-msB t| :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hdC (abs_nonneg _))
    _  <  ε/(C+1)+C*(ε/(C+1)) :=
      add_lt_add_of_lt_of_le hd1 (mul_le_mul_of_nonneg_left hd0.le hC0)
    _ = ε := by field_simp [show C+1≠0 by linarith]; ring1

private theorem ms_Q_continuous : Continuous msQ :=
  (show Differentiable ℝ msQ from fun t=>(ms_Q_hasDeriv t).differentiableAt).continuous

/-- One fixed strict decrease survives in every sufficiently large finite logarithmic window. -/
theorem exists_liClockPairedEtaPartitionMixedLogDerivative_stable_window_witness :
    ∃a b:ℝ,0 < a ∧ a < b ∧
      liClockPairedEtaInfinitePartitionMixedLogDerivative b <
        liClockPairedEtaInfinitePartitionMixedLogDerivative a ∧
      ∀c:ℝ,0 < c→∀ᶠN:ℕ in atTop,
        0 < N ∧ b ≤ c*Real.log (2*(N:ℝ)+1) ∧
        liClockPairedEtaPartitionMixedLogDerivative N b <
          liClockPairedEtaPartitionMixedLogDerivative N a ∧
        liClockPairedEtaPartitionMixedBorelKernel N a*
          (liClockPairedEtaPartitionMixedLogDerivative N b-
            liClockPairedEtaPartitionMixedLogDerivative N a) < 0 := by
  have hd : ∀ᶠt:ℝ in atTop,deriv msQ t < 0 :=
    liClockPairedEtaInfinitePartitionMixedLogDerivative_eventually_above_two_decreasing.mono
      (fun _ h=>h.2)
  obtain ⟨R,hR⟩ := eventually_atTop.1 hd
  let a : ℝ := max 1 R
  let b : ℝ := a+1
  have ha : 0 < a := (by norm_num:(0:ℝ) < 1).trans_le (le_max_left _ _)
  have hab : a < b := by dsimp [b]; linarith
  have har : R ≤ a := le_max_right _ _
  have hs : StrictAntiOn msQ (Icc a b) := strictAntiOn_of_deriv_neg (convex_Icc a b)
    ms_Q_continuous.continuousOn (fun t ht=>hR t (har.trans (interior_subset ht).1))
  have hq : msQ b < msQ a := hs ⟨le_refl _,hab.le⟩ ⟨hab.le,le_refl _⟩ hab
  refine ⟨a,b,ha,hab,hq,?_⟩
  intro c hc
  have hcast : Tendsto (fun N:ℕ=>(N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun N:ℕ=>2*(N:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun N=>by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]) hcast
  have hwindow : Tendsto (fun N:ℕ=>c*Real.log (2*(N:ℝ)+1)) atTop atTop :=
    Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp harg)
  have hw : ∀ᶠN:ℕ in atTop,b ≤ c*Real.log (2*(N:ℝ)+1) :=
    hwindow.eventually (eventually_ge_atTop b)
  have hconv := tendstoUniformlyOn_liClockPairedEtaPartitionMixedLogDerivative b (ha.le.trans hab.le)
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  have hδ : 0 < (msQ a-msQ b)/3 := by linarith
  filter_upwards [hw,hconv ((msQ a-msQ b)/3) hδ,eventually_ge_atTop 1] with N hwN hn hN
  have hat : a∈closedBall (0:ℝ) b := by
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_pos ha]
    exact hab.le
  have hbt : b∈closedBall (0:ℝ) b := by
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_pos (ha.trans hab)]
    exact le_refl _
  have hqa := hn a hat
  have hqb := hn b hbt
  rw [Real.dist_eq] at hqa hqb
  have hNq : liClockPairedEtaPartitionMixedLogDerivative N b <
      liClockPairedEtaPartitionMixedLogDerivative N a := by
    have ha' := (abs_lt.mp hqa).2
    have hb' := (abs_lt.mp hqb).1
    linarith
  have hNp : 0 < N := by omega
  refine ⟨hNp,hwN,hNq,?_⟩
  exact mul_neg_of_pos_of_neg (liClockPairedEtaPartitionMixedBorelKernel_pos hNp a)
    (sub_neg.mpr hNq)

/-- Every fixed positive logarithmic-window rate eventually contains a strict decrease. -/
theorem liClockPairedEtaPartitionMixedLogDerivative_eventually_not_monotoneOn_window
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠN:ℕ in atTop,¬MonotoneOn (liClockPairedEtaPartitionMixedLogDerivative N)
      (Icc 0 (c*Real.log (2*(N:ℝ)+1))) := by
  obtain ⟨a,b,ha,hab,_hq,hw⟩ :=
    exists_liClockPairedEtaPartitionMixedLogDerivative_stable_window_witness
  filter_upwards [hw c hc] with N hn
  intro hmono
  have hle := hmono ⟨ha.le,hab.le.trans hn.2.1⟩
    ⟨(ha.trans hab).le,hn.2.1⟩ hab.le
  exact (not_le_of_gt hn.2.2.1) hle

end RHTower
