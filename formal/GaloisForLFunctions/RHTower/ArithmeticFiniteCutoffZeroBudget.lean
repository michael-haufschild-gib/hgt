import GaloisForLFunctions.RHTower.ArithmeticLogarithmicFourierTail
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# A global zero budget for the finite arithmetic source

The complete pole-cleared Bernoulli head is an entire exponential polynomial with a fixed
nonzero anchor at the zeta pole. Jensen bounds its exact matches among actual simple critical
zeros in terms of both height and cutoff. The unconditional superlinear census forces a
polynomial cutoff scale for exact matching. Every fixed cutoff misses a superlinear number
of simple critical zeros; the discrepancy there is exactly the retained centered tail.
These counting constraints do not establish a separating arithmetic sign or RH.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The pole-cleared finite Bernoulli approximation, with its endpoint and mean retained. -/
def finiteCutoffResidual (N : ℕ) (s : ℂ) : ℂ :=
  (s-1)*(∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s))+(N:ℂ)^(1-s)-
    (s-1)*(N:ℂ)^(-s)/2+s*(s-1)*(N:ℂ)^(-s-1)/12

/-- Every positive integer cutoff gives an entire residual. -/
theorem differentiable_finiteCutoffResidual {N : ℕ} (hN : 1 ≤ N) :
    Differentiable ℂ (finiteCutoffResidual N) := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  intro s
  have hp (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f s) :
      DifferentiableAt ℂ (fun z => (N:ℂ)^(f z)) s := hf.const_cpow (Or.inl hn)
  have hsum : DifferentiableAt ℂ (fun z : ℂ => ∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-z)) s := by
    apply DifferentiableAt.fun_sum
    intro n hn
    exact differentiableAt_id.neg.const_cpow (Or.inl (by
      exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)))
  unfold finiteCutoffResidual
  exact (((differentiableAt_id.sub_const 1).mul hsum).add
    (hp _ ((differentiable_const 1).differentiableAt.sub differentiableAt_id))).sub
      (((differentiableAt_id.sub_const 1).mul (hp _ differentiableAt_id.neg)).div_const 2) |>.add
        (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
          (hp _ (differentiableAt_id.neg.sub_const 1))).div_const 12)

/-- Pole removal fixes the same nonzero anchor for every cutoff. -/
@[simp] theorem finiteCutoffResidual_one (N : ℕ) : finiteCutoffResidual N 1=1 := by
  simp [finiteCutoffResidual]

/-- The exact discrepancy is the complete centered Bernoulli tail. -/
theorem finiteCutoffResidual_eq_zeta_add_tail {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    finiteCutoffResidual N s=(s-1)*riemannZeta s+s*(s-1)*(s+1)*
      (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  have hp : s+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [centeredBernoulliTail_eq_sub_mean (by linarith : -1 < s.re) hN,
    zeta_eq_centredTruncated_of_re_pos hN hs hs1]
  unfold finiteCutoffResidual zetaCentredTruncated
  field_simp
  ring

/-- Powers in a finite Dirichlet head have uniform type `log N`. -/
theorem norm_finiteCutoff_power_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (s : ℂ) :
    ‖(n:ℂ)^(-s)‖ ≤ Real.exp (Real.log N*‖s‖) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0<n), Complex.neg_re,
    Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlnN : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hre : -s.re ≤ ‖s‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm s)
  nlinarith [norm_nonneg s]

/-- A uniform growth bound retains the cutoff in both type and prefactor. -/
theorem norm_finiteCutoffResidual_le {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    ‖finiteCutoffResidual N s‖ ≤ 3*(N:ℝ)*Real.exp ((Real.log N+2)*‖s‖) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ)<N := by linarith
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  let E := Real.exp (Real.log N*‖s‖)
  let U := Real.exp ‖s‖
  have hE : 0 < E := Real.exp_pos _
  have hU : 1 ≤ U := Real.one_le_exp (norm_nonneg s)
  have hu : ‖s‖+1 ≤ U := Real.add_one_le_exp _
  have hp := norm_finiteCutoff_power_le hN (le_refl N) s
  change ‖(N:ℂ)^(-s)‖ ≤ E at hp
  have hsum : ‖∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s)‖ ≤ (N:ℝ)*E := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n:ℂ)^(-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, E := Finset.sum_le_sum (fun n hn =>
        norm_finiteCutoff_power_le (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 s)
      _ = _ := by simp
  have hsp : ‖s-1‖ ≤ U := (norm_sub_le s 1).trans (by simpa using hu)
  have hsU : ‖s‖ ≤ U := by linarith
  have hp1 : ‖(N:ℂ)^(1-s)‖ ≤ (N:ℝ)*E := by
    rw [show (1:ℂ)-s=1+(-s) by ring, Complex.cpow_add _ _ hNc, Complex.cpow_one,
      norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hpm : ‖(N:ℂ)^(-s-1)‖ ≤ E := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hNc, Complex.cpow_neg_one, norm_mul, norm_inv,
      Complex.norm_natCast]
    have hinv : (N:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hN0).mpr hNr
    exact (mul_le_mul hp hinv (by positivity) hE.le).trans_eq (mul_one E)
  have heq : Real.exp ((Real.log N+2)*‖s‖)=E*U*U := by
    dsimp [E,U]
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hb := norm_add_le ((s-1)*(∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s))+
      (N:ℂ)^(1-s)-(s-1)*(N:ℂ)^(-s)/2) (s*(s-1)*(N:ℂ)^(-s-1)/12)
  have ha := norm_sub_le ((s-1)*(∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s))+(N:ℂ)^(1-s))
      ((s-1)*(N:ℂ)^(-s)/2)
  have hc := norm_add_le ((s-1)*(∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s))) ((N:ℂ)^(1-s))
  have ht1 : ‖(s-1)*(∑ n ∈ Finset.Icc 1 N, (n:ℂ)^(-s))‖ ≤ U*((N:ℝ)*E) := by
    rw [norm_mul]; exact mul_le_mul hsp hsum (norm_nonneg _) (by positivity)
  have ht2 : ‖(s-1)*(N:ℂ)^(-s)/2‖ ≤ U*E/2 := by
    rw [norm_div,norm_mul]; norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right (mul_le_mul hsp hp (norm_nonneg _) (by positivity)) (by norm_num)
  have ht3 : ‖s*(s-1)*(N:ℂ)^(-s-1)/12‖ ≤ U*U*E/12 := by
    rw [norm_div,norm_mul,norm_mul]; norm_num only [Complex.norm_ofNat]
    gcongr
  change ‖_+_‖ ≤ _
  rw [heq]
  have hx : U*((N:ℝ)*E)+(N:ℝ)*E+U*E/2+U*U*E/12 ≤ 3*(N:ℝ)*(E*U*U) := by
    have a := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ (N:ℝ)*E*U by positivity)
    have b := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ (N:ℝ)*E by positivity)
    have c := mul_nonneg (sub_nonneg.mpr hNr) (show 0 ≤ E*U*U by positivity)
    have d := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ E*U by positivity)
    nlinarith
  linarith

/-- Actual simple critical zeros reproduced exactly by the finite residual. -/
def finiteCutoffMatchingZeros (N : ℕ) (T : ℝ) : Finset ℂ :=
  (xiSimpleCriticalZeroFinset T).filter (fun s => finiteCutoffResidual N s=0)

/-- Actual simple critical zeros where the retained tail is essential. -/
def finiteCutoffMissedZeros (N : ℕ) (T : ℝ) : Finset ℂ :=
  (xiSimpleCriticalZeroFinset T).filter (fun s => finiteCutoffResidual N s≠0)

/-- Exact matching and nonzero discrepancy partition the actual census. -/
theorem finiteCutoff_count_partition (N : ℕ) (T : ℝ) :
    (finiteCutoffMatchingZeros N T).card+(finiteCutoffMissedZeros N T).card=
      xiSimpleCriticalZeroCount T := by
  classical
  exact Finset.card_filter_add_card_filter_not _

/-- Jensen's explicit budget applies to the literal matching zeros at every cutoff. -/
theorem finiteCutoff_matching_count_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    ((finiteCutoffMatchingZeros N T).card:ℝ) ≤
      (Real.log (3*(N:ℝ))+(Real.log N+2)*(2*T+3))/Real.log 2 := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hF := differentiable_finiteCutoffResidual hN
  have hanchor : finiteCutoffResidual N 1≠0 := by simp
  have hdiv : ((finiteCutoffMatchingZeros N T).card:ℤ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor (finiteCutoffResidual N) (closedBall 1 (T+1))) u := by
    apply card_le_sum_divisor_of_finite_zeros hF hanchor
      (finiteCutoffMatchingZeros N T) (fun s : ℂ => s)
    · intro s hs z hz h; exact h
    · intro s hs
      have hm := mem_xiSimpleCriticalZeroFinset.mp (Finset.mem_filter.mp hs).1
      rw [mem_closedBall_iff_norm]
      have hb := Complex.norm_le_abs_re_add_abs_im (s-1)
      simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero,
        hm.2.2.2.2.2.1, abs_of_pos hm.2.2.1] at hb
      norm_num at hb
      linarith [hm.2.2.2.1]
    · intro s hs; exact (Finset.mem_filter.mp hs).2
  have hdivR : ((finiteCutoffMatchingZeros N T).card:ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor (finiteCutoffResidual N) (closedBall 1 (T+1))) u):ℝ) :=
    by exact_mod_cast hdiv
  have hb := exponentialType_zeroCount_le hF hanchor
    (A := Real.log N+2) (C := 3*(N:ℝ))
    (by linarith [Real.log_nonneg hNr]) (by linarith)
    (norm_finiteCutoffResidual_le hN) (r := T+1) (by linarith)
  simp only [finiteCutoffResidual_one,norm_one,Real.log_one,sub_zero] at hb
  have he : (1:ℝ)+2*(T+1)=2*T+3 := by ring
  rw [he] at hb
  exact hdivR.trans hb

/-- A simpler uniform budget separates the height and cutoff parameters. -/
theorem finiteCutoff_matching_count_le_linear {N : ℕ} (hN : 1 ≤ N)
    {T : ℝ} (hT : 1 ≤ T) :
    ((finiteCutoffMatchingZeros N T).card:ℝ) ≤
      T*(6*Real.log N+12)/Real.log 2 := by
  apply (finiteCutoff_matching_count_le hN hT).trans
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hN0.ne']
  have hl := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  nlinarith [mul_nonneg (sub_nonneg.mpr hT) hl]

/-- The nonzero retained discrepancies have an explicit lower counting bound. -/
theorem finiteCutoff_missed_count_lower {N : ℕ} (hN : 1 ≤ N)
    {T : ℝ} (hT : 1 ≤ T) :
    (xiSimpleCriticalZeroCount T:ℝ)-T*(6*Real.log N+12)/Real.log 2 ≤
      ((finiteCutoffMissedZeros N T).card:ℝ) := by
  have hp : ((finiteCutoffMatchingZeros N T).card:ℝ)+
      ((finiteCutoffMissedZeros N T).card:ℝ)=(xiSimpleCriticalZeroCount T:ℝ) := by
    exact_mod_cast finiteCutoff_count_partition N T
  linarith [finiteCutoff_matching_count_le_linear hN hT]

/-- Exact matching at a height forces a quantitative logarithmic cutoff cost. -/
theorem eventually_finiteCutoff_matching_log_lower :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 1 ≤ N →
      (∀ s ∈ xiSimpleCriticalZeroFinset T, finiteCutoffResidual N s=0) →
      Real.log N ≥ (Real.log 2/(432*Real.pi))*Real.log T-2 := by
  filter_upwards [eventually_superlinear_xiSimpleCriticalZeroCount,
    eventually_ge_atTop (1:ℝ)] with T hcount hT
  intro N hN hmatch
  have he : finiteCutoffMatchingZeros N T=xiSimpleCriticalZeroFinset T := by
    classical
    ext s
    simp only [finiteCutoffMatchingZeros,Finset.mem_filter]
    exact ⟨And.left,fun hs => ⟨hs,hmatch s hs⟩⟩
  have hb := finiteCutoff_matching_count_le_linear hN hT
  rw [he,card_xiSimpleCriticalZeroFinset] at hb
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hbig := (le_div_iff₀ hl2).mp (hcount.trans hb)
  have hT0 : 0<T := by linarith
  have hcost : (1/(72*Real.pi))*Real.log T*Real.log 2 ≤ 6*Real.log N+12 := by
    apply (mul_le_mul_iff_right₀ hT0).mp
    nlinarith [hbig]
  have heq : (1/(72*Real.pi))*Real.log T*Real.log 2=
      6*((Real.log 2/(432*Real.pi))*Real.log T) := by ring
  rw [heq] at hcost
  linarith

/-- Any exact matching schedule eventually needs a positive polynomial cutoff scale. -/
theorem eventually_finiteCutoff_matching_power_lower :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 1 ≤ N →
      (∀ s ∈ xiSimpleCriticalZeroFinset T, finiteCutoffResidual N s=0) →
      T^(Real.log 2/(864*Real.pi)) ≤ (N:ℝ) := by
  have hc : 0<Real.log 2/(864*Real.pi) := by positivity
  filter_upwards [eventually_finiteCutoff_matching_log_lower,
    Real.tendsto_log_atTop.eventually_ge_atTop (2/(Real.log 2/(864*Real.pi))),
    eventually_ge_atTop (1:ℝ)] with T hcost hlarge hT
  intro N hN hmatch
  have ha := (div_le_iff₀ hc).mp hlarge
  have hb := hcost N hN hmatch
  have hlog : Real.log T*(Real.log 2/(864*Real.pi)) ≤ Real.log N := by
    have he : Real.log 2/(432*Real.pi)=2*(Real.log 2/(864*Real.pi)) := by ring
    rw [he] at hb
    nlinarith
  rw [Real.rpow_def_of_pos (by linarith : 0<T)]
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by
    exact_mod_cast (show 0<N by omega)))

/-- At a zeta zero the finite discrepancy is exactly the tail that was omitted. -/
theorem finiteCutoffResidual_at_zero {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) (hz : riemannZeta s=0) :
    finiteCutoffResidual N s=s*(s-1)*(s+1)*
      (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  rw [finiteCutoffResidual_eq_zeta_add_tail hN hs hs1,hz,mul_zero,zero_add]

/-- Beyond the height cutoff, the nonzero discrepancy still has a controlled size. -/
theorem norm_finiteCutoffResidual_at_zero_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) (hz : riemannZeta s=0) (ht : |s.im|≤N) :
    ‖finiteCutoffResidual N s‖ ≤ ‖s*(s-1)*(s+1)‖*((N:ℝ)^(-s.re-2)/15) := by
  rw [finiteCutoffResidual_at_zero hN hs hs1 hz,norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_centeredBernoulliTail_le_linear
      (by exact_mod_cast (show 0<N by omega)) (by linarith : -1<s.re) ht) (norm_nonneg _)

/-- Every fixed cutoff misses a superlinear number of actual simple critical zeros. -/
theorem eventually_finiteCutoff_missed_superlinear {N : ℕ} (hN : 1 ≤ N) :
    ∀ᶠ T : ℝ in atTop, (1/(144*Real.pi))*T*Real.log T ≤
      ((finiteCutoffMissedZeros N T).card:ℝ) := by
  let K := (6*Real.log N+12)/Real.log 2
  let c := (1/(144*Real.pi):ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [eventually_superlinear_xiSimpleCriticalZeroCount,
    Real.tendsto_log_atTop.eventually_ge_atTop (K/c),
    eventually_ge_atTop (1:ℝ)] with T hcount hlog hT
  have hcost : K ≤ c*Real.log T := by
    have := (div_le_iff₀ hc).mp hlog
    nlinarith
  have hb := finiteCutoff_missed_count_lower hN hT
  have he : T*(6*Real.log N+12)/Real.log 2=T*K := by dsimp [K]; ring
  rw [he] at hb
  have hmul := mul_le_mul_of_nonneg_left hcost (show 0≤T by linarith)
  have hec : (1/(72*Real.pi):ℝ)=2*c := by dsimp [c]; ring
  rw [hec] at hcount
  change c*T*Real.log T ≤ _
  nlinarith

/-- A fixed cutoff has nonzero residual at actual simple critical zeros above every height. -/
theorem exists_high_finiteCutoff_missed {N : ℕ} (hN : 1 ≤ N) (H : ℝ) :
    ∃ s : ℂ, H<s.im ∧ s∈xiSimpleCriticalZeroFinset s.im ∧ finiteCutoffResidual N s≠0 := by
  classical
  by_contra! h
  apply not_linear_bound_of_superlinear (c := 1/(144*Real.pi)) (K := 0)
    (m := (xiSimpleCriticalZeroCount H:ℝ)) (by positivity)
    (eventually_finiteCutoff_missed_superlinear hN)
  intro T hT
  have hsub : finiteCutoffMissedZeros N T ⊆ xiSimpleCriticalZeroFinset H := by
    intro s hs
    obtain ⟨hsT,hne⟩ := Finset.mem_filter.mp hs
    obtain ⟨hr0,hr1,hi0,hiT,hzero,hr,ho⟩ := mem_xiSimpleCriticalZeroFinset.mp hsT
    have hself : s∈xiSimpleCriticalZeroFinset s.im :=
      mem_xiSimpleCriticalZeroFinset.mpr ⟨hr0,hr1,hi0,le_refl _,hzero,hr,ho⟩
    have hiH : s.im≤H := by
      by_contra hn
      exact hne (h s (lt_of_not_ge hn) hself)
    exact mem_xiSimpleCriticalZeroFinset.mpr ⟨hr0,hr1,hi0,hiH,hzero,hr,ho⟩
  have hb := Finset.card_le_card hsub
  rw [card_xiSimpleCriticalZeroFinset] at hb
  simp only [zero_mul,zero_add]
  exact_mod_cast hb

/-- The tail that every fixed cutoff omits is nonzero at arbitrarily high actual simple zeros. -/
theorem exists_high_finiteCutoff_nonzero_tail {N : ℕ} (hN : 1 ≤ N) (H : ℝ) :
    ∃ s : ℂ, H<s.im ∧ 0<s.im ∧ s.re=1/2 ∧ riemannZeta s=0 ∧
      (analyticOrderAt xi s).toNat=1 ∧ finiteCutoffResidual N s≠0 ∧
      (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2))≠0 := by
  obtain ⟨s,hH,hs,hne⟩ := exists_high_finiteCutoff_missed hN H
  obtain ⟨hr0,hr1,hi0,-,hxi,hr,ho⟩ := mem_xiSimpleCriticalZeroFinset.mp hs
  have hz := (xi_zero_iff_zeta_zero_of_mem_strip hr0 hr1).mp hxi
  refine ⟨s,hH,hi0,hr,hz,ho,hne,?_⟩
  intro ht
  have hs1 : s≠1 := by intro h; rw [h] at hr1; norm_num at hr1
  have he := finiteCutoffResidual_at_zero hN hr0 hs1 hz
  rw [ht,mul_zero] at he
  exact hne he

/-- The finite exponential polynomial is exactly the source cut at `N`, after pole clearing. -/
theorem finiteCutoffResidual_eq_boundary_sub_head {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) :
    finiteCutoffResidual N s=(s+2)*(s+3)/12-s*(s-1)*(s+1)*
      (∫ x in (1:ℝ)..(N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  have hiB := integrableOn_bernoulli_cpow (by linarith : -1<s.re) (show 1≤1 by omega)
  simp only [Nat.cast_one,show -s-1-1=-s-2 by ring] at hiB
  have hiC := (integrableOn_Ioi_cpow_of_lt (by
    norm_num
    linarith : (-s-2).re < -1) (by norm_num : (0:ℝ)<1)).const_mul (1/12:ℂ)
  have hi : IntegrableOn
      (fun x : ℝ => ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) (Ioi 1) := by
    have he : (fun x : ℝ => ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2))=
        (fun x : ℝ => (bernoulliPeriodic x:ℂ)*(x:ℂ)^(-s-2)+(1/12:ℂ)*(x:ℂ)^(-s-2)) := by
      funext x
      push_cast
      ring
    rw [he]
    exact hiB.add hiC
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hi
    (show (1:ℝ)≤N by exact_mod_cast hN)
  have hunit := finiteCutoffResidual_eq_zeta_add_tail (show 1≤1 by omega) hs hs1
  have hNid := finiteCutoffResidual_eq_zeta_add_tail hN hs hs1
  have hpoly : finiteCutoffResidual 1 s=(s+2)*(s+3)/12 := by
    simp [finiteCutoffResidual]
    ring
  rw [hpoly] at hunit
  norm_num only [Nat.cast_one] at hunit
  rw [←hsplit]
  linear_combination hNid-hunit

end RHTower.DeletionMixedRefinement
