import GaloisForLFunctions.RHTower.ChiRamanujanMovingLabelRows
import GaloisForLFunctions.RHTower.ChiRamanujanOscillatoryLogWindow
import GaloisForLFunctions.RHTower.ChiRamanujanMixedProfileCancellation
/-!
# Actual mixed-frequency label rows and collisions

One Mellin variable approaches the pole at logarithmic scale while the other
retains a fixed nonzero real frequency. The original rational label rows have
limits `1-E(u), 1, 1-E(u), 1-E(u)` after division by `log N`. Every exact
pair/triple collision is negligible even at one logarithmic scale. Their
complete masked assembly therefore tends to `(1-E(u))^2` at the cubic scale.

The proof retains each prime phase as a unit-circle parameter. Compact
continuity controls the whole large-prime tail; the exact fixed-prime
limiting denominator is nonzero. The corpus oscillatory prime windows remove
all remaining phase terms. No response bound or convergence premise is added.
The full mixed cofactor assembly and uniform physical cancellation remain
separate obligations.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RHTower.BAGTrace

private theorem response_uniform_tail (R : ℝ × (ℝ × ℂ) → ℂ)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q : ℂ, ‖q‖ = 1 → ContinuousAt R (0,(t,q)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q : ℂ, ‖q‖ = 1 →
      ‖R ((n : ℝ)⁻¹,(t,q))-R (0,(t,q))‖ < ε := by
  have he : ∀ᶠ z : ℝ in 𝓝 0, ∀ tq ∈ (Set.Icc (0 : ℝ) 1) ×ˢ (Metric.sphere (0 : ℂ) 1),
      ‖R (z,tq)-R (0,tq)‖ < ε := by
    apply (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) 1)).eventually_forall_of_forall_eventually
    intro tq htq
    have hq : ‖tq.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using htq.2
    have hmap : ContinuousAt (fun zt : ℝ × (ℝ × ℂ) => ((0 : ℝ),zt.2)) (0,tq) :=
      continuousAt_const.prodMk continuousAt_snd
    have hc := (h0 tq.1 htq.1 tq.2 hq).tendsto.comp hmap.tendsto
    have he := ((h0 tq.1 htq.1 tq.2 hq).tendsto.sub hc).norm
    have hl : Tendsto (fun zt : ℝ × (ℝ × ℂ) => ‖R zt-R (0,zt.2)‖) (𝓝 (0,tq)) (𝓝 0) := by
      simpa only [Function.comp_def,sub_self,norm_zero] using he
    exact hl.eventually (gt_mem_nhds hε)
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hn.eventually he)
  refine ⟨K,fun n hn t ht q hq => hK n hn (t,q) ?_⟩
  exact ⟨ht,by simpa only [Metric.mem_sphere,dist_zero_right] using hq⟩

private theorem prime_mass_ratio :
    Tendsto (fun N : ℕ => mertensPrimeWeightSum N/Real.log N) atTop (𝓝 1) := by
  have h := tendsto_mertensPrimeWindow_div_log
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1))
  simpa [mertensPrimeWindow,mertensPrimeWeightSum] using h

private def responseWindowError (R : ℝ × (ℝ × ℂ) → ℂ) (phase : ℕ → ℂ) (N n : ℕ) : ℂ :=
  (R ((n : ℝ)⁻¹,(Real.log n/Real.log N,phase n))-R (0,(Real.log n/Real.log N,phase n)))*
    (mertensPrimeWeight n : ℂ)

private theorem response_head_zero (R : ℝ × (ℝ × ℂ) → ℂ) (phase : ℕ → ℂ)
    (h0 : ∀ n : ℕ, n.Prime → ContinuousAt R (0,(0,phase n)))
    (hh : ∀ n : ℕ, n.Prime → ContinuousAt R ((n : ℝ)⁻¹,(0,phase n))) (K : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/
      (Real.log N : ℂ)) atTop (𝓝 0) := by
  have ht (n : ℕ) : Tendsto (fun N : ℕ => responseWindowError R phase N n/(Real.log N : ℂ))
      atTop (𝓝 0) := by
    by_cases hp : n.Prime
    · have hd := tendsto_drift_zero (Real.log n)
      have ha := (hh n hp).tendsto.comp (tendsto_const_nhds.prodMk_nhds (hd.prodMk_nhds tendsto_const_nhds))
      have hb := (h0 n hp).tendsto.comp (tendsto_const_nhds.prodMk_nhds (hd.prodMk_nhds tendsto_const_nhds))
      have h := (((ha.sub hb).mul_const (mertensPrimeWeight n : ℂ)).mul criticalLogScaleInv_tendsto_zero)
      simpa only [Function.comp_def,mul_zero,responseWindowError,div_eq_mul_inv] using h
    · simp only [responseWindowError,mertensPrimeWeight,if_neg hp,
        Complex.ofReal_zero,mul_zero,zero_div]
      exact tendsto_const_nhds
  have h := tendsto_finsetSum (Finset.Icc 0 K) (fun n _ => ht n)
  simpa only [Finset.sum_div,Finset.sum_const_zero] using h

private theorem response_error_zero (R : ℝ × (ℝ × ℂ) → ℂ) (phase : ℕ → ℂ)
    (hp : ∀ n : ℕ, n.Prime → ‖phase n‖ = 1)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q : ℂ, ‖q‖ = 1 → ContinuousAt R (0,(t,q)))
    (hh : ∀ n : ℕ, n.Prime → ContinuousAt R ((n : ℝ)⁻¹,(0,phase n))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,responseWindowError R phase N n)/
      (Real.log N : ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK⟩ := response_uniform_tail R h0 (show 0 < ε/4 by positivity)
  have hhlim := response_head_zero R phase (fun n hn => h0 0 (by simp) (phase n) (hp n hn)) hh K
  have he : ∀ᶠ N : ℕ in atTop,
      ‖(∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/(Real.log N : ℂ)‖ < ε/2 := by
    have h := hhlim.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using half_pos hε))
    exact h
  have hm := prime_mass_ratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ)<2))
  obtain ⟨M,hM⟩ := eventually_atTop.mp (he.and (hm.and (eventually_ge_atTop (max K 2))))
  refine ⟨M,fun N hMN => ?_⟩
  obtain ⟨hhead,hmass,hN⟩ := hM N hMN
  have hNK : K ≤ N := (le_max_left K 2).trans hN
  have hN2 : 2 ≤ N := (le_max_right K 2).trans hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos
    (by exact_mod_cast (show 1 < N by omega))
  have heqhead : (∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n) =
      ∑ n ∈ Finset.Icc 0 N, if n ≤ K then responseWindowError R phase N n else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.zero_le,true_and]
    omega
  have hdiff : (∑ n ∈ Finset.Icc 0 N,responseWindowError R phase N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/(Real.log N : ℂ) =
      (∑ n ∈ Finset.Icc 0 N,if n ≤ K then 0 else responseWindowError R phase N n)/(Real.log N : ℂ) := by
    rw [← sub_div,heqhead,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ≤ K <;> simp [hn]
  have hbd : ‖∑ n ∈ Finset.Icc 0 N,if n ≤ K then 0 else responseWindowError R phase N n‖ ≤
      (ε/4)*mertensPrimeWeightSum N := by
    calc _ ≤ ∑ n ∈ Finset.Icc 0 N, ‖if n ≤ K then 0 else responseWindowError R phase N n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 0 N, (ε/4)*mertensPrimeWeight n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hnK : n ≤ K
        · simp only [if_pos hnK,norm_zero]
          exact mul_nonneg (by positivity) (mertensPrimeWeight_nonneg n)
        · by_cases hprime : n.Prime
          · have he := (hK n (by omega) _ (logRatio_mem_Icc hprime (Finset.mem_Icc.mp hn).2) (phase n) (hp n hprime)).le
            simp only [if_neg hnK,responseWindowError,norm_mul,Complex.norm_real,
              Real.norm_eq_abs,abs_of_nonneg (mertensPrimeWeight_nonneg n)]
            exact mul_le_mul_of_nonneg_right he (mertensPrimeWeight_nonneg n)
          · simp [responseWindowError,mertensPrimeWeight,hprime]
      _ = _ := by rw [mertensPrimeWeightSum,Finset.mul_sum]
  have hsmall : ‖(∑ n ∈ Finset.Icc 0 N,responseWindowError R phase N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/(Real.log N : ℂ)‖ ≤ ε/2 := by
    rw [hdiff,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
    apply (div_le_iff₀ hlog).mpr
    have hm' := (div_lt_iff₀ hlog).mp hmass
    have hb := mul_le_mul_of_nonneg_left hm'.le (show 0 ≤ ε/4 by positivity)
    linarith
  rw [dist_zero_right]
  have htri := norm_add_le
    ((∑ n ∈ Finset.Icc 0 N,responseWindowError R phase N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/(Real.log N : ℂ))
    ((∑ n ∈ Finset.Icc 0 K,responseWindowError R phase N n)/(Real.log N : ℂ))
  rw [sub_add_cancel] at htri
  linarith


private def responseF (a b : ℂ) : ℂ := (a+b-a^2-b^2)/(a*b)
private def responseG (a b : ℂ) : ℂ := a+b-1-b/a-a/b+b^2/a+a^2/b
private def responseBase (z a b : ℂ) : ℂ :=
  1+(z*responseF a b+z^2*(a+b-2))/(1-z)^2
private def responseFirstNumerator (z a b : ℂ) : ℂ :=
  ((a+b-1)+z*((a+b)*responseF a b-a*b-1)+
    z^2*(a*b-a-b+a^2+b^2))/(a*(1-z)^2)
private def responseThirdNumerator (z a b : ℂ) : ℂ :=
  (a*b-a-b+z*(2*(a+b)-a*b-1)-z^2*a*b)/(a*b*(1-z)^3)
private def responsePairNumerator (z a b : ℂ) : ℂ :=
  (a^2+b^2+a*b-a-b+z*(a*b*(2-responseF a b-a-b)-(a+b)*responseG a b)+
    z^2*a*b*responseG a b)/(a*b*(1-z)^2)
private def responseNumerator (k : Fin 4) (z a b : ℂ) : ℂ :=
  if k=0 then responseFirstNumerator z a b else
  if k=1 then responseFirstNumerator z b a else
  if k=2 then responseThirdNumerator z a b else responsePairNumerator z a b
private def responseRational (k : Fin 4) (z a b : ℂ) : ℂ :=
  responseNumerator k z a b/responseBase z a b

private theorem responseBase_zero (a b : ℂ) : responseBase 0 a b = 1 := by
  simp [responseBase]

private theorem continuousAt_responseBase {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseBase w.1 w.2.1 w.2.2) (z,a,b) := by
  unfold responseBase responseF
  fun_prop (disch := simp [hz,ha,hb])

private theorem continuousAt_responseNumerator (k : Fin 4) {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseNumerator k w.1 w.2.1 w.2.2) (z,a,b) := by
  fin_cases k <;>
    simp [responseNumerator,responseFirstNumerator,responseThirdNumerator,
      responsePairNumerator,responseF,responseG] <;>
    fun_prop (disch := simp [hz,ha,hb])

private theorem continuousAt_responseRational (k : Fin 4) {z a b : ℂ}
    (hz : 1-z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hH : responseBase z a b ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ × ℂ => responseRational k w.1 w.2.1 w.2.2) (z,a,b) :=
  (continuousAt_responseNumerator k hz ha hb).div (continuousAt_responseBase hz ha hb) hH


private def responseLocalNumerator (k : Fin 4) (z x y : ℂ) : ℂ :=
  if k=0 then x⁻¹*weightedConeEulerMinusOne z x y else
  if k=1 then y⁻¹*weightedConeEulerMinusOne z x y else
  if k=2 then weightedConeEuler z x y 1 else x⁻¹*y⁻¹*weightedConeEulerMinusTwo z x y

private theorem minusOne_swap (z x y : ℂ) (hz : 1-z ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hx1 : 1-x ≠ 0) (hy1 : 1-y ≠ 0) :
    weightedConeEulerMinusOne z x y = weightedConeEulerMinusOne z y x := by
  unfold weightedConeEulerMinusOne weightedEuler
  field_simp
  ring

private theorem responseBase_eq (z a b : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseBase z a b = (1-z*a)*(1-z*b)*weightedEuler z (z*a) (z*b) := by
  have h := weightedEuler_normalized_deformation z a b hz ha hb h1 hx hy
  rw [h]
  unfold responseBase responseF
  ring

private theorem responseNumerator_eq (k : Fin 4) (z a b : ℂ)
    (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseNumerator k z a b = (1-z*a)*(1-z*b)*responseLocalNumerator k z (z*a) (z*b) := by
  fin_cases k
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedFirst_normalized_deformation z a b hz ha hb h1 hx hy
    unfold responseFirstNumerator responseF
    convert h.symm using 1 <;> ring
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedFirst_normalized_deformation z b a hz hb ha h1 hy hx
    rw [minusOne_swap z (z*b) (z*a) h1 (mul_ne_zero hz hb) (mul_ne_zero hz ha) hy hx] at h
    unfold responseFirstNumerator responseF
    convert h.symm using 1 <;> ring
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedThird_normalized_deformation z a b hz ha hb h1 hx hy
    exact h.symm
  · simp [responseNumerator,responseLocalNumerator]
    have h := weightedPair_normalized_deformation z a b hz ha hb h1 hx hy
    dsimp only at h
    unfold responsePairNumerator responseF responseG
    convert h.symm using 1
    ring

private theorem responseRational_eq (k : Fin 4) (z a b : ℂ)
    (hz : z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*a ≠ 0) (hy : 1-z*b ≠ 0) :
    responseRational k z a b =
      responseLocalNumerator k z (z*a) (z*b)/weightedEuler z (z*a) (z*b) := by
  rw [responseRational,responseNumerator_eq k z a b hz ha hb h1 hx hy,
    responseBase_eq z a b hz ha hb h1 hx hy]
  exact mul_div_mul_left _ _ (mul_ne_zero hx hy)


private theorem responseActual_local (k : Fin 4) (p : Nat.Primes) (s t : ℂ) :
    criticalMellinResponse k p s t =
      responseLocalNumerator k (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t)/
        weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p s) (cubicPrimeBase p t) := by
  fin_cases k <;> simp [criticalMellinResponse,responseLocalNumerator,
    criticalFirstMellinResponse,criticalSecondMellinResponse,criticalThirdMellinResponse,
    criticalPairMellinResponse,criticalLocalMellinBase]

private theorem moving_base_eq (p : Nat.Primes) (u : ℂ) (L : ℝ) :
    cubicPrimeBase p (1+u/(L : ℂ)) =
      (((p : ℝ)⁻¹ : ℝ) : ℂ)*Complex.exp (-u*((Real.log (p : ℝ)/L : ℝ) : ℂ)) := by
  have h := criticalPrimeMellinRatio_logScale p u L
  rw [criticalPrimeMellinRatio] at h
  have he := (div_eq_iff (cubicPrimeBase_ne_zero p 1)).mp h
  simpa [cubicPrimeBase,Complex.cpow_neg_one,mul_comm] using he

private theorem base_complement_nonzero (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1-cubicPrimeBase p s ≠ 0 := by
  have h : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  intro he
  rw [← sub_eq_zero.mp he,norm_one] at h
  exact (lt_irrefl _ h)


private def primePhase (tau : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-(tau : ℂ)*Complex.I*(Real.log n : ℂ))

private theorem primePhase_norm (tau : ℝ) (n : ℕ) : ‖primePhase tau n‖ = 1 := by
  rw [primePhase,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,neg_zero,Real.exp_zero]

private def mixedResponseProfile (k : Fin 4) (u v : ℂ) (zx : ℝ × (ℝ × ℂ)) : ℂ :=
  responseRational k zx.1 (Complex.exp (-u*(zx.2.1 : ℂ)))
    (zx.2.2*Complex.exp (-v*(zx.2.1 : ℂ)))

private theorem phase_ne_zero {q : ℂ} (hq : ‖q‖ = 1) : q ≠ 0 := by
  intro h
  rw [h,norm_zero] at hq
  exact zero_ne_one hq

private theorem mixedProfile_continuousAt (k : Fin 4) (u v : ℂ) {z x : ℝ} {q : ℂ}
    (hz : 1-(z : ℂ) ≠ 0) (hq : q ≠ 0)
    (hH : responseBase z (Complex.exp (-u*(x : ℂ))) (q*Complex.exp (-v*(x : ℂ))) ≠ 0) :
    ContinuousAt (mixedResponseProfile k u v) (z,(x,q)) := by
  have hm : ContinuousAt (fun zx : ℝ × (ℝ × ℂ) => ((zx.1 : ℂ),
      Complex.exp (-u*(zx.2.1 : ℂ)),zx.2.2*Complex.exp (-v*(zx.2.1 : ℂ)))) (z,(x,q)) := by fun_prop
  have h := (continuousAt_responseRational k hz (Complex.exp_ne_zero _)
    (mul_ne_zero hq (Complex.exp_ne_zero _)) hH).tendsto.comp hm.tendsto
  exact h

private theorem mixedProfile_slice (k : Fin 4) (u v : ℂ) (x : ℝ) {q : ℂ} (hq : ‖q‖ = 1) :
    ContinuousAt (mixedResponseProfile k u v) (0,(x,q)) := by
  apply mixedProfile_continuousAt
  · norm_num
  · exact phase_ne_zero hq
  · simp [responseBase_zero]

private theorem responseBase_one_left (z q : ℂ) (hz : 1-z ≠ 0) (hq : q ≠ 0) :
    responseBase z 1 q=(1-z*q)/(1-z) := by
  unfold responseBase responseF
  field_simp
  ring

private theorem mixedProfile_head (k : Fin 4) (u v : ℂ) (tau : ℝ) (n : ℕ) (hn : n.Prime) :
    ContinuousAt (mixedResponseProfile k u v) ((n : ℝ)⁻¹,(0,primePhase tau n)) := by
  have hi : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hn.one_lt)
  have hz : 1-(((n : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hi).ne'
  have hq := phase_ne_zero (primePhase_norm tau n)
  apply mixedProfile_continuousAt k u v hz hq
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  rw [responseBase_one_left _ _ hz hq]
  apply div_ne_zero _ hz
  have hnorm : ‖(((n : ℝ)⁻¹ : ℝ) : ℂ)*primePhase tau n‖ < 1 := by
    rw [norm_mul,primePhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    exact hi
  intro h
  rw [← sub_eq_zero.mp h,norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

private theorem phase_eq_base (tau : ℝ) (p : Nat.Primes) :
    primePhase tau p = cubicPrimeBase p ((tau : ℂ)*Complex.I) := by
  rw [primePhase,cubicPrimeBase,Complex.cpow_def_of_ne_zero
    (by exact_mod_cast p.property.ne_zero)]
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  rw [show (p : ℂ)=((p : ℝ) : ℂ) by simp,← Complex.ofReal_log hp.le]
  congr 1
  ring

private theorem mixed_base_eq (p : Nat.Primes) (v : ℂ) (tau : ℝ) (L : ℝ) :
    cubicPrimeBase p (1+v/(L : ℂ)+(tau : ℂ)*Complex.I)=
      (((p : ℝ)⁻¹ : ℝ) : ℂ)*(primePhase tau p*Complex.exp (-v*((Real.log (p : ℝ)/L : ℝ) : ℂ))) := by
  rw [← cubicPrimeBase_mul,moving_base_eq,phase_eq_base]
  ring

private theorem mixedActual_eq_profile (k : Fin 4) (p : Nat.Primes) (u v : ℂ) (tau : ℝ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMellinResponse k p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)=
      mixedResponseProfile k u v ((p : ℝ)⁻¹,(Real.log (p : ℝ)/Real.log N,primePhase tau p)) := by
  have hbase : cubicPrimeBase p 1 = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp [cubicPrimeBase,Complex.cpow_neg_one]
  have hz : (((p : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (by exact_mod_cast p.property.ne_zero))
  have h1 : 1-(((p : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have hi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast p.property.one_lt)
    exact_mod_cast (sub_pos.mpr hi).ne'
  have hx := base_complement_nonzero p hu
  have hv' : 0 < (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I).re := by simpa using hv
  have hy := base_complement_nonzero p hv'
  rw [moving_base_eq] at hx
  rw [mixed_base_eq] at hy
  rw [responseActual_local,hbase,moving_base_eq,mixed_base_eq]
  exact (responseRational_eq k (((p : ℝ)⁻¹ : ℝ) : ℂ)
    (Complex.exp (-u*((Real.log (p : ℝ)/Real.log N : ℝ) : ℂ)))
    (primePhase tau p*Complex.exp (-v*((Real.log (p : ℝ)/Real.log N : ℝ) : ℂ)))
    hz (Complex.exp_ne_zero _) (mul_ne_zero (phase_ne_zero (primePhase_norm tau p))
      (Complex.exp_ne_zero _)) h1 hx hy).symm

private def mixedLeading (k : Fin 4) (u v q : ℂ) (t : ℝ) : ℂ :=
  if k=0 then 1+q*Complex.exp ((u-v)*(t : ℂ))-Complex.exp (u*(t : ℂ)) else
  if k=1 then 1+q⁻¹*Complex.exp ((v-u)*(t : ℂ))-q⁻¹*Complex.exp (v*(t : ℂ)) else
  if k=2 then 1-Complex.exp (u*(t : ℂ))-q⁻¹*Complex.exp (v*(t : ℂ)) else
    1+q*Complex.exp ((u-v)*(t : ℂ))+q⁻¹*Complex.exp ((v-u)*(t : ℂ))-
      Complex.exp (u*(t : ℂ))-q⁻¹*Complex.exp (v*(t : ℂ))

private theorem mixedProfile_zero (k : Fin 4) (u v : ℂ) (t : ℝ) {q : ℂ} (hq : q ≠ 0) :
    mixedResponseProfile k u v (0,(t,q))=mixedLeading k u v q t := by
  have hu : Complex.exp (u*(t : ℂ)) = (Complex.exp (-u*(t : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  have hv : Complex.exp (v*(t : ℂ)) = (Complex.exp (-v*(t : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  have huv : Complex.exp ((u-v)*(t : ℂ)) =
      Complex.exp (-v*(t : ℂ))/Complex.exp (-u*(t : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  have hvu : Complex.exp ((v-u)*(t : ℂ)) =
      Complex.exp (-u*(t : ℂ))/Complex.exp (-v*(t : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  simp only [mixedResponseProfile,responseRational,Complex.ofReal_zero,responseBase_zero,div_one,
    mixedLeading,hu,hv,huv,hvu]
  have ha := Complex.exp_ne_zero (-u*(t : ℂ))
  have hb := Complex.exp_ne_zero (-v*(t : ℂ))
  fin_cases k <;>
    simp [responseNumerator,responseFirstNumerator,responseThirdNumerator,responsePairNumerator] <;>
    field_simp <;> ring

private theorem phase_inv (tau : ℝ) (n : ℕ) : (primePhase tau n)⁻¹=primePhase (-tau) n := by
  rw [primePhase,← Complex.exp_neg,primePhase]
  push_cast
  congr 1
  ring

private theorem phase_div (tau : ℝ) (n : ℕ) (hn : n.Prime) :
    primePhase tau n/(n : ℂ)=criticalPrimeBoundaryCoeff tau n := by
  have hp := phase_eq_base tau ⟨n,hn⟩
  change primePhase tau n = (n : ℂ)^(-((tau : ℂ)*Complex.I)) at hp
  rw [hp,criticalPrimeBoundaryCoeff,div_eq_mul_inv,← Complex.cpow_neg_one,
    ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne_zero)]
  congr 1
  ring

private theorem oscillatory_weighted_sum (tau : ℝ) (w : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N,primePhase tau n*Complex.exp (w*((Real.log n/Real.log N : ℝ) : ℂ))*
      (mertensPrimeWeight n : ℂ))/(Real.log N : ℂ)=
    criticalOscillatoryLogWindow tau (fun t => (t : ℂ)*Complex.exp (w*(t : ℂ))) N := by
  rw [criticalOscillatoryLogWindow,Finset.sum_div,
    show Nat.primesLE N=(Finset.Icc 0 N).filter Nat.Prime by
      ext n; simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE],Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · rw [if_pos hn,mertensPrimeWeight,if_pos hn,← phase_div tau n hn]
    push_cast
    ring
  · simp [hn,mertensPrimeWeight]

private theorem oscillatory_weighted_limit (tau : ℝˣ) (w : ℂ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      primePhase tau n*Complex.exp (w*((Real.log n/Real.log N : ℝ) : ℂ))*
        (mertensPrimeWeight n : ℂ))/(Real.log N : ℂ)) atTop (𝓝 0) := by
  obtain ⟨A,hA⟩ := criticalOscillatoryLogWindow_tendsto tau
  simpa only [oscillatory_weighted_sum] using (hA w).2

private theorem leading_window_limit (k : Fin 4) (u v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      mixedLeading k u v (primePhase tau n) (Real.log n/Real.log N)*
        (mertensPrimeWeight n : ℂ))/(Real.log N : ℂ)) atTop
      (𝓝 (if k=1 then 1 else 1-criticalExponentialMean u)) := by
  have hc := criticalComplexPrimeWindow_tendsto
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Set.Icc 0 1))
  have he := criticalComplexPrimeWindow_tendsto
    (show ContinuousOn (fun t : ℝ => Complex.exp (u*(t : ℂ))) (Set.Icc 0 1) from by fun_prop)
  rw [← criticalExponentialMean_eq_integral] at he
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hc
  have hp := oscillatory_weighted_limit tau (u-v)
  have hm := oscillatory_weighted_limit (-tau) (v-u)
  have hv := oscillatory_weighted_limit (-tau) v
  fin_cases k
  · simpa [mixedLeading,add_mul,sub_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,add_div,sub_div] using (hc.add hp).sub he
  · simpa [mixedLeading,phase_inv,add_mul,sub_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,add_div,sub_div] using (hc.add hm).sub hv
  · simpa [mixedLeading,phase_inv,add_mul,sub_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,add_div,sub_div] using (hc.sub he).sub hv
  · simpa [mixedLeading,phase_inv,add_mul,sub_mul,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,add_div,sub_div] using (((hc.add hp).add hm).sub he).sub hv

private theorem profile_window_limit (k : Fin 4) (u v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      mixedResponseProfile k u v ((n : ℝ)⁻¹,(Real.log n/Real.log N,primePhase tau n))*
        (mertensPrimeWeight n : ℂ))/(Real.log N : ℂ)) atTop
      (𝓝 (if k=1 then 1 else 1-criticalExponentialMean u)) := by
  have herr := response_error_zero (mixedResponseProfile k u v) (primePhase tau)
    (fun n _ => primePhase_norm tau n) (fun t _ q hq => mixedProfile_slice k u v t hq)
    (mixedProfile_head k u v tau)
  have h := (leading_window_limit k u v tau).add herr
  simp only [add_zero] at h
  apply h.congr
  intro N
  rw [← add_div,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [responseWindowError,mixedProfile_zero k u v _ (phase_ne_zero (primePhase_norm tau n))]
  ring

private theorem response_moving_positive (u : ℂ) :
    ∀ᶠ N : ℕ in atTop, 0 < (1+u/(Real.log N : ℂ)).re := by
  have hd : Tendsto (fun N : ℕ => u/(Real.log N : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using criticalLogScaleInv_tendsto_zero.const_mul u
  have h := (Complex.continuous_re.tendsto _).comp
    ((tendsto_const_nhds (x := (1 : ℂ))).add hd)
  exact h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < (1+(0 : ℂ)).re))

private theorem prime_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ p : Sieve.primeSubtypeLE N,f p.val.val) = ∑ n ∈ Nat.primesLE N,f n := by
  calc (∑ p : Sieve.primeSubtypeLE N,f p.val.val) =
      ∑ p ∈ Sieve.primeSubtypeLE N,f p.val :=
        Finset.sum_coe_sort (Sieve.primeSubtypeLE N) (fun p : Nat.Primes => f p.val)
    _ = _ := Finset.sum_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)

private theorem prime_weighted_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ p : Sieve.primeSubtypeLE N,(criticalPrimeLabelWeight p : ℂ)*f p.val.val)=
      ∑ n ∈ Finset.Icc 0 N,f n*(mertensPrimeWeight n : ℂ) := by
  calc _ = ∑ p : Sieve.primeSubtypeLE N,f p.val.val*
        ((Real.log (p.val.val : ℝ)/(p.val.val : ℝ) : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro p _
          simp only [criticalPrimeLabelWeight]
          ring
    _ = ∑ n ∈ Nat.primesLE N,f n*((Real.log n/(n : ℝ) : ℝ) : ℂ) := prime_sum N (fun n : ℕ => f n*((Real.log n/(n : ℝ) : ℝ) : ℂ))
    _ = _ := by
      rw [show Nat.primesLE N=(Finset.Icc 0 N).filter Nat.Prime by
        ext n; simp [Finset.mem_filter,Finset.mem_Icc,Nat.mem_primesLE],Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n.Prime <;> simp [hn,mertensPrimeWeight]

/-- The original distinguished-label row with one near-pole and one off-pole Mellin variable. -/
def criticalMixedMellinResponseRow (k : Fin 4) (u v : ℂ) (tau : ℝ) (N : ℕ) : ℂ :=
  ∑ p : Sieve.primeSubtypeLE N,(criticalPrimeLabelWeight p : ℂ)*
    criticalMellinResponse k p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)

private theorem mixed_row_eq_window (k : Fin 4) (u v : ℂ) (tau : ℝ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMixedMellinResponseRow k u v tau N =
      ∑ n ∈ Finset.Icc 0 N,mixedResponseProfile k u v
        ((n : ℝ)⁻¹,(Real.log n/Real.log N,primePhase tau n))*(mertensPrimeWeight n : ℂ) := by
  unfold criticalMixedMellinResponseRow
  simp_rw [mixedActual_eq_profile k _ u v tau N hu hv]
  exact prime_weighted_sum N (fun n : ℕ => mixedResponseProfile k u v
    ((n : ℝ)⁻¹,(Real.log n/Real.log N,primePhase tau n)))

/-- Every actual mixed-frequency label row has its full growing prime-cutoff limit.
Only the second row retains one; the other three retain `1 - E(u)`. -/
theorem criticalMixedMellinResponseRow_tendsto (k : Fin 4) (u v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => criticalMixedMellinResponseRow k u v tau N/(Real.log N : ℂ))
      atTop (𝓝 (if k=1 then 1 else 1-criticalExponentialMean u)) := by
  apply (profile_window_limit k u v tau).congr'
  filter_upwards [response_moving_positive u,response_moving_positive v] with N hu hv
  exact (congrArg (fun z : ℂ => z/(Real.log N : ℂ)) (mixed_row_eq_window k u v tau N hu hv)).symm

private def collisionWeight (z : ℝ) : ℂ := ((-(z*Real.log z) : ℝ) : ℂ)

private theorem collisionWeight_continuous : Continuous collisionWeight :=
  Complex.continuous_ofReal.comp Real.continuous_mul_log.neg

private theorem collisionWeight_zero : collisionWeight 0 = 0 := by simp [collisionWeight]

private theorem collisionWeight_prime (p : Nat.Primes) :
    collisionWeight ((p : ℝ)⁻¹) = (criticalPrimeLabelWeight p : ℂ) := by
  unfold collisionWeight criticalPrimeLabelWeight
  rw [Real.log_inv]
  congr 1
  ring

private def collisionProfile (k : Fin 4) (u v : ℂ) (zt : ℝ × (ℝ × ℂ)) : ℂ :=
  let w := collisionWeight zt.1
  let a := mixedResponseProfile 0 u v zt
  let b := mixedResponseProfile 1 u v zt
  let c := mixedResponseProfile 2 u v zt
  let d := mixedResponseProfile 3 u v zt
  if k=0 then w*(d-a*b) else
  if k=1 then w*b*c else
  if k=2 then w*a*c else w^2*c*(2*a*b-d)

private theorem collisionProfile_continuousAt (k : Fin 4) (u v : ℂ) {zt : ℝ × (ℝ × ℂ)}
    (hR : ∀ j : Fin 4, ContinuousAt (mixedResponseProfile j u v) zt) :
    ContinuousAt (collisionProfile k u v) zt := by
  have hw : ContinuousAt (fun zt : ℝ × (ℝ × ℂ) => collisionWeight zt.1) zt :=
    collisionWeight_continuous.continuousAt.comp continuousAt_fst
  fin_cases k
  · exact hw.mul ((hR 3).sub ((hR 0).mul (hR 1)))
  · exact (hw.mul (hR 1)).mul (hR 2)
  · exact (hw.mul (hR 0)).mul (hR 2)
  · exact ((hw.pow 2).mul (hR 2)).mul
      (((continuousAt_const.mul (hR 0)).mul (hR 1)).sub (hR 3))

private theorem collisionProfile_zero (k : Fin 4) (u v : ℂ) (t : ℝ) (q : ℂ) :
    collisionProfile k u v (0,(t,q)) = 0 := by
  fin_cases k <;> simp [collisionProfile,collisionWeight_zero]

/-- Every exact pair and triple collision in the original mixed-frequency response expansion. -/
def criticalMixedMellinCollisionMoment (k : Fin 4) (u v : ℂ) (tau : ℝ) (N : ℕ) : ℂ :=
  ∑ p : Sieve.primeSubtypeLE N,
    let w : ℂ := criticalPrimeLabelWeight p
    let a := criticalMellinResponse 0 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
    let b := criticalMellinResponse 1 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
    let c := criticalMellinResponse 2 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
    let d := criticalMellinResponse 3 p (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)
    if k=0 then w^2*(d-a*b) else
    if k=1 then w^2*b*c else
    if k=2 then w^2*a*c else w^3*c*(2*a*b-d)

private theorem collision_window_zero (k : Fin 4) (u v : ℂ) (tau : ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      collisionProfile k u v ((n : ℝ)⁻¹,(Real.log n/Real.log N,primePhase tau n))*
        (mertensPrimeWeight n : ℂ))/(Real.log N : ℂ)) atTop (𝓝 0) := by
  have h := response_error_zero (collisionProfile k u v) (primePhase tau)
    (fun n _ => primePhase_norm tau n)
    (fun t _ q hq => collisionProfile_continuousAt k u v (fun j => mixedProfile_slice j u v t hq))
    (fun n hn => collisionProfile_continuousAt k u v (fun j => mixedProfile_head j u v tau n hn))
  simpa only [responseWindowError,collisionProfile_zero,sub_zero] using h

private theorem mixed_collision_eq_window (k : Fin 4) (u v : ℂ) (tau : ℝ) (N : ℕ)
    (hu : 0 < (1+u/(Real.log N : ℂ)).re) (hv : 0 < (1+v/(Real.log N : ℂ)).re) :
    criticalMixedMellinCollisionMoment k u v tau N =
      ∑ n ∈ Finset.Icc 0 N,collisionProfile k u v
        ((n : ℝ)⁻¹,(Real.log n/Real.log N,primePhase tau n))*(mertensPrimeWeight n : ℂ) := by
  rw [← prime_weighted_sum]
  unfold criticalMixedMellinCollisionMoment
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  simp_rw [mixedActual_eq_profile _ p u v tau N hu hv]
  fin_cases k <;> simp [collisionProfile,collisionWeight_prime] <;> ring

/-- Every original mixed-frequency pair/triple collision vanishes even at one
logarithmic scale. This includes the zero-frequency boundary. -/
theorem criticalMixedMellinCollisionMoment_tendsto (k : Fin 4) (u v : ℂ) (tau : ℝ) :
    Tendsto (fun N : ℕ => criticalMixedMellinCollisionMoment k u v tau N/(Real.log N : ℂ))
      atTop (𝓝 0) := by
  apply (collision_window_zero k u v tau).congr'
  filter_upwards [response_moving_positive u,response_moving_positive v] with N hu hv
  exact (congrArg (fun z : ℂ => z/(Real.log N : ℂ))
    (mixed_collision_eq_window k u v tau N hu hv)).symm

private theorem mixed_masked_response_eq (u v : ℂ) (tau : ℝ) (N : ℕ) :
    criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I) =
    criticalMixedMellinResponseRow 0 u v tau N*criticalMixedMellinResponseRow 1 u v tau N*
      criticalMixedMellinResponseRow 2 u v tau N+
    criticalMixedMellinResponseRow 2 u v tau N*criticalMixedMellinCollisionMoment 0 u v tau N-
    criticalMixedMellinResponseRow 0 u v tau N*criticalMixedMellinCollisionMoment 1 u v tau N-
    criticalMixedMellinResponseRow 1 u v tau N*criticalMixedMellinCollisionMoment 2 u v tau N+
    criticalMixedMellinCollisionMoment 3 u v tau N := by
  simpa [criticalMixedMellinResponseRow,criticalMixedMellinCollisionMoment,criticalMellinResponse] using
    criticalMaskedMellinResponse_expansion (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)

/-- The original complete masked response, with both exclusions and all pair/triple
collisions, has the predicted mixed-frequency cubic logarithmic limit. -/
theorem criticalMixedMaskedMellinResponse_tendsto (u v : ℂ) (tau : ℝˣ) :
    Tendsto (fun N : ℕ => criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)+(tau : ℂ)*Complex.I)/(Real.log N : ℂ)^3)
      atTop (𝓝 ((1-criticalExponentialMean u)^2)) := by
  have ha := criticalMixedMellinResponseRow_tendsto 0 u v tau
  have hb := criticalMixedMellinResponseRow_tendsto 1 u v tau
  have hc := criticalMixedMellinResponseRow_tendsto 2 u v tau
  have hd0 := criticalMixedMellinCollisionMoment_tendsto 0 u v tau
  have hd1 := criticalMixedMellinCollisionMoment_tendsto 1 u v tau
  have hd2 := criticalMixedMellinCollisionMoment_tendsto 2 u v tau
  have hd3 := criticalMixedMellinCollisionMoment_tendsto 3 u v tau
  simp only [ite_true] at hb
  rw [if_neg (show (0 : Fin 4) ≠ 1 by decide)] at ha
  rw [if_neg (show (2 : Fin 4) ≠ 1 by decide)] at hc
  have h := (((((ha.mul hb).mul hc).add ((hc.mul hd0).mul criticalLogScaleInv_tendsto_zero)).sub
    ((ha.mul hd1).mul criticalLogScaleInv_tendsto_zero)).sub
    ((hb.mul hd2).mul criticalLogScaleInv_tendsto_zero)).add (hd3.mul (criticalLogScaleInv_tendsto_zero.pow 2))
  simp only [mul_zero,zero_mul,add_zero,sub_zero,mul_one] at h
  rw [← pow_two] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [mixed_masked_response_eq]
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

end RHTower.BAGTrace
