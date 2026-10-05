import GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit
import Mathlib.Topology.Compactness.Compact
/-!
# Moving logarithmic prime windows

Compact continuity along the zero-coordinate slice gives a uniform prime tail;
each fixed-prime head vanishes after logarithmic normalization. Combined with
the corpus complex Mertens window, this proves the moving-profile limit without
requiring continuity across other singularities of a rational profile.
-/

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section
namespace RHTower.BAGTrace

private theorem response_uniform_tail (R : ℝ × ℝ → ℂ)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousAt R (0,t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖R ((n : ℝ)⁻¹,t)-R (0,t)‖ < ε := by
  have he : ∀ᶠ z : ℝ in 𝓝 0, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖R (z,t)-R (0,t)‖ < ε := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hmap : ContinuousAt (fun zt : ℝ × ℝ => ((0 : ℝ),zt.2)) (0,t) :=
      continuousAt_const.prodMk continuousAt_snd
    have hc := (h0 t ht).tendsto.comp hmap.tendsto
    have he := ((h0 t ht).tendsto.sub hc).norm
    have hl : Tendsto (fun zt : ℝ × ℝ => ‖R zt-R (0,zt.2)‖) (𝓝 (0,t)) (𝓝 0) := by
      simpa only [Function.comp_def,sub_self,norm_zero] using he
    exact hl.eventually (gt_mem_nhds hε)
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (hn.eventually he)

private theorem prime_mass_ratio :
    Tendsto (fun N : ℕ => mertensPrimeWeightSum N/Real.log N) atTop (𝓝 1) := by
  have h := tendsto_mertensPrimeWindow_div_log
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 1))
  simpa [mertensPrimeWindow,mertensPrimeWeightSum] using h

/-- The inverse logarithmic normalization tends to zero. -/
theorem criticalLogScaleInv_tendsto_zero :
    Tendsto (fun N : ℕ => (Real.log N : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (tendsto_drift_zero 1)
  simpa only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_zero,one_div,Complex.ofReal_inv] using h

private def responseWindowError (R : ℝ × ℝ → ℂ) (N n : ℕ) : ℂ :=
  (R ((n : ℝ)⁻¹,Real.log n/Real.log N)-R (0,Real.log n/Real.log N))*
    (mertensPrimeWeight n : ℂ)

private theorem response_head_zero (R : ℝ × ℝ → ℂ)
    (h0 : ContinuousAt R (0,0))
    (hh : ∀ n : ℕ, n.Prime → ContinuousAt R ((n : ℝ)⁻¹,0)) (K : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/
      (Real.log N : ℂ)) atTop (𝓝 0) := by
  have ht (n : ℕ) : Tendsto (fun N : ℕ => responseWindowError R N n/(Real.log N : ℂ))
      atTop (𝓝 0) := by
    by_cases hp : n.Prime
    · have hd := tendsto_drift_zero (Real.log n)
      have ha := (hh n hp).tendsto.comp (tendsto_const_nhds.prodMk_nhds hd)
      have hb := h0.tendsto.comp (tendsto_const_nhds.prodMk_nhds hd)
      have h := (((ha.sub hb).mul_const (mertensPrimeWeight n : ℂ)).mul criticalLogScaleInv_tendsto_zero)
      simpa only [Function.comp_def,mul_zero,responseWindowError,div_eq_mul_inv] using h
    · simp only [responseWindowError,mertensPrimeWeight,if_neg hp,
        Complex.ofReal_zero,mul_zero,zero_div]
      exact tendsto_const_nhds
  have h := tendsto_finsetSum (Finset.Icc 0 K) (fun n _ => ht n)
  simpa only [Finset.sum_div,Finset.sum_const_zero] using h

private theorem response_error_zero (R : ℝ × ℝ → ℂ)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousAt R (0,t))
    (hh : ∀ n : ℕ, n.Prime → ContinuousAt R ((n : ℝ)⁻¹,0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,responseWindowError R N n)/
      (Real.log N : ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK⟩ := response_uniform_tail R h0 (show 0 < ε/4 by positivity)
  have hhlim := response_head_zero R (h0 0 (by simp)) hh K
  have he : ∀ᶠ N : ℕ in atTop,
      ‖(∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/(Real.log N : ℂ)‖ < ε/2 := by
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
  have heqhead : (∑ n ∈ Finset.Icc 0 K,responseWindowError R N n) =
      ∑ n ∈ Finset.Icc 0 N, if n ≤ K then responseWindowError R N n else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.zero_le,true_and]
    omega
  have hdiff : (∑ n ∈ Finset.Icc 0 N,responseWindowError R N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/(Real.log N : ℂ) =
      (∑ n ∈ Finset.Icc 0 N,if n ≤ K then 0 else responseWindowError R N n)/(Real.log N : ℂ) := by
    rw [← sub_div,heqhead,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ≤ K <;> simp [hn]
  have hbd : ‖∑ n ∈ Finset.Icc 0 N,if n ≤ K then 0 else responseWindowError R N n‖ ≤
      (ε/4)*mertensPrimeWeightSum N := by
    calc _ ≤ ∑ n ∈ Finset.Icc 0 N, ‖if n ≤ K then 0 else responseWindowError R N n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 0 N, (ε/4)*mertensPrimeWeight n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hnK : n ≤ K
        · simp only [if_pos hnK,norm_zero]
          exact mul_nonneg (by positivity) (mertensPrimeWeight_nonneg n)
        · by_cases hp : n.Prime
          · have he := (hK n (by omega) _ (logRatio_mem_Icc hp (Finset.mem_Icc.mp hn).2)).le
            simp only [if_neg hnK,responseWindowError,norm_mul,Complex.norm_real,
              Real.norm_eq_abs,abs_of_nonneg (mertensPrimeWeight_nonneg n)]
            exact mul_le_mul_of_nonneg_right he (mertensPrimeWeight_nonneg n)
          · simp [responseWindowError,mertensPrimeWeight,hp]
      _ = _ := by rw [mertensPrimeWeightSum,Finset.mul_sum]
  have hsmall : ‖(∑ n ∈ Finset.Icc 0 N,responseWindowError R N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/(Real.log N : ℂ)‖ ≤ ε/2 := by
    rw [hdiff,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
    apply (div_le_iff₀ hlog).mpr
    have hm' := (div_lt_iff₀ hlog).mp hmass
    have hb := mul_le_mul_of_nonneg_left hm'.le (show 0 ≤ ε/4 by positivity)
    linarith
  rw [dist_zero_right]
  have htri := norm_add_le
    ((∑ n ∈ Finset.Icc 0 N,responseWindowError R N n)/(Real.log N : ℂ)-
      (∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/(Real.log N : ℂ))
    ((∑ n ∈ Finset.Icc 0 K,responseWindowError R N n)/(Real.log N : ℂ))
  rw [sub_add_cancel] at htri
  linarith

/-- Moving prime-window convergence from zero-slice and fixed-prime continuity. -/
theorem criticalMovingResponseWindow_tendsto (R : ℝ × ℝ → ℂ)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousAt R (0,t))
    (hh : ∀ n : ℕ, n.Prime → ContinuousAt R ((n : ℝ)⁻¹,0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 0 N,
      R ((n : ℝ)⁻¹,Real.log n/Real.log N)*(mertensPrimeWeight n : ℂ))/
      (Real.log N : ℂ)) atTop (𝓝 (∫ t in (0 : ℝ)..1,R (0,t))) := by
  have hg : ContinuousOn (fun t : ℝ => R (0,t)) (Set.Icc 0 1) := by
    intro t ht
    have hm : ContinuousAt (fun x : ℝ => ((0 : ℝ),x)) t :=
      continuousAt_const.prodMk continuousAt_id
    have hc := (h0 t ht).tendsto.comp hm.tendsto
    exact (show ContinuousAt (fun x : ℝ => R (0,x)) t from hc).continuousWithinAt
  have h := (criticalComplexPrimeWindow_tendsto hg).add (response_error_zero R h0 hh)
  simp only [add_zero] at h
  refine h.congr fun N => ?_
  rw [← add_div,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [responseWindowError]
  ring

end RHTower.BAGTrace
