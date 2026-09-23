/-
The digamma asymptotic `ψ(w) − log w → 0` (a mathlib gap), built from Euler's `GammaSeq` limit.

`logDeriv (GammaSeq · n) s = log n − ∑_{k≤n} 1/(s+k)`, and `GammaSeq → Γ` locally uniformly on the
right half-plane (uniform dominated convergence on the beta integral, dominated `s`-uniformly by
`e^{-x}(x^{a-1}+x^{b-1})`), so `logDeriv` passes to the limit: Gauss's formula
`ψ(s) = lim (log n − ∑_{k≤n} 1/(s+k))`. Combined with the integer asymptotic `ψ(N+1) − log(N+1) → 0`
(recurrence + Euler–Mascheroni) this yields `ψ(w+N) − log(w+N) → 0`, discharging the far-field anchor
of the vertical digamma bound.
-/
import Mathlib
import GaloisForLFunctions.HTGeometry.DigammaBounds
open Complex Filter MeasureTheory Set Real

namespace RHTower

theorem digamma_natCast_add_one (N : ℕ) :
    Complex.digamma ((N : ℂ) + 1)
      = -(Real.eulerMascheroniConstant : ℂ) + ∑ k ∈ Finset.range N, (1 : ℂ) / ((k : ℂ) + 1) := by
  induction N with
  | zero => simp [Complex.digamma_one]
  | succ n ih =>
    have hne : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
      intro m hc
      have hre := congrArg Complex.re hc
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re] at hre
      have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have h2 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    rw [Nat.cast_succ, Complex.digamma_apply_add_one ((n : ℂ) + 1) hne, ih,
      Finset.sum_range_succ]
    ring

theorem harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℝ) : ℂ) = ∑ k ∈ Finset.range N, (1 : ℂ) / ((k : ℂ) + 1) := by
  have h : (harmonic N : ℝ) = ∑ k ∈ Finset.range N, (1:ℝ)/((k:ℝ)+1) := by
    simp only [harmonic, one_div]; push_cast; rfl
  rw [h, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  push_cast; ring

/-- **The digamma asymptotic along the positive integers.** `ψ(N+1) − log(N+1) → 0`. -/
theorem digamma_natCast_add_one_sub_log_tendsto :
    Tendsto (fun N : ℕ => Complex.digamma ((N : ℂ) + 1) - Complex.log ((N : ℂ) + 1))
      atTop (nhds 0) := by
  have hlogcast : ∀ N : ℕ, Complex.log ((N : ℂ) + 1) = ((Real.log ((N:ℝ) + 1) : ℝ) : ℂ) := by
    intro N
    rw [show ((N:ℂ)+1) = (((N:ℝ)+1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_log (by positivity)]
  have heq : ∀ N : ℕ,
      Complex.digamma ((N : ℂ) + 1) - Complex.log ((N : ℂ) + 1)
        = (((harmonic N : ℝ) - Real.log ((N:ℝ)+1) - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    intro N
    rw [digamma_natCast_add_one, ← harmonic_cast_eq, hlogcast]
    push_cast; ring
  rw [tendsto_congr heq]
  have hR : Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log ((N:ℝ)+1)
      - Real.eulerMascheroniConstant)) atTop (nhds 0) := by
    have h := Real.tendsto_harmonic_sub_log_add_one.sub_const Real.eulerMascheroniConstant
    simpa [sub_self] using h
  have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hR
  simp only [Complex.ofReal_zero] at hcomp
  exact hcomp

theorem logDeriv_natCast_cpow (n : ℕ) (hn : (n:ℂ) ≠ 0) (s : ℂ) :
    logDeriv (fun s => (n:ℂ)^s) s = Complex.log n := by
  rw [logDeriv_apply, (hasStrictDerivAt_const_cpow (Or.inl hn)).hasDerivAt.deriv]
  rw [mul_comm, mul_div_assoc, div_self (Complex.cpow_ne_zero_iff.mpr (Or.inl hn)), mul_one]

theorem logDeriv_add_const (c s : ℂ) :
    logDeriv (fun s => s + c) s = 1/(s+c) := by
  rw [logDeriv_apply]
  have hd : deriv (fun s : ℂ => s + c) s = 1 := by simp
  rw [hd]

theorem logDeriv_GammaSeq (n : ℕ) (hn : (n:ℂ) ≠ 0) (s : ℂ)
    (hs : ∀ j ∈ Finset.range (n+1), s + (j:ℂ) ≠ 0) :
    logDeriv (fun s => Complex.GammaSeq s n) s
      = Complex.log n - ∑ j ∈ Finset.range (n+1), 1/(s + (j:ℂ)) := by
  have hprodne : (∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hs
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnum : (n:ℂ)^s * (n.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hn)) hfac
  have hdcpow : DifferentiableAt ℂ (fun s => (n:ℂ)^s) s :=
    (hasStrictDerivAt_const_cpow (Or.inl hn)).hasDerivAt.differentiableAt
  have hdf : DifferentiableAt ℂ (fun s => (n:ℂ)^s * (n.factorial : ℂ)) s := hdcpow.mul_const _
  have hdg : DifferentiableAt ℂ (fun s => ∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) s := by
    fun_prop
  have hgs : (fun s => Complex.GammaSeq s n) = fun s =>
      ((n:ℂ)^s * (n.factorial : ℂ)) / (∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) := by
    funext s; rw [Complex.GammaSeq]
  rw [hgs, logDeriv_div s hnum hprodne hdf hdg]
  congr 1
  · rw [logDeriv_mul_const s (n.factorial : ℂ) hfac, logDeriv_natCast_cpow n hn]
  · rw [logDeriv_prod hs (fun j _ => (differentiable_id.add_const _).differentiableAt)]
    apply Finset.sum_congr rfl
    intro j hj
    exact logDeriv_add_const (j:ℂ) s

/-- `x^{c-1} ≤ x^{a-1} + x^{b-1}` for `0 < x` and `a ≤ c ≤ b`. -/
theorem rpow_re_le_sum {a b c x : ℝ} (hx : 0 < x) (hac : a ≤ c) (hcb : c ≤ b) :
    x ^ (c - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  by_cases hx1 : 1 ≤ x
  · have h1 : x ^ (c - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hnn : 0 ≤ x ^ (a - 1) := le_of_lt (Real.rpow_pos_of_pos hx _)
    linarith
  · have h1 : x ^ (c - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx (le_of_lt (not_le.mp hx1)) (by linarith)
    have hnn : 0 ≤ x ^ (b - 1) := le_of_lt (Real.rpow_pos_of_pos hx _)
    linarith

/-- The pointwise integrand-difference bound, uniform in `s` over the strip `a ≤ re s ≤ b`. -/
theorem integrand_diff_norm_le {a b : ℝ} {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖(Set.Ioc 0 (n:ℝ)).indicator (fun x : ℝ => ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) x
        - (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖
      ≤ (Real.exp (-x) - (Set.Ioc 0 (n:ℝ)).indicator (fun x : ℝ => ((1 - x / n) ^ n : ℝ)) x)
          * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hxcpow : ‖(x : ℂ) ^ (s - 1)‖ = x ^ (s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
  have hxre_le : x ^ (s.re - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := rpow_re_le_sum hx hsa hsb
  rcases lt_or_ge (n : ℝ) x with hxn | hxn
  · -- x > n: indicator is 0
    have hnotmem : x ∉ Set.Ioc 0 (n:ℝ) := by
      simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => hxn
    rw [Set.indicator_of_notMem hnotmem, Set.indicator_of_notMem hnotmem]
    rw [zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      hxcpow, sub_zero]
    exact mul_le_mul_of_nonneg_left hxre_le (le_of_lt (Real.exp_pos _))
  · -- 0 < x ≤ n
    have hmem : x ∈ Set.Ioc 0 (n:ℝ) := ⟨hx, hxn⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    rw [← sub_mul, norm_mul, hxcpow]
    have hle : ((1 - x / n) ^ n : ℝ) ≤ Real.exp (-x) := by
      have hxnle : x / n ≤ 1 := div_le_one_of_le₀ hxn (by positivity)
      exact one_sub_div_pow_le_exp_neg hxn
    have hpow_nonneg : (0:ℝ) ≤ (1 - x / n) ^ n := by
      apply pow_nonneg; have : x / n ≤ 1 := div_le_one_of_le₀ hxn (by positivity); linarith
    have hnormsub : ‖(((1 - x / n) ^ n : ℝ) : ℂ) - (Real.exp (-x) : ℂ)‖
        = Real.exp (-x) - (1 - x / n) ^ n := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    rw [hnormsub]
    exact mul_le_mul_of_nonneg_left hxre_le (by linarith)

theorem En_tendsto_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ),
        (Real.exp (-x) - (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)
          * (x ^ (a - 1) + x ^ (b - 1))) atTop (nhds 0) := by
  set dom : ℝ → ℝ := fun x => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)) with hdom
  have hdomint : IntegrableOn dom (Ioi 0) volume := by
    have h1 := Real.GammaIntegral_convergent ha
    have h2 := Real.GammaIntegral_convergent (lt_of_lt_of_le ha hab)
    have hsum := h1.add h2
    refine hsum.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, hdom, mul_add]
  set gn : ℕ → ℝ → ℝ := fun n x =>
      (Real.exp (-x) - (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)
        * (x ^ (a - 1) + x ^ (b - 1)) with hgn
  have hpolycont : ContinuousOn (fun x : ℝ => x ^ (a - 1) + x ^ (b - 1)) (Ioi 0) := by
    apply ContinuousOn.add
    · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
    · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
  have hmeas : ∀ n, AEStronglyMeasurable (gn n) (volume.restrict (Ioi 0)) := by
    intro n
    refine AEStronglyMeasurable.mul ?_ (hpolycont.aestronglyMeasurable measurableSet_Ioi)
    refine AEStronglyMeasurable.sub ?_ ?_
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).indicator measurableSet_Ioc
  have hbound : ∀ n, ∀ᵐ x ∂(volume.restrict (Ioi 0)), ‖gn n x‖ ≤ dom x := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hxpos : (0:ℝ) < x := hx
    have hpoly_nonneg : (0:ℝ) ≤ x ^ (a - 1) + x ^ (b - 1) := by positivity
    have hhn_nonneg : 0 ≤ (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x := by
      by_cases hxn : x ≤ (n:ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hxpos, hxn⟩)]
        apply pow_nonneg; have : x / n ≤ 1 := div_le_one_of_le₀ hxn (by positivity); linarith
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => lt_of_not_ge hxn)]
    have hhn_le : (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x ≤ Real.exp (-x) := by
      by_cases hxn : x ≤ (n:ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hxpos, hxn⟩)]; exact one_sub_div_pow_le_exp_neg hxn
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => lt_of_not_ge hxn)]
        exact le_of_lt (Real.exp_pos _)
    rw [hgn, Real.norm_eq_abs, abs_of_nonneg (by positivity), hdom]
    apply mul_le_mul_of_nonneg_right _ hpoly_nonneg
    linarith
  have htends : ∀ᵐ x ∂(volume.restrict (Ioi 0)), Tendsto (fun n => gn n x) atTop (nhds 0) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hxpos : (0:ℝ) < x := hx
    have hhn : Tendsto (fun n : ℕ => (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)
        atTop (nhds (Real.exp (-x))) := by
      refine Tendsto.congr' ?_ (?_ : Tendsto (fun n : ℕ => (1 - x / n) ^ n) atTop (nhds (Real.exp (-x))))
      · filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
        rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hxpos, by rw [Nat.ceil_le] at hn; exact hn⟩)]
      · have := Real.tendsto_one_add_div_pow_exp (-x)
        refine this.congr (fun n => ?_); rw [neg_div, ← sub_eq_add_neg]
    have hsub : Tendsto (fun n : ℕ => (Real.exp (-x)
        - (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)) atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := Real.exp (-x))).sub hhn
      simpa using this
    have hlim := hsub.mul_const (x ^ (a - 1) + x ^ (b - 1))
    simpa [hgn] using hlim
  have := tendsto_integral_of_dominated_convergence dom hmeas hdomint hbound htends
  simpa using this


theorem GammaSeq_sub_Gamma_norm_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hsa : a ≤ s.re) (hsb : s.re ≤ b) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.GammaSeq s n - Complex.Gamma s‖ ≤ ∫ x in Ioi (0:ℝ),
        (Real.exp (-x) - (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)
          * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hspos : 0 < s.re := lt_of_lt_of_le ha hsa
  have hGS : Complex.GammaSeq s n = ∫ x in Ioi (0:ℝ),
      (Ioc 0 (n:ℝ)).indicator (fun x => ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) x := by
    rw [Complex.GammaSeq_eq_approx_Gamma_integral hspos hn,
      intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ n),
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
  have hG : Complex.Gamma s = ∫ x in Ioi (0:ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1) := by
    rw [Complex.Gamma_eq_integral hspos, Complex.GammaIntegral]
  have hf_int : Integrable
      (fun x => (Ioc 0 (n:ℝ)).indicator (fun x => ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) x)
      (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ← IntegrableOn,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0:ℝ) ≤ n)]
    apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_cpow'
      rw [Complex.sub_re, Complex.one_re]; linarith
    · fun_prop
  have hg_int : Integrable (fun x => (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1))
      (volume.restrict (Ioi 0)) := Complex.GammaIntegral_convergent hspos
  have hgn_int : Integrable
      (fun x => (Real.exp (-x) - (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x)
        * (x ^ (a - 1) + x ^ (b - 1))) (volume.restrict (Ioi 0)) := by
    have hdomint : IntegrableOn (fun x => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) (Ioi 0) volume := by
      have h1 := Real.GammaIntegral_convergent ha
      have h2 := Real.GammaIntegral_convergent (lt_of_lt_of_le ha hab)
      have hsum := h1.add h2
      refine hsum.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [Pi.add_apply, mul_add]
    apply Integrable.mono' hdomint
    · apply AEStronglyMeasurable.mul
      · refine AEStronglyMeasurable.sub ?_ ?_
        · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
        · exact (Continuous.aestronglyMeasurable (by fun_prop)).indicator measurableSet_Ioc
      · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
        apply ContinuousOn.add <;> exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      have hxpos : (0:ℝ) < x := hx
      have hpoly : (0:ℝ) ≤ x ^ (a - 1) + x ^ (b - 1) := by positivity
      have hind0 : 0 ≤ (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x := by
        by_cases hxn : x ≤ (n:ℝ)
        · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hxpos, hxn⟩)]
          apply pow_nonneg; have : x / n ≤ 1 := div_le_one_of_le₀ hxn (by positivity); linarith
        · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => lt_of_not_ge hxn)]
      have hindle : (Ioc 0 (n:ℝ)).indicator (fun x => (1 - x / n) ^ n) x ≤ Real.exp (-x) := by
        by_cases hxn : x ≤ (n:ℝ)
        · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hxpos, hxn⟩)]; exact one_sub_div_pow_le_exp_neg hxn
        · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => lt_of_not_ge hxn)]
          exact le_of_lt (Real.exp_pos _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ hpoly
      linarith
  rw [hGS, hG, ← integral_sub hf_int hg_int]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (ae_of_all _ (fun x => norm_nonneg _)) hgn_int ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact integrand_diff_norm_le hsa hsb n hx


theorem GammaSeq_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (fun n s => Complex.GammaSeq s n) Complex.Gamma atTop
      {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro K hKsub hKcomp
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall (fun n x hx => absurd hx (Set.notMem_empty x))
  · obtain ⟨sm, hsm_mem, hsm⟩ := hKcomp.exists_isMinOn hKne Complex.continuous_re.continuousOn
    obtain ⟨sM, hsM_mem, hsM⟩ := hKcomp.exists_isMaxOn hKne Complex.continuous_re.continuousOn
    set a := sm.re with ha
    set b := sM.re with hb
    have ha_pos : 0 < a := hKsub hsm_mem
    have hab : a ≤ b := (isMinOn_iff.mp hsm) sM hsM_mem
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hEn := En_tendsto_zero ha_pos hab
    filter_upwards [hEn.eventually (Iio_mem_nhds hε), eventually_ge_atTop 1] with n hnE hn1
    intro s hsK
    have hsa : a ≤ s.re := (isMinOn_iff.mp hsm) s hsK
    have hsb : s.re ≤ b := (isMaxOn_iff.mp hsM) s hsK
    have hbound := GammaSeq_sub_Gamma_norm_le ha_pos hab hsa hsb (Nat.one_le_iff_ne_zero.mp hn1)
    rw [Complex.dist_eq, norm_sub_rev]
    exact lt_of_le_of_lt hbound hnE


theorem GammaSeq_differentiableOn {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hsre : 0 < s.re := hs
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  apply DifferentiableAt.differentiableWithinAt
  have hprodne : (∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _ hc
    have hre := congrArg Complex.re hc
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    have hjnn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have hnum : DifferentiableAt ℂ (fun s => (n:ℂ)^s * (n.factorial:ℂ)) s :=
    ((hasStrictDerivAt_const_cpow (Or.inl hnne)).hasDerivAt.differentiableAt).mul_const _
  have hden : DifferentiableAt ℂ (fun s => ∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) s := by
    fun_prop
  have heq : (fun s => Complex.GammaSeq s n) = fun s =>
      ((n:ℂ)^s * (n.factorial:ℂ)) / (∏ j ∈ Finset.range (n+1), (s + (j:ℂ))) := by
    funext s; rw [Complex.GammaSeq]
  rw [heq]
  exact hnum.div hden hprodne

/-- **Gauss's formula for the digamma function.** For `0 < Re s`,
`ψ(s) = lim_n (log n − ∑_{k≤n} 1/(s+k))`. -/
theorem gauss_digamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => Complex.log n - ∑ j ∈ Finset.range (n+1), 1/(s + (j:ℂ)))
      atTop (nhds (Complex.digamma s)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m hc => by
    rw [hc] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith)
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (fun s => Complex.GammaSeq s n)
      {s : ℂ | 0 < s.re} := by
    filter_upwards [eventually_ge_atTop 1] with n hn using GammaSeq_differentiableOn hn
  have hld := logDeriv_tendsto hU hs GammaSeq_tendstoLocallyUniformlyOn hdiff hgne
  rw [show Complex.digamma s = logDeriv Complex.Gamma s from congrFun Complex.digamma_def s]
  refine hld.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hsj : ∀ j ∈ Finset.range (n+1), s + (j:ℂ) ≠ 0 := by
    intro j _ hc
    have hre := congrArg Complex.re hc
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  exact logDeriv_GammaSeq n hnne s hsj


theorem sum_inv_sq_shift_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ j ∈ Finset.range M, (1:ℝ)/((N:ℝ)+1+j)^(2 : ℕ) ≤ 1/(N:ℝ) := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hstep : ∀ j : ℕ, (1:ℝ)/((N:ℝ)+1+j)^(2 : ℕ) ≤ 1/((N:ℝ)+j) - 1/((N:ℝ)+1+j) := by
    intro j
    have hNj : (0:ℝ) < (N:ℝ)+j := by have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j; linarith
    have hNj1 : (0:ℝ) < (N:ℝ)+1+j := by linarith
    have heq : 1/((N:ℝ)+j) - 1/((N:ℝ)+1+j) = 1/(((N:ℝ)+j)*((N:ℝ)+1+j)) := by
      field_simp; ring
    rw [heq]
    gcongr
    nlinarith [hNj, hNj1]
  have htel : ∑ j ∈ Finset.range M, (1/((N:ℝ)+j) - 1/((N:ℝ)+1+j)) = 1/(N:ℝ) - 1/((N:ℝ)+M) := by
    have key : ∀ i : ℕ, (1:ℝ)/((N:ℝ)+i) - 1/((N:ℝ)+1+i)
        = (fun k : ℕ => (1:ℝ)/((N:ℝ)+k)) i - (fun k : ℕ => (1:ℝ)/((N:ℝ)+k)) (i+1) := by
      intro i; simp only; congr 2; push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => key i),
      Finset.sum_range_sub' (fun k : ℕ => (1:ℝ)/((N:ℝ)+k)) M]
    push_cast; ring
  calc ∑ j ∈ Finset.range M, (1:ℝ)/((N:ℝ)+1+j)^(2 : ℕ)
      ≤ ∑ j ∈ Finset.range M, (1/((N:ℝ)+j) - 1/((N:ℝ)+1+j)) := Finset.sum_le_sum (fun j _ => hstep j)
    _ = 1/(N:ℝ) - 1/((N:ℝ)+M) := htel
    _ ≤ 1/(N:ℝ) := by
        have : (0:ℝ) < (N:ℝ)+M := by positivity
        have : (0:ℝ) ≤ 1/((N:ℝ)+M) := by positivity
        linarith

theorem digamma_shift_diff_bound {w : ℂ} {N : ℕ} (hN : 1 ≤ N) (hwN : 0 < (w + (N:ℂ)).re)
    (hthr : 2 * ‖w - 1‖ ≤ (N:ℝ)) :
    ‖Complex.digamma (w + (N:ℂ)) - Complex.digamma ((N:ℂ) + 1)‖ ≤ 2 * ‖w - 1‖ / (N:ℝ) := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hgw := gauss_digamma hwN
  have hg1 := gauss_digamma (show 0 < ((N:ℂ) + 1).re by
    rw [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  have hdiff := hgw.sub hg1
  have hSm : ∀ m : ℕ,
      (Complex.log m - ∑ j ∈ Finset.range (m+1), 1/(w + (N:ℂ) + (j:ℂ)))
        - (Complex.log m - ∑ j ∈ Finset.range (m+1), 1/((N:ℂ) + 1 + (j:ℂ)))
      = ∑ j ∈ Finset.range (m+1), (1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ))) := by
    intro m; rw [Finset.sum_sub_distrib]; ring
  have htermbound : ∀ (j : ℕ),
      ‖1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ))‖ ≤ 2 * ‖w - 1‖ / ((N:ℝ)+1+j)^(2 : ℕ) := by
    intro j
    set A : ℂ := (N:ℂ) + 1 + (j:ℂ) with hAdef
    set B : ℂ := w + (N:ℂ) + (j:ℂ) with hBdef
    have hApos : (0:ℝ) < (N:ℝ)+1+j := by positivity
    have hAnorm : ‖A‖ = (N:ℝ)+1+j := by
      rw [hAdef, show (N:ℂ) + 1 + (j:ℂ) = (((N:ℝ)+1+j : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    have hBA : B = A + (w - 1) := by rw [hAdef, hBdef]; ring
    have hBnorm : ((N:ℝ)+1+j)/2 ≤ ‖B‖ := by
      have hrev : ‖A‖ - ‖w - 1‖ ≤ ‖B‖ := by
        have h := norm_sub_norm_le A (-(w-1))
        rw [sub_neg_eq_add, ← hBA, norm_neg] at h
        exact h
      have : ‖w - 1‖ ≤ ((N:ℝ)+1+j)/2 := by
        have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith [hthr]
      rw [hAnorm] at hrev; linarith
    have hAne : A ≠ 0 := by rw [← norm_ne_zero_iff, hAnorm]; positivity
    have hBne : B ≠ 0 := by rw [← norm_ne_zero_iff]; have : (0:ℝ) < ((N:ℝ)+1+j)/2 := by positivity
                            linarith
    have hdiffeq : 1/A - 1/B = (w - 1)/(A * B) := by
      rw [div_sub_div _ _ hAne hBne]; congr 1; rw [hBA]; ring
    rw [hdiffeq, norm_div, norm_mul, hAnorm]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : (0:ℝ) ≤ ‖w - 1‖ * ((N:ℝ)+1+j) * (2 * ‖B‖ - ((N:ℝ)+1+j)) := by
      apply mul_nonneg (mul_nonneg (norm_nonneg _) hApos.le)
      linarith [hBnorm]
    nlinarith [hprod]
  have hbound : ∀ m : ℕ,
      ‖∑ j ∈ Finset.range (m+1), (1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ)))‖
        ≤ 2 * ‖w - 1‖ / (N:ℝ) := by
    intro m
    calc ‖∑ j ∈ Finset.range (m+1), (1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ)))‖
        ≤ ∑ j ∈ Finset.range (m+1), ‖1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (m+1), 2 * ‖w - 1‖ / ((N:ℝ)+1+j)^(2 : ℕ) :=
          Finset.sum_le_sum (fun j _ => htermbound j)
      _ = 2 * ‖w - 1‖ * ∑ j ∈ Finset.range (m+1), 1 / ((N:ℝ)+1+j)^(2 : ℕ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ 2 * ‖w - 1‖ * (1 / (N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sq_shift_le hN (m+1)) (by positivity)
      _ = 2 * ‖w - 1‖ / (N:ℝ) := by ring
  have hlim : Tendsto (fun m : ℕ =>
      ‖∑ j ∈ Finset.range (m+1), (1/((N:ℂ) + 1 + (j:ℂ)) - 1/(w + (N:ℂ) + (j:ℂ)))‖)
      atTop (nhds ‖Complex.digamma (w + (N:ℂ)) - Complex.digamma ((N:ℂ) + 1)‖) := by
    apply Filter.Tendsto.norm
    exact hdiff.congr hSm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)


theorem digamma_vertical_anchor_tendsto (σ t : ℝ) :
    Tendsto (fun N : ℕ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (N:ℂ))).re
        - (1 / 2) * Real.log ((σ + (N:ℝ)) ^ 2 + t ^ 2)) atTop (nhds 0) := by
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hw
  have hwre : w.re = σ := by rw [hw]; simp
  have hwadd : ∀ N : ℕ, (σ : ℂ) + (t : ℂ) * Complex.I + (N:ℂ) = w + (N:ℂ) := by
    intro N; rw [hw]
  have hnormsq : ∀ N : ℕ, ‖w + (N:ℂ)‖ = Real.sqrt ((σ + (N:ℝ)) ^ 2 + t ^ 2) := by
    intro N
    rw [hw, show (σ : ℂ) + (t : ℂ) * Complex.I + (N:ℂ) = (((σ + (N:ℝ)):ℝ):ℂ) + ((t:ℝ):ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I]
  -- P1 : Re(ψ(w+N) - ψ(N+1)) → 0
  have hP1 : Tendsto (fun N : ℕ => (Complex.digamma (w + (N:ℂ))).re
      - (Complex.digamma ((N:ℂ) + 1)).re) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖w - 1‖))
    · filter_upwards [eventually_ge_atTop 1,
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-σ + 1),
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * ‖w - 1‖)]
        with N hN1 hσN hthr
      have hwN : 0 < (w + (N:ℂ)).re := by rw [Complex.add_re, hwre, Complex.natCast_re]; linarith
      have hb := digamma_shift_diff_bound hN1 hwN hthr
      rw [← Complex.sub_re]
      calc ‖(Complex.digamma (w + (N:ℂ)) - Complex.digamma ((N:ℂ) + 1)).re‖
          ≤ ‖Complex.digamma (w + (N:ℂ)) - Complex.digamma ((N:ℂ) + 1)‖ := by
            rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
        _ ≤ 2 * ‖w - 1‖ / (N:ℝ) := hb
  -- P2 : Re ψ(N+1) - log(N+1) → 0
  have hP2 : Tendsto (fun N : ℕ => (Complex.digamma ((N:ℂ) + 1)).re - Real.log ((N:ℝ) + 1))
      atTop (nhds 0) := by
    have hcomplex := digamma_natCast_add_one_sub_log_tendsto
    have hre : Tendsto (fun N : ℕ => (Complex.digamma ((N:ℂ) + 1) - Complex.log ((N:ℂ) + 1)).re)
        atTop (nhds 0) := by
      have := (Complex.continuous_re.tendsto _).comp hcomplex
      apply this.congr'
      filter_upwards [] with N
      simp only [Function.comp_apply, Complex.sub_re]
    apply hre.congr
    intro N
    rw [Complex.sub_re]
    congr 1
    rw [Complex.log_re, show ((N:ℂ) + 1) = (((N:ℝ)+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  -- P3 : log(N+1) - ½ log((σ+N)²+t²) → 0
  have hP3 : Tendsto (fun N : ℕ => Real.log ((N:ℝ) + 1) - (1/2) * Real.log ((σ + (N:ℝ))^(2 : ℕ) + t^(2 : ℕ)))
      atTop (nhds 0) := by
    have hcdiv : ∀ c : ℝ, Tendsto (fun N : ℕ => c/((N:ℝ)+1)) atTop (nhds 0) := by
      intro c
      have hden : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      simpa using hden.const_div_atTop c
    have hratio : Tendsto (fun N : ℕ => ((σ + (N:ℝ))^(2 : ℕ) + t^(2 : ℕ)) / ((N:ℝ)+1)^(2 : ℕ)) atTop (nhds 1) := by
      have h1 : Tendsto (fun N : ℕ => (σ + (N:ℝ))/((N:ℝ)+1)) atTop (nhds 1) := by
        have heq : (fun N : ℕ => (σ + (N:ℝ))/((N:ℝ)+1)) = fun N : ℕ => 1 + (σ - 1)/((N:ℝ)+1) := by
          funext N; have : (N:ℝ)+1 ≠ 0 := by positivity
          field_simp; ring
        rw [heq]; simpa using tendsto_const_nhds.add (hcdiv (σ - 1))
      have h2 : Tendsto (fun N : ℕ => t/((N:ℝ)+1)) atTop (nhds 0) := hcdiv t
      have hcomb : Tendsto (fun N : ℕ => ((σ + (N:ℝ))/((N:ℝ)+1))^(2 : ℕ) + (t/((N:ℝ)+1))^(2 : ℕ))
          atTop (nhds 1) := by simpa using (h1.pow 2).add (h2.pow 2)
      apply hcomb.congr'
      filter_upwards [eventually_ge_atTop 1] with N _
      have hne : (N:ℝ)+1 ≠ 0 := by positivity
      field_simp
    have hlog : Tendsto (fun N : ℕ => Real.log (((σ + (N:ℝ))^(2 : ℕ) + t^(2 : ℕ)) / ((N:ℝ)+1)^(2 : ℕ)))
        atTop (nhds 0) := by
      have := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hratio
      have hcomp :
          Tendsto (Real.log ∘ fun N : ℕ =>
            ((σ + (N : ℝ)) ^ 2 + t ^ 2) / ((N : ℝ) + 1) ^ 2)
            atTop (nhds 0) := by
        simpa only [Real.log_one] using this
      apply hcomp.congr'
      filter_upwards [] with N
      rfl
    have hP3fin : Tendsto (fun N : ℕ =>
        (-1/2 : ℝ) * Real.log (((σ + (N:ℝ))^(2 : ℕ) + t^(2 : ℕ)) / ((N:ℝ)+1)^(2 : ℕ))) atTop (nhds 0) := by
      simpa using hlog.const_mul (-1/2 : ℝ)
    apply hP3fin.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-σ)] with N hσN
    have hden : (0:ℝ) < ((N:ℝ)+1)^(2 : ℕ) := by positivity
    have hpos : (0:ℝ) < (σ + (N:ℝ))^(2 : ℕ) + t^(2 : ℕ) := by
      have : (0:ℝ) < σ + (N:ℝ) := by linarith
      positivity
    rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hden),
      show Real.log (((N:ℝ)+1)^(2 : ℕ)) = 2 * Real.log ((N:ℝ)+1) by rw [Real.log_pow]; push_cast; ring]
    ring
  -- assemble
  have hsum := (hP1.add hP2).add hP3
  simp only [add_zero] at hsum
  apply hsum.congr
  intro N
  rw [hwadd N]
  ring

/-- **The vertical digamma bound, unconditionally.** `|Re ψ(σ+it) − ½·log(σ²+t²)| ≤ 1/t² + π/(2t)`,
with the far-field anchor now discharged by the digamma asymptotic. -/
theorem re_digamma_vertical_bound_uncond {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    |(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - (1 / 2) * Real.log (σ ^ 2 + t ^ 2)|
      ≤ 1 / t ^ 2 + Real.pi / (2 * t) :=
  re_digamma_vertical_bound hσ ht (digamma_vertical_anchor_tendsto σ t)


theorem hasDerivAt_log_norm_Gamma (y x : ℝ)
    (hz : ∀ m : ℕ, (x:ℂ) + (y:ℂ) * I ≠ -(m:ℂ))
    (hΓ : Complex.Gamma ((x:ℂ) + (y:ℂ) * I) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x:ℂ) + (y:ℂ) * I)‖)
      (Complex.digamma ((x:ℂ) + (y:ℂ) * I)).re x := by
  set z : ℂ := (x:ℂ) + (y:ℂ) * I with hzdef
  have hg : HasDerivAt (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) 1 x := by
    have h1 : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      exact Complex.ofRealCLM.hasDerivAt
    simpa using h1.add_const ((y:ℂ) * I)
  have hΓd : HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z :=
    (Complex.differentiableAt_Gamma z hz).hasDerivAt
  have hu : HasDerivAt (fun x : ℝ => Complex.Gamma ((x:ℂ) + (y:ℂ) * I)) (deriv Complex.Gamma z) x := by
    have h := hΓd.comp x hg
    have hfun :
        Complex.Gamma ∘ (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) =
          (fun x : ℝ => Complex.Gamma ((x : ℂ) + (y : ℂ) * I)) := by
      funext u
      rfl
    rw [hfun] at h
    apply h.congr_deriv
    ring
  have hure : HasDerivAt (fun x : ℝ => (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).re)
      (deriv Complex.Gamma z).re x := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hu
  have huim : HasDerivAt (fun x : ℝ => (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).im)
      (deriv Complex.Gamma z).im x := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hu
  set B : ℝ := 2 * ((Complex.Gamma z).re * (deriv Complex.Gamma z).re
        + (Complex.Gamma z).im * (deriv Complex.Gamma z).im) with hBdef
  have hnsq : HasDerivAt (fun x : ℝ => Complex.normSq (Complex.Gamma ((x:ℂ) + (y:ℂ) * I))) B x := by
    have h := hure.mul hure |>.add (huim.mul huim)
    have hfn : (fun x : ℝ => Complex.normSq (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)))
        = fun x : ℝ => (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).re * (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).re
          + (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).im * (Complex.Gamma ((x:ℂ) + (y:ℂ) * I)).im := by
      funext x; rw [Complex.normSq_apply]
    rw [hfn]
    apply h.congr_deriv
    rw [hBdef]; ring
  have hn0 : Complex.normSq (Complex.Gamma z) ≠ 0 := fun h => hΓ (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hn0).comp x hnsq
  have hF := hlog.const_mul (1/2 : ℝ)
  simp only [Function.comp] at hF
  have hfunF : (fun x : ℝ => (1/2 : ℝ) * Real.log (Complex.normSq (Complex.Gamma ((x:ℂ) + (y:ℂ) * I))))
      = fun x : ℝ => Real.log ‖Complex.Gamma ((x:ℂ) + (y:ℂ) * I)‖ := by
    funext x
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast; ring
  rw [hfunF] at hF
  apply hF.congr_deriv
  -- Re ψ z = ½ · (1/normSq)·B
  rw [Complex.digamma_def, logDeriv_apply, Complex.div_re, hBdef]
  field_simp


theorem digamma_continuousOn_uhp :
    ContinuousOn Complex.digamma {z : ℂ | 0 < z.im} := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hne : ∀ z ∈ {z : ℂ | 0 < z.im}, ∀ m : ℕ, z ≠ -(m:ℂ) := by
    intro z hz m hc
    rw [hc] at hz
    simp only [Set.mem_setOf_eq, Complex.neg_im, Complex.natCast_im, neg_zero] at hz
    exact lt_irrefl 0 hz
  have hΓdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.im} :=
    fun z hz => (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hΓanalytic : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.im} :=
    hΓdiff.analyticOnNhd hUopen
  have hderivcont : ContinuousOn (deriv Complex.Gamma) {z : ℂ | 0 < z.im} :=
    hΓanalytic.deriv.continuousOn
  have hΓcont : ContinuousOn Complex.Gamma {z : ℂ | 0 < z.im} := hΓdiff.continuousOn
  have hΓne : ∀ z ∈ {z : ℂ | 0 < z.im}, Complex.Gamma z ≠ 0 :=
    fun z hz => Complex.Gamma_ne_zero (hne z hz)
  have : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z; rw [Complex.digamma_def, logDeriv_apply]
  rw [this]
  exact hderivcont.div hΓcont hΓne


theorem ftc_log_norm_Gamma {a b y : ℝ} (hy : 0 < y) :
    ∫ x in a..b, (Complex.digamma ((x:ℂ) + (y:ℂ) * I)).re
      = Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
        - Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := by
  have hne : ∀ x : ℝ, ∀ m : ℕ, (x:ℂ) + (y:ℂ) * I ≠ -(m:ℂ) := by
    intro x m hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, Complex.neg_im, Complex.natCast_im, neg_zero] at him
    linarith
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact hasDerivAt_log_norm_Gamma y x (hne x) (Complex.Gamma_ne_zero (hne x))
  · apply ContinuousOn.intervalIntegrable
    have hφ : ContinuousOn (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) := by fun_prop
    have hmaps : Set.MapsTo (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) {z : ℂ | 0 < z.im} := by
      intro x _
      simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
      exact hy
    exact Complex.continuous_re.comp_continuousOn (digamma_continuousOn_uhp.comp hφ hmaps)

/-- Lower bound on `Re ψ` on the vertical line, from the vertical digamma bound: for `x ≥ 0`,
`Re ψ(x+iy) ≥ log y − (1/y² + π/(2y))`. -/
theorem re_digamma_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.log y - (1 / y ^ 2 + Real.pi / (2 * y)) ≤ (Complex.digamma ((x:ℂ) + (y:ℂ) * I)).re := by
  have hb := re_digamma_vertical_bound_uncond hx hy
  have habs := abs_le.mp hb
  have hlogle : Real.log y ≤ (1/2) * Real.log (x ^ 2 + y ^ 2) := by
    rw [show Real.log y = (1/2) * Real.log (y^(2 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    nlinarith [sq_nonneg x]
  linarith [habs.1]

end RHTower
