import GaloisForLFunctions.RHTower.LeeYangChainQuarterTurnZeroCount
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Integer-anchored Γ-site Lee–Yang chains cannot approximate Ξ

The Γ-site chain has fields `e^{−i t log((k+2)/(k+1))}`, so that a single domain wall after site
`k` carries the integer frequency `log (k+2)`.  Its first site has frequency `log 2`.  By the
quarter-turn zero count, every such chain — of any length, with any real fugacities in
`[−1, 1]`, signed or ferromagnetic — vanishes at some real point of `[0, π/log 2] ⊂ [0, 4.6]`
(`exists_gammaChainZ_eq_zero`).  The centered `Ξ` has no real zero there: ξ has no zero of
ordinate at most `√32` (`XiC_ne_zero_of_mem_Icc_pi_div_log_two`).

Consequently no multiplication by any normalizer brings a Γ-site chain uniformly closer to
`E · Ξ` on `[0, π/log 2]` than `min |E Ξ|` (`exists_gammaChain_error_eq`), and no family of
normalized Γ-site chains converges to `E · Ξ` uniformly there
(`not_tendstoUniformlyOn_gammaChain_XiC`).
-/

open Complex Finset Set Filter Topology

namespace RHTower.LeeYangChain

noncomputable section

theorem gammaFreq_zero : gammaFreq 0 = Real.log 2 := by
  norm_num [gammaFreq]

/-- **Forced early zero.**  Every Γ-site chain with fugacities in `[−1, 1]` vanishes somewhere on
`[0, π/log 2]`. -/
theorem exists_gammaChainZ_eq_zero {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1) (N : ℕ) :
    ∃ t ∈ Icc 0 (Real.pi / Real.log 2), chainZ c (lineField gammaFreq t) N = 0 := by
  have h := exists_chainZ_eq_zero_Icc hc (fun k => (gammaFreq_pos k).le) (Nat.zero_le N)
    (gammaFreq_pos 0)
  rwa [gammaFreq_zero] at h

theorem sq_le_thirtyTwo_of_mem_Icc_pi_div_log_two {t : ℝ}
    (ht : t ∈ Icc 0 (Real.pi / Real.log 2)) : t ^ 2 ≤ 32 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log 2 := by linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h1 : t * Real.log 2 ≤ Real.pi := (le_div_iff₀ hlogpos).mp ht.2
  have h2 : t < 5 := by nlinarith [ht.1]
  nlinarith [ht.1]

/-- `Ξ` has no real zero on `[0, π/log 2]`. -/
theorem XiC_ne_zero_of_mem_Icc_pi_div_log_two {t : ℝ}
    (ht : t ∈ Icc 0 (Real.pi / Real.log 2)) : XiC (t : ℂ) ≠ 0 := by
  show xi ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0
  apply xi_ne_zero_of_im_sq_le
  simpa using sq_le_thirtyTwo_of_mem_Icc_pi_div_log_two ht

/-- **Approximation defect.**  For any normalizer `e` and any target `F`, some point of
`[0, π/log 2]` carries the full target as error: `‖e t · Z(t) − F t‖ = ‖F t‖`. -/
theorem exists_gammaChain_error_eq {c : ℕ → ℝ} (hc : ∀ k, |c k| ≤ 1) (N : ℕ) (e F : ℝ → ℂ) :
    ∃ t ∈ Icc 0 (Real.pi / Real.log 2),
      ‖e t * chainZ c (lineField gammaFreq t) N - F t‖ = ‖F t‖ := by
  obtain ⟨t, ht, hz⟩ := exists_gammaChainZ_eq_zero hc N
  exact ⟨t, ht, by rw [hz, mul_zero, zero_sub, norm_neg]⟩

theorem continuous_XiC_real : Continuous fun t : ℝ => XiC (t : ℂ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (XiC_analytic (x : ℂ) (Set.mem_univ _)).continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- **The Γ-site route cannot reach Ξ.**  For every continuous zero-free `E` on `[0, π/log 2]`,
no family of normalized Γ-site Lee–Yang chains with fugacities in `[−1, 1]` converges to
`E · Ξ` uniformly on `[0, π/log 2]`, whatever the normalizers and the chain lengths. -/
theorem not_tendstoUniformlyOn_gammaChain_XiC {ι : Type*} {l : Filter ι} [l.NeBot]
    (N : ι → ℕ) (c : ι → ℕ → ℝ) (hc : ∀ i k, |c i k| ≤ 1) (e : ι → ℝ → ℂ) {E : ℝ → ℂ}
    (hE : ContinuousOn E (Icc 0 (Real.pi / Real.log 2)))
    (hE0 : ∀ t ∈ Icc 0 (Real.pi / Real.log 2), E t ≠ 0) :
    ¬ TendstoUniformlyOn (fun i t => e i t * chainZ (c i) (lineField gammaFreq t) (N i))
      (fun t => E t * XiC (t : ℂ)) l (Icc 0 (Real.pi / Real.log 2)) := by
  intro hU
  have hlogpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hne : (Icc 0 (Real.pi / Real.log 2)).Nonempty :=
    ⟨0, left_mem_Icc.mpr (div_nonneg Real.pi_pos.le hlogpos.le)⟩
  have hcont : ContinuousOn (fun t => ‖E t * XiC (t : ℂ)‖) (Icc 0 (Real.pi / Real.log 2)) :=
    (hE.mul continuous_XiC_real.continuousOn).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  have hm : 0 < ‖E t₀ * XiC (t₀ : ℂ)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (hE0 t₀ ht₀) (XiC_ne_zero_of_mem_Icc_pi_div_log_two ht₀))
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hU _ hm).exists
  obtain ⟨t, ht, hz⟩ := exists_gammaChainZ_eq_zero (hc i) (N i)
  have hlt := hi t ht
  simp only [hz, mul_zero, dist_zero_right] at hlt
  exact absurd (isMinOn_iff.mp hmin t ht) (not_le.mpr hlt)

end

end RHTower.LeeYangChain
