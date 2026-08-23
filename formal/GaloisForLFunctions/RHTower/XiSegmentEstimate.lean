import GaloisForLFunctions.RHTower.XiZeroBandFinite
import GaloisForLFunctions.RHTower.XiHorizontalLog
import GaloisForLFunctions.HTGeometry.PoissonKernelSegmentIntegral

/-!
# The movement of `log‖xi‖` across a horizontal segment

Integrating the symmetrised partial fraction of `logDeriv xi` across `σ ≤ u ≤ 2` at a fixed height
`T` bounds the movement of `log‖xi‖` zero by zero: each divisor copy contributes at most
`log(1 + 9/(T−γ)²) + log(1 + 9/(T+γ)²)`, the segment integral of the Poisson kernel.  The
contribution is `O(1/(T−γ)²)` for a far zero and only logarithmic in the distance for a near one, so
the whole sum is finite — and its size at a *well chosen* height is what Proposition 5.1 needs.

## Main results

* `integral_abs_poissonShift_le` — the one-zero bound
* `summable_xiSegmentBound`
* `abs_integral_re_logDeriv_xi_le`
-/

open Complex Set MeasureTheory intervalIntegral Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The one-zero bound -/

theorem integral_abs_poissonShift_le {c β : ℝ} (hc : c ≠ 0) {σ : ℝ} (h1 : -1 ≤ σ) (h2 : σ ≤ 2)
    (hβ0 : -1 ≤ β) (hβ1 : β ≤ 1) :
    (∫ u in σ..2, |(u - β) / ((u - β) ^ 2 + c ^ 2)|) ≤ Real.log (1 + 9 / c ^ 2) := by
  have hshift : (∫ u in σ..2, |(u - β) / ((u - β) ^ 2 + c ^ 2)|)
      = ∫ v in (σ - β)..(2 - β), |v| / (v ^ 2 + c ^ 2) := by
    have := intervalIntegral.integral_comp_sub_right
      (a := σ) (b := 2) (fun v : ℝ => |v| / (v ^ 2 + c ^ 2)) β
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [abs_div, abs_of_pos (poissonDenom_pos hc (u - β))]
  rw [hshift]
  exact integral_poissonKernelAbs_le hc (by linarith) (by linarith) (by linarith)

/-! ## The two resolvent families along the segment -/

theorem re_inv_first (T u : ℝ) (ρ : ℂ) :
    ((((u : ℂ) + (T : ℂ) * I) - ρ)⁻¹).re
      = (u - ρ.re) / ((u - ρ.re) ^ 2 + (T - ρ.im) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  have h1 : (((u : ℂ) + (T : ℂ) * I) - ρ).re = u - ρ.re := by simp
  have h2 : (((u : ℂ) + (T : ℂ) * I) - ρ).im = T - ρ.im := by simp
  rw [h1, h2]
  ring_nf

theorem re_inv_second (T u : ℝ) (ρ : ℂ) :
    ((((u : ℂ) + (T : ℂ) * I) - 1 + ρ)⁻¹).re
      = (u - (1 - ρ.re)) / ((u - (1 - ρ.re)) ^ 2 + (T + ρ.im) ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  have h1 : (((u : ℂ) + (T : ℂ) * I) - 1 + ρ).re = u - (1 - ρ.re) := by simp; ring
  have h2 : (((u : ℂ) + (T : ℂ) * I) - 1 + ρ).im = T + ρ.im := by simp
  rw [h1, h2]
  ring_nf

theorem continuous_re_pairTerm {T : ℝ} {q : XiZeroCopy}
    (h1 : T - (q.1 : ℂ).im ≠ 0) (h2 : T + (q.1 : ℂ).im ≠ 0) :
    Continuous fun u : ℝ =>
      ((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
        + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re := by
  have hfun : (fun u : ℝ =>
      ((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
        + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re)
      = fun u : ℝ =>
        (u - (q.1 : ℂ).re) / ((u - (q.1 : ℂ).re) ^ 2 + (T - (q.1 : ℂ).im) ^ 2)
          + (u - (1 - (q.1 : ℂ).re))
            / ((u - (1 - (q.1 : ℂ).re)) ^ 2 + (T + (q.1 : ℂ).im) ^ 2) := by
    funext u
    rw [Complex.add_re, re_inv_first, re_inv_second]
  rw [hfun]
  refine Continuous.add ?_ ?_
  · refine Continuous.div (by fun_prop) (by fun_prop) fun u => (poissonDenom_pos h1 _).ne'
  · refine Continuous.div (by fun_prop) (by fun_prop) fun u => (poissonDenom_pos h2 _).ne'

/-- **The one-zero segment bound.** -/
theorem integral_abs_re_pairTerm_le {T : ℝ} {q : XiZeroCopy}
    (h1 : T - (q.1 : ℂ).im ≠ 0) (h2 : T + (q.1 : ℂ).im ≠ 0)
    {σ : ℝ} (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ u in σ..2, ‖((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
        + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re‖)
      ≤ Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)
        + Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2) := by
  obtain ⟨hb0, hb1⟩ := xi_divisor_support_re_mem_open_unit q.1
  set β : ℝ := (q.1 : ℂ).re with hβ
  set γ : ℝ := (q.1 : ℂ).im with hγ
  have hcont1 : Continuous fun u : ℝ => |(u - β) / ((u - β) ^ 2 + (T - γ) ^ 2)| := by
    refine continuous_abs.comp (Continuous.div (by fun_prop) (by fun_prop) ?_)
    exact fun u => (poissonDenom_pos h1 (u - β)).ne'
  have hcont2 : Continuous fun u : ℝ =>
      |(u - (1 - β)) / ((u - (1 - β)) ^ 2 + (T + γ) ^ 2)| := by
    refine continuous_abs.comp (Continuous.div (by fun_prop) (by fun_prop) ?_)
    exact fun u => (poissonDenom_pos h2 (u - (1 - β))).ne'
  have hsplit : (∫ u in σ..2, ‖((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
        + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re‖)
      ≤ (∫ u in σ..2, |(u - β) / ((u - β) ^ 2 + (T - γ) ^ 2)|)
        + ∫ u in σ..2, |(u - (1 - β)) / ((u - (1 - β)) ^ 2 + (T + γ) ^ 2)| := by
    rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on hσ2 ?_ ?_ ?_
    · refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_norm.comp (continuous_re_pairTerm h1 h2)
    · exact (hcont1.add hcont2).intervalIntegrable _ _
    · intro u _
      rw [Complex.add_re, re_inv_first, re_inv_second, Real.norm_eq_abs]
      exact abs_add_le _ _
  refine hsplit.trans (add_le_add ?_ ?_)
  · exact integral_abs_poissonShift_le h1 hσ1 hσ2 (by linarith) (by linarith)
  · exact integral_abs_poissonShift_le h2 hσ1 hσ2 (by linarith) (by linarith)

/-! ## Summability of the bound family -/

theorem log_kernel_nonneg (x c : ℝ) : 0 ≤ Real.log (1 + 9 / (x - c) ^ 2) := by
  refine Real.log_nonneg ?_
  have : (0 : ℝ) ≤ 9 / (x - c) ^ 2 := by positivity
  linarith

theorem summable_logKernel (x : ℝ) :
    Summable (fun q : XiZeroCopy => Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2)) := by
  classical
  have hfin := finite_xiZeroCopy_band x (by norm_num : (0 : ℝ) ≤ 1)
  set S : Finset XiZeroCopy := hfin.toFinset with hS
  set b : XiZeroCopy → ℝ := fun q =>
    if q ∈ S then Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2) else 0 with hb
  set c : XiZeroCopy → ℝ := fun q => 18 * ((1 : ℝ) / (1 + (x - (q.1 : ℂ).im) ^ 2)) with hc
  have hbs : Summable b := by
    refine summable_of_ne_finset_zero (s := S) fun q hq => ?_
    rw [hb]
    simp [hq]
  have hcs : Summable c := (summable_xiZeroWeight x).mul_left 18
  refine Summable.of_nonneg_of_le (fun q => log_kernel_nonneg x _) (fun q => ?_) (hbs.add hcs)
  by_cases hq : q ∈ S
  · have hbq : b q = Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2) := by
      rw [hb]; simp [hq]
    have hcq : 0 ≤ c q := by
      show (0:ℝ) ≤ 18 * ((1:ℝ) / (1 + (x - (q.1 : ℂ).im) ^ 2))
      positivity
    show Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2) ≤ b q + c q
    linarith
  · have hbq : b q = 0 := by rw [hb]; simp [hq]
    have hfar : (1 : ℝ) < (x - (q.1 : ℂ).im) ^ 2 := by
      have hnot : ¬ (|(q.1 : ℂ).im - x| ≤ 1) := by
        intro hle
        exact hq (by rw [hS, Set.Finite.mem_toFinset]; exact hle)
      have habs : 1 < |(q.1 : ℂ).im - x| := lt_of_not_ge hnot
      have hsq : ((q.1 : ℂ).im - x) ^ 2 = (x - (q.1 : ℂ).im) ^ 2 := by ring
      nlinarith [abs_nonneg ((q.1 : ℂ).im - x), sq_abs ((q.1 : ℂ).im - x)]
    have hlog : Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2) ≤ 9 / (x - (q.1 : ℂ).im) ^ 2 := by
      have hpos : (0 : ℝ) < 1 + 9 / (x - (q.1 : ℂ).im) ^ 2 := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have hA : (0 : ℝ) < (x - (q.1 : ℂ).im) ^ 2 := by linarith
    have hd : (0 : ℝ) < 1 + (x - (q.1 : ℂ).im) ^ 2 := by linarith
    have hcq : c q = 18 / (1 + (x - (q.1 : ℂ).im) ^ 2) := by
      show (18 : ℝ) * ((1 : ℝ) / (1 + (x - (q.1 : ℂ).im) ^ 2))
          = 18 / (1 + (x - (q.1 : ℂ).im) ^ 2)
      ring
    have hcmp : 9 / (x - (q.1 : ℂ).im) ^ 2 ≤ c q := by
      rw [hcq, div_le_div_iff₀ hA hd]
      nlinarith
    show Real.log (1 + 9 / (x - (q.1 : ℂ).im) ^ 2) ≤ b q + c q
    linarith

theorem summable_xiSegmentBound (T : ℝ) :
    Summable (fun q : XiZeroCopy => Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)
      + Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)) := by
  refine (summable_logKernel T).add ?_
  refine ((summable_logKernel (-T)).congr fun q => ?_)
  congr 2
  ring

/-! ## The segment estimate -/

/-- **The segment estimate.**  The movement of `Re ∫ logDeriv xi` across a horizontal segment of the
strip is bounded by the sum of the one-zero contributions. -/
theorem abs_two_mul_integral_re_logDeriv_xi_le {T : ℝ}
    (hne : ∀ u : ℝ, xi ((u : ℂ) + (T : ℂ) * I) ≠ 0)
    (h1 : ∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0)
    (h2 : ∀ q : XiZeroCopy, T + (q.1 : ℂ).im ≠ 0)
    {σ : ℝ} (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2) :
    |2 * (∫ u in σ..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re|
      ≤ ∑' q : XiZeroCopy, (Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)
          + Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)) := by
  classical
  set P : XiZeroCopy → ℝ → ℝ := fun q u =>
    ((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
      + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹).re with hP
  set bnd : XiZeroCopy → ℝ := fun q => Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)
      + Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2) with hbnd
  have hcontP : ∀ q, Continuous (P q) := fun q => continuous_re_pairTerm (h1 q) (h2 q)
  have hint : ∀ q, Integrable (P q) (volume.restrict (Ioc σ 2)) := by
    intro q
    exact (hcontP q).integrableOn_Ioc
  have hnormle : ∀ q, (∫ u in Ioc σ 2, ‖P q u‖) ≤ bnd q := by
    intro q
    have hIoc : (∫ u in Ioc σ 2, ‖P q u‖) = ∫ u in σ..2, ‖P q u‖ :=
      (intervalIntegral.integral_of_le hσ2).symm
    rw [hIoc]
    exact integral_abs_re_pairTerm_le (h1 q) (h2 q) hσ1 hσ2
  have hnn : ∀ q, 0 ≤ ∫ u in Ioc σ 2, ‖P q u‖ := by
    intro q
    exact integral_nonneg fun u => norm_nonneg _
  have hsumnorm : Summable (fun q => ∫ u in Ioc σ 2, ‖P q u‖) :=
    Summable.of_nonneg_of_le hnn hnormle (summable_xiSegmentBound T)
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumnorm
  have hpoint : ∀ u : ℝ, (∑' q : XiZeroCopy, P q u)
      = 2 * (logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re := by
    intro u
    have hxi := hne u
    have hs := summable_xiPairTerm hxi
    have := two_logDeriv_xi_eq_pair_tsum hxi
    have hre : (2 * logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re
        = (∑' q : XiZeroCopy,
            ((((u : ℂ) + (T : ℂ) * I) - (q.1 : ℂ))⁻¹
              + (((u : ℂ) + (T : ℂ) * I) - 1 + (q.1 : ℂ))⁻¹)).re := by
      rw [this]
    rw [Complex.re_tsum hs] at hre
    rw [hP]
    rw [← hre]
    simp
  have hInt : Integrable (fun u : ℝ => logDeriv xi ((u : ℂ) + (T : ℂ) * I))
      (volume.restrict (Ioc σ 2)) := (continuous_logDeriv_xi_horizontal hne).integrableOn_Ioc
  have hfinal : (∑' q : XiZeroCopy, ∫ u in Ioc σ 2, P q u)
      = 2 * (∫ u in σ..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re := by
    rw [hswap]
    have hcongr : (∫ u in Ioc σ 2, ∑' q : XiZeroCopy, P q u)
        = ∫ u in Ioc σ 2, 2 * (logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => hpoint u
    rw [hcongr, MeasureTheory.integral_const_mul]
    congr 1
    have hcomm := ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt
    rw [intervalIntegral.integral_of_le hσ2]
    exact hcomm
  rw [← hfinal, ← Real.norm_eq_abs]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hsumnorm
    exact norm_integral_le_integral_norm _
  · have hsum2 : Summable (fun q : XiZeroCopy => ‖∫ u in Ioc σ 2, P q u‖) := by
      refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hsumnorm
      exact norm_integral_le_integral_norm _
    exact hsum2.tsum_le_tsum
      (fun q => le_trans (norm_integral_le_integral_norm _) (hnormle q))
      (summable_xiSegmentBound T)

end

end RHTower
