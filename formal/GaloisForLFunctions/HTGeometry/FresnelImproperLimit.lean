import GaloisForLFunctions.HTGeometry.FresnelTailBound

/-!
# The improper Fresnel integral converges

The oscillatory half-power integrand is interval integrable on every bounded interval — its modulus
is `|u|^{-1/2}`, integrable at the origin — and the tail bound `2 a^{-1/2}` makes the truncated
integrals Cauchy at infinity.  Hence the improper integral

`lim_{R → ∞} ∫₀^R u^{-1/2} e^{iu} du`

exists.  This is the analytic half of the half-log scattering constant.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem intervalIntegrable_fresnelKernel (a b : ℝ) :
    IntervalIntegrable fresnelKernel volume a b := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmeas : AEStronglyMeasurable fresnelKernel (volume.restrict (Set.uIoc a b)) := by
    apply Measurable.aestronglyMeasurable
    unfold fresnelKernel
    fun_prop
  refine IntervalIntegrable.mono_fun hbase hmeas ?_
  filter_upwards with u
  have hval : ‖fresnelKernel u‖ = |u ^ (-(1:ℝ)/2)| := by
    rw [fresnelKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  rw [hval, Real.norm_eq_abs]

/-- The truncated Fresnel integrals. -/
def fresnelTruncated (R : ℝ) : ℂ := ∫ u in (0:ℝ)..R, fresnelKernel u

theorem fresnelTruncated_sub (a b : ℝ) :
    fresnelTruncated b - fresnelTruncated a = ∫ u in a..b, fresnelKernel u := by
  rw [fresnelTruncated, fresnelTruncated,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fresnelKernel 0 a) (intervalIntegrable_fresnelKernel a b)]
  ring

/-- **The improper Fresnel integral converges.** -/
theorem exists_tendsto_fresnelTruncated :
    ∃ S : ℂ, Tendsto fresnelTruncated atTop (𝓝 S) := by
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, 0 < N ∧
      ∀ a b : ℝ, N ≤ a → a ≤ b → ‖fresnelTruncated b - fresnelTruncated a‖ < ε := by
    intro ε hε
    refine ⟨max 1 (16 / ε ^ 2), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    intro a b hNa hab
    have ha1 : (1:ℝ) ≤ a := le_trans (le_max_left _ _) hNa
    have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
    have hbound := norm_integral_fresnelKernel_le ha0 hab
    rw [fresnelTruncated_sub a b]
    have hkey : 2 * a ^ (-(1:ℝ)/2) < ε := by
      have haε : 16 / ε ^ 2 ≤ a := le_trans (le_max_right _ _) hNa
      have hsqrt : a ^ (-(1:ℝ)/2) = 1 / Real.sqrt a := by
        have hhalf : a ^ ((1:ℝ)/2) = Real.sqrt a := (Real.sqrt_eq_rpow a).symm
        rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring, Real.rpow_neg ha0.le, hhalf, one_div]
      rw [hsqrt]
      have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
      rw [mul_one_div, div_lt_iff₀ hsa]
      have hsq : (4 / ε) ^ 2 ≤ a := by
        rw [div_pow]
        calc (4:ℝ) ^ 2 / ε ^ 2 = 16 / ε ^ 2 := by norm_num
          _ ≤ a := haε
      have h4 : 4 / ε ≤ Real.sqrt a := by
        have hnn : (0:ℝ) ≤ 4 / ε := by positivity
        nlinarith [Real.sq_sqrt ha0.le, Real.sqrt_nonneg a, hsq, hnn]
      rw [div_le_iff₀ hε] at h4
      nlinarith [h4, hε, hsa]
    linarith [hbound, hkey]
  have hseq : CauchySeq (fun n : ℕ => fresnelTruncated ((n : ℝ) + 1)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN0, hN⟩ := hcauchy ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge N
    refine ⟨M, fun n hn => ?_⟩
    have hMn : (M : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hNM : N ≤ (M : ℝ) + 1 := by linarith
    rw [dist_eq_norm]
    exact hN _ _ hNM hMn
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hseq
  refine ⟨S, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN0, hN⟩ := hcauchy (ε / 2) (by linarith)
  have hSlim := Metric.tendsto_atTop.mp hS (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := hSlim
  obtain ⟨K, hK⟩ := exists_nat_ge (max N ((M : ℝ) + 1))
  have hKN : N ≤ (K : ℝ) := le_trans (le_max_left _ _) hK
  have hKM : ((M : ℝ) + 1) ≤ (K : ℝ) := le_trans (le_max_right _ _) hK
  refine ⟨max N ((K : ℝ) + 1), fun R hR => ?_⟩
  have hNR : N ≤ R := le_trans (le_max_left _ _) hR
  have hKR : (K : ℝ) + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hMK : M ≤ K := by
    have : (M : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast this
  have hstep₁ : dist (fresnelTruncated ((K : ℝ) + 1)) S < ε / 2 := hM K hMK
  have hNK : N ≤ (K : ℝ) + 1 := by linarith
  have hstep₂ : ‖fresnelTruncated R - fresnelTruncated ((K : ℝ) + 1)‖ < ε / 2 :=
    hN _ _ hNK hKR
  have hdist : dist (fresnelTruncated R) S
      ≤ dist (fresnelTruncated R) (fresnelTruncated ((K : ℝ) + 1))
        + dist (fresnelTruncated ((K : ℝ) + 1)) S := dist_triangle _ _ _
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hdist
  rw [dist_eq_norm] at hstep₁
  rw [dist_eq_norm]
  linarith [hdist, hstep₁, hstep₂]

end

end GaloisForLFunctions.HTGeometry
