/-
# Zero density at the mean-spacing scale from the mollified first moment

The strengthened ceiling `exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare`
bounds `∑ m_ρ (Re ρ − 1/2) + (1/2 − σ₀) ∑ m_ρ` over the zeros of `ζ` with `Re ρ ≥ 1/2` in the
window. Every zero with `Re ρ ≥ 1/2 + Δ` contributes at least `Δ` to the first moment, so the
multiplicity-weighted count `N_Δ` of such zeros satisfies

  `2π [Δ · N_Δ + (1/2 − σ₀) · N_{≥1/2}] ≤ ½(T₂−T₁) log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`.

On the Levinson line `σ₀ = 1/2 − R/log T` with `Δ = a/log T`, this is the explicit density
`p_T(a) := N(1/2 + a/log T, T)/N(T) ≤ [log c(R,θ) − (1+κ)R]/(2a)` (polynomial decay in `a`;
the exponential decay `e^{−2θa}` needs the sharp-head mollifier on the right-shifted line).

The second lemma quantifies why second-moment (Jensen) bounds cannot reach `p_T(a) → 0`: for a
complex Gaussian deviation of variance `σ²` the true log-mean is `E₁(1/σ²) ≤ σ² e^{−1/σ²}`, while
Jensen charges `log(1 + σ²)`; the loss `e^{−1/σ²}` is exactly the small-value probability that a
mean-square method cannot see.
-/
import GaloisForLFunctions.RHTower.ZetaOffLineFirstMomentLineCount
import GaloisForLFunctions.RHTower.ComplexGaussianLogMeanExponentialIntegral

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **Zero density at scale `Δ` from the mollified first moment.** -/
theorem exists_zetaZeroDensity_scale_le_of_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
      ∀ Δ : ℝ, 0 ≤ Δ →
        2 * Real.pi *
            (Δ * (∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re),
                ((analyticOrderAt riemannZeta w).toNat : ℝ))
              + (1 / 2 - σ₀) * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq Z hZ
    Δ hΔ
  have h := hmain b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2
    hMsq Z hZ
  -- the first moment dominates `Δ` times the count beyond `1/2 + Δ`
  have hcount : Δ * (∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ))
      ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    rw [Finset.mul_sum]
    calc ∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re), Δ * ((analyticOrderAt riemannZeta w).toNat : ℝ)
        ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
          apply Finset.sum_le_sum
          intro w hw
          rw [Finset.mem_filter] at hw
          have : Δ ≤ w.re - 1 / 2 := by linarith [hw.2]
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro w hw _
          have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
          rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
          exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi *
        (Δ * (∑ w ∈ Z.filter (fun w => 1 / 2 + Δ ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ))
          + (1 / 2 - σ₀) * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ))
      ≤ 2 * Real.pi *
        ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          + (1 / 2 - σ₀) * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hpi
        linarith [hcount]
    _ ≤ _ := h

/-- **The Jensen loss.**  `E₁(x) ≤ e^{−x}/x` for `x > 0`: the Gaussian log-mean `E₁(1/σ²)` is
exponentially smaller than the Jensen bound `log(1+σ²) ≈ σ²`. -/
theorem expIntegralE1_le_exp_neg_div {x : ℝ} (hx : 0 < x) :
    expIntegralE1 x ≤ Real.exp (-x) / x := by
  unfold expIntegralE1
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi x) := integrableOn_exp_neg_Ioi x
  have hmaj : IntegrableOn (fun u : ℝ => Real.exp (-u) * x⁻¹) (Set.Ioi x) :=
    Integrable.mul_const h1 x⁻¹
  have hpt : ∀ u ∈ Set.Ioi x, Real.exp (-u) / u ≤ Real.exp (-u) * x⁻¹ := by
    intro u hu
    have hu' : x < u := hu
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx hu'.le
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioi x) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (ContinuousOn.div (Real.continuous_exp.comp continuous_neg).continuousOn
        continuousOn_id (fun u hu => ne_of_gt (lt_trans hx hu))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : x < u := hu
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
      exact hpt u hu
  calc ∫ u in Set.Ioi x, Real.exp (-u) / u
      ≤ ∫ u in Set.Ioi x, Real.exp (-u) * x⁻¹ :=
        MeasureTheory.setIntegral_mono_on hint hmaj measurableSet_Ioi hpt
    _ = (∫ u in Set.Ioi x, Real.exp (-u)) * x⁻¹ := MeasureTheory.integral_mul_const _ _
    _ = Real.exp (-x) / x := by rw [integral_exp_neg_Ioi, div_eq_mul_inv]

end

end RHTower
