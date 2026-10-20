import GaloisForLFunctions.RHTower.ZetaPartialSumIsolatedZeroHeightsAndUniformPairReturns

/-!
# Besicovitch almost periodicity of zeta on lines of the strip

For `1/2 < σ < 1` the function `t ↦ ζ(σ + it)` is almost periodic in the mean square: for every
`ε > 0` there are `M` and `θ > 0` such that every simultaneous `θ`-almost period `d` of the phases
`n^{-id}`, `n ≤ M` (`headPhaseReturnSet M θ`), satisfies

  `(1/T) ∫₀ᵀ |ζ(σ + i(d + t)) − ζ(σ + it)|² dt < ε`  for all large `T`

(`exists_besicovitch_almostPeriods_zeta_line`).  These almost periods are relatively dense and of
positive lower density (`zeta_line_besicovitch_almostPeriodic`).  Write `ζ = head_M + tail_M`:
along `d` the head moves by at most `M θ` on the line, and both shifted and unshifted tails have
Carlson mean square `Σ_{n > M} n^{-2σ}` (`carlson_zeta_tail_shifted_meanSquare`,
`carlson_zeta_tail_meanSquare`), which is small for large `M`.

Together with the Bohr–Fourier coefficients and Parseval (`ZetaStripBohrFourierCoefficients`,
`carlson_zeta_meanSquare`) this is the Bohr–Jessen mean-value substrate of the self-return analysis:
the Besicovitch almost periods of `ζ` on a line are the Kronecker almost periods of its finite
heads.  The obstruction to *uniform* (Bohr) almost periodicity at a fixed base disc is the subject of
the head-zero and zero-transport laws.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem norm_sq_add_sub_le_three (a b c : ℂ) :
    ‖a + b - c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h0 := norm_nonneg (a + b - c)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c, mul_le_mul h1 h1 h0 (by positivity)]

/-- `t ↦ ζ(σ + it)` is continuous for `σ ≠ 1`. -/
theorem continuous_riemannZeta_vertical_line {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
  have h : (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) =
      fun t => zetaDirichletTail 0 σ t + zetaDirichletHead 0 σ t := by
    funext t
    unfold zetaDirichletTail
    ring
  rw [h]
  exact (continuous_zetaDirichletTail 0 hσ).add (continuous_zetaDirichletHead 0 σ)

/-- **Besicovitch almost periods of `ζ` on a line of the strip.**  For `1/2 < σ < 1` and `ε > 0`
there are `M` and `θ > 0` such that every `d ∈ headPhaseReturnSet M θ` is an `ε`-almost period of
`t ↦ ζ(σ + it)` in the mean square. -/
theorem exists_besicovitch_almostPeriods_zeta_line {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∃ θ > 0, ∀ d ∈ headPhaseReturnSet M θ, ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T < ε := by
  obtain ⟨M, hM⟩ := ((tendsto_zetaCoefficientTailMass hσ).eventually
    (gt_mem_nhds (show 0 < ε / 18 by positivity))).exists
  set θ : ℝ := Real.sqrt (ε / 9) / (M + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  refine ⟨M, θ, hθ0, fun d hd => ?_⟩
  have hhead : ∀ t : ℝ, ‖zetaDirichletHead M σ (d + t) - zetaDirichletHead M σ t‖ ≤ M * θ := by
    intro t
    have h := norm_edPoly_one_Icc_shift_sub_le hd (w := (σ : ℂ) + (t : ℂ) * I)
      (by simp; linarith)
    have e : zetaDirichletHead M σ (d + t) =
        edPoly (fun _ => 1) (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I + d * I) := by
      unfold zetaDirichletHead
      congr 1
      push_cast
      ring
    rw [e]
    exact h
  have hMθ : (M : ℝ) * θ ≤ Real.sqrt (ε / 9) := by
    rw [hθ, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (ε / 9)]
  have hMθsq : 3 * ((M : ℝ) * θ) ^ 2 ≤ ε / 3 := by
    have := pow_le_pow_left₀ (by positivity) hMθ 2
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  have hc1 := carlson_zeta_tail_shifted_meanSquare M hσ hσ1 d
  have hc2 := carlson_zeta_tail_meanSquare M hσ hσ1
  filter_upwards [hc1.eventually (gt_mem_nhds hM), hc2.eventually (gt_mem_nhds hM),
    eventually_gt_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hpt : ∀ t ∈ Icc (0 : ℝ) T,
      ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) - riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        3 * (((M : ℝ) * θ) ^ 2 + ‖zetaDirichletTail M σ (d + t)‖ ^ 2 +
          ‖zetaDirichletTail M σ t‖ ^ 2) := by
    intro t _
    have hdec : riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) =
        (zetaDirichletHead M σ (d + t) - zetaDirichletHead M σ t) +
          zetaDirichletTail M σ (d + t) - zetaDirichletTail M σ t := by
      unfold zetaDirichletTail
      ring
    rw [hdec]
    refine (norm_sq_add_sub_le_three _ _ _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) (hhead t) 2
    linarith
  have hcζ : Continuous fun t : ℝ =>
      ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) - riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    have h1 : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) :=
      (continuous_riemannZeta_vertical_line hσ1.ne).comp (continuous_const.add continuous_id)
    exact ((h1.sub (continuous_riemannZeta_vertical_line hσ1.ne)).norm).pow 2
  have hcb : Continuous fun t : ℝ => 3 * (((M : ℝ) * θ) ^ 2 +
      ‖zetaDirichletTail M σ (d + t)‖ ^ 2 + ‖zetaDirichletTail M σ t‖ ^ 2) := by
    have h1 : Continuous fun t : ℝ => ‖zetaDirichletTail M σ (d + t)‖ ^ 2 :=
      (((continuous_zetaDirichletTail M hσ1.ne).comp (continuous_const.add continuous_id)).norm).pow 2
    have h2 : Continuous fun t : ℝ => ‖zetaDirichletTail M σ t‖ ^ 2 :=
      ((continuous_zetaDirichletTail M hσ1.ne).norm).pow 2
    exact continuous_const.mul ((continuous_const.add h1).add h2)
  have hint : (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) -
      riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, 3 * (((M : ℝ) * θ) ^ 2 + ‖zetaDirichletTail M σ (d + t)‖ ^ 2 +
        ‖zetaDirichletTail M σ t‖ ^ 2) :=
    intervalIntegral.integral_mono_on hT0.le (hcζ.intervalIntegrable _ _)
      (hcb.intervalIntegrable _ _) hpt
  have h1i : IntervalIntegrable (fun t : ℝ => ‖zetaDirichletTail M σ (d + t)‖ ^ 2) volume 0 T :=
    ((((continuous_zetaDirichletTail M hσ1.ne).comp
      (continuous_const.add continuous_id)).norm).pow 2).intervalIntegrable _ _
  have h2i : IntervalIntegrable (fun t : ℝ => ‖zetaDirichletTail M σ t‖ ^ 2) volume 0 T :=
    (((continuous_zetaDirichletTail M hσ1.ne).norm).pow 2).intervalIntegrable _ _
  have hci : IntervalIntegrable (fun _ : ℝ => ((M : ℝ) * θ) ^ 2) volume 0 T :=
    continuous_const.intervalIntegrable _ _
  have hsplit : (∫ t in (0 : ℝ)..T, 3 * (((M : ℝ) * θ) ^ 2 +
      ‖zetaDirichletTail M σ (d + t)‖ ^ 2 + ‖zetaDirichletTail M σ t‖ ^ 2)) =
      3 * ((T - 0) * ((M : ℝ) * θ) ^ 2 +
        (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ (d + t)‖ ^ 2) +
          ∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hci.add h1i) h2i,
      intervalIntegral.integral_add hci h1i, intervalIntegral.integral_const, smul_eq_mul]
  rw [div_lt_iff₀ hT0]
  rw [div_lt_iff₀ hT0] at hT1 hT2
  have hε1 : 3 * ((M : ℝ) * θ) ^ 2 * T ≤ ε / 3 * T := mul_le_mul_of_nonneg_right hMθsq hT0.le
  calc (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ 3 * ((T - 0) * ((M : ℝ) * θ) ^ 2 +
          (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ (d + t)‖ ^ 2) +
            ∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) := hsplit ▸ hint
    _ < ε * T := by nlinarith

/-- **`ζ` is Besicovitch almost periodic on every line of the strip.**  For `1/2 < σ < 1` and
`ε > 0` there is a relatively dense set `E` of positive lower density such that every `d ∈ E` is an
`ε`-almost period of `t ↦ ζ(σ + it)` in the mean square. -/
theorem zeta_line_besicovitch_almostPeriodic {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ E : Set ℝ, (∃ L > 0, ∀ a : ℝ, ∃ d ∈ Icc a (a + L), d ∈ E) ∧
      (∃ κ > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (κ * T) ≤ volume (E ∩ Icc 0 T)) ∧
      ∀ d ∈ E, ∀ᶠ T : ℝ in atTop,
        (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + ((d + t : ℝ) : ℂ) * I) -
          riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T < ε := by
  obtain ⟨M, θ, hθ, hd⟩ := exists_besicovitch_almostPeriods_zeta_line hσ hσ1 hε
  exact ⟨headPhaseReturnSet M θ, exists_relDense_headPhaseReturnSet M hθ,
    exists_pos_density_headPhaseReturnSet M hθ, hd⟩

end RHTower
