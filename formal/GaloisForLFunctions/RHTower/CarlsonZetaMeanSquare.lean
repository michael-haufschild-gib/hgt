import GaloisForLFunctions.RHTower.ZetaSuperlinearCutoff
import GaloisForLFunctions.RHTower.ZetaDirichletBandMeanSquare
import GaloisForLFunctions.RHTower.IntervalMeanSquareTransfer

/-!
# Carlson mean squares for zeta in the Bagchi strip

For `1/2 < σ < 1`, the actual zeta function minus any fixed unsmoothed
Dirichlet head has mean square equal to the square coefficient tail. All
truncation and finite-polynomial estimates are supplied unconditionally.
This unconditioned mean does not assert the centered-tail estimate on
finite-head return sets required by Bagchi self-recurrence.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

def zetaDirichletTail (M : ℕ) (σ t : ℝ) : ℂ :=
  riemannZeta ((σ : ℂ) + (t : ℂ) * I) - zetaDirichletHead M σ t

private theorem continuous_carlson_zeta_line {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := fun h => hσ (by simpa using congrArg Complex.re h)
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) (by fun_prop)

theorem continuous_zetaDirichletTail (M : ℕ) {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (zetaDirichletTail M σ) :=
  (continuous_carlson_zeta_line hσ).sub (continuous_zetaDirichletHead M σ)

theorem tendsto_zetaDirichletBand_mean_of_cutoff (M : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {N : ℝ → ℕ} (hN : Tendsto N atTop atTop)
    (hrate : Tendsto (fun T : ℝ => (N T : ℝ) ^ (2 - 2 * σ) / T) atTop (𝓝 0)) :
    Tendsto (fun T => dyadicSquareMean (zetaDirichletBand M (N T) σ) T)
      atTop (𝓝 (zetaCoefficientTailMass M σ)) := by
  have hone : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hbound : Tendsto (fun T : ℝ =>
      208 * (((N T : ℝ) ^ (2 - 2 * σ) / T) / (2 - 2 * σ) + 1 / T)) atTop (𝓝 0) := by
    simpa using ((hrate.div_const (2 - 2 * σ)).add hone).const_mul 208
  have herr : Tendsto (fun T => dyadicSquareMean (zetaDirichletBand M (N T) σ) T -
      zetaBandDiagonal M (N T) σ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hbound
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have h := zetaDirichletBand_meanSquare_error_subcritical M (N T) hσ hσ1 T (2 * T)
    rw [show 2 * T - T = T by ring] at h
    have heq : dyadicSquareMean (zetaDirichletBand M (N T) σ) T - zetaBandDiagonal M (N T) σ =
        ((∫ t in T..2 * T, ‖zetaDirichletBand M (N T) σ t‖ ^ 2) -
          T * zetaBandDiagonal M (N T) σ) / T := by
      unfold dyadicSquareMean
      field_simp
    rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hT0]
    exact (div_le_div_of_nonneg_right h hT0.le).trans_eq (by ring)
  have hdiag := (tendsto_zetaBandDiagonal M hσ).comp hN
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using herr.add hdiag

/-- The actual zeta tail has the exact Carlson mean on every dyadic height window. -/
theorem carlson_zeta_tail_dyadicMeanSquare (M : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (dyadicSquareMean (zetaDirichletTail M σ))
      atTop (𝓝 (zetaCoefficientTailMass M σ)) := by
  let a := σ + 1 / 2
  let N : ℝ → ℕ := superlinearCutoff a
  have ha : 0 < a := by dsimp [a]; linarith
  have hN : Tendsto N atTop atTop := tendsto_superlinearCutoff ha
  obtain ⟨m, he, hrate⟩ := exists_zetaSuperlinearTruncation hσ hσ1
  apply tendsto_dyadicSquareMean_of_uniform_error
    (continuous_zetaDirichletTail M (ne_of_lt hσ1))
    (fun T => continuous_zetaDirichletBand M (N T) σ) he
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact zetaTruncationErrorScale_nonneg (by linarith) (by linarith) m (N T)
  · filter_upwards [eventually_ge_atTop (1 : ℝ),
      hN.eventually (eventually_ge_atTop (max M 1))] with T hT hNT
    intro t ht
    have hM : M ≤ N T := (le_max_left _ _).trans hNT
    have hN1 : 1 ≤ N T := (le_max_right _ _).trans hNT
    rw [zetaDirichletBand_eq_sub hM]
    simp only [zetaDirichletTail, sub_sub_sub_cancel_right]
    exact norm_zeta_sub_head_le_arbitraryOrder (by linarith) hT ht hN1 m
  · exact tendsto_zetaDirichletBand_mean_of_cutoff M hσ hσ1 hN hrate

/-- Carlson's exact unconditioned L² approximation formula for actual zeta,
with every analytic estimate discharged on `1/2 < σ < 1`. -/
theorem carlson_zeta_tail_meanSquare (M : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / T)
      atTop (𝓝 (zetaCoefficientTailMass M σ)) :=
  tendsto_prefixSquareMean_of_dyadic (continuous_zetaDirichletTail M (ne_of_lt hσ1))
    (carlson_zeta_tail_dyadicMeanSquare M hσ hσ1)

theorem carlson_zeta_meanSquare {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T =>
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
      atTop (𝓝 (zetaCoefficientTailMass 0 σ)) := by
  simpa [zetaDirichletTail, zetaDirichletHead, edPoly] using
    carlson_zeta_tail_meanSquare 0 hσ hσ1

theorem tendsto_zetaCoefficientTailMass {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun M => zetaCoefficientTailMass M σ) atTop (𝓝 0) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hpoint (n : ℕ) :
      Tendsto (fun M : ℕ => if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    simp [hM]
  have hbound : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      ‖(if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ))‖ ≤ (n : ℝ) ^ (-2 * σ) := by
    apply Eventually.of_forall
    intro M n
    split_ifs
    · simp only [norm_zero]
      positivity
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [zetaCoefficientTailMass, tsum_zero] using
    tendsto_tsum_of_dominated_convergence hs hpoint hbound

/-- Unconditioned tails can be made arbitrarily small in limiting square mean.
The averaging threshold may depend on the fixed head length. -/
theorem carlson_zeta_L2_approximation {σ ε : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, ‖zetaDirichletTail M σ t‖ ^ 2) / T < ε := by
  filter_upwards [(tendsto_zetaCoefficientTailMass hσ).eventually_lt_const hε] with M hM
  exact (carlson_zeta_tail_meanSquare M hσ hσ1).eventually_lt_const hM

end RHTower
