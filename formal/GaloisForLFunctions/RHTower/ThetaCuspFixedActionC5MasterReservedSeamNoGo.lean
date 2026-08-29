import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5AdaptiveReservedSeamNoGo
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5AdaptiveResidualReserve
import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamOrientation

/-!
# Master-reserved fixed-action C5 seam no-go

The strongest one-scalar endpoint of the likelihood lift has the wrong sign at the fixed-action
seam. On the physical chamber, adaptive scale-weighting strictly exceeds six units of adverse
master curvature, so the adaptive-reserved margin strictly dominates the master-reserved margin.
The former is already negative near every positive seam centre; hence the latter is negative there
as well.

This kills the chain

`one-scalar master reserve -> literal direct-J orientation -> compact/far-tail C5 assembly ->
rank-four/Ptolemy wall -> CLG/TTF or Weil positivity -> RH`.

The positive survivor is an exact two-channel decomposition of everything discarded by the master
endpoint: a strictly positive adaptive scale-gap surplus plus the exact third-likelihood-channel
residual. Wherever exact seam orientation is positive, these discarded channels reverse the
master surrogate's sign in a whole punctured seam neighbourhood. Any surviving C5 proof must
therefore retain exact third-channel transport or prove projective sixth-curvature monotonicity
directly.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Adaptive scale-weighting strictly exceeds six units of reflected master curvature. -/
theorem six_mul_neg_reflectedJetTwo_lt_c5LikelihoodAdaptiveMasterCurvature
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    6 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t) <
      c5LikelihoodAdaptiveMasterCurvature u t := by
  let Fp := thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)
  let Fm := thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t)
  let Ap := thetaCuspSingleAtomReflectionScale 1 (u + t)
  let Am := thetaCuspSingleAtomReflectionScale 1 (u - t)
  have hFp : 0 < Fp := by
    simpa only [Fp] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_pos (show 0 ≤ u + t by linarith)
  have hFm : 0 < Fm := by
    simpa only [Fm] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_pos (show 0 ≤ u - t by linarith)
  have hAp : 3 < Ap := by
    simpa only [Ap] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) Nat.one_pos
        (show 0 ≤ u + t by linarith)
  have hAm : 3 < Am := by
    simpa only [Am] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) Nat.one_pos
        (show 0 ≤ u - t by linarith)
  have hp : 6 * Fp < 2 * Ap * Fp := by nlinarith
  have hm : 6 * Fm < 2 * Am * Fm := by nlinarith
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
    c5LikelihoodAdaptiveMasterCurvature
  dsimp only [Fp, Fm, Ap, Am] at hp hm ⊢
  linarith

/-- The adaptive-reserved lower endpoint strictly dominates the universal master-reserved one. -/
theorem c5CompletedMasterReservedCompensationMargin_lt_adaptiveReserved
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedMasterReservedCompensationMargin u t <
      c5CompletedAdaptiveReservedCompensationMargin u t := by
  have ha := c5CompletedActionJetOne_pos ht htu
  have hz := six_mul_neg_reflectedJetTwo_lt_c5LikelihoodAdaptiveMasterCurvature
    ht.le htu.le
  have hc : 0 < 5 * t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t := by
    positivity
  have hmul := mul_lt_mul_of_pos_left hz hc
  unfold c5CompletedMasterReservedCompensationMargin
    c5CompletedAdaptiveReservedCompensationMargin
  nlinarith

/-- Universal one-scalar master reserve has the wrong sign near every positive seam centre. -/
theorem eventually_c5CompletedMasterReservedCompensationMargin_neg
    {u : ℝ} (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      c5CompletedMasterReservedCompensationMargin u t < 0 := by
  rcases eventually_c5CompletedAdaptiveReservedCompensationMargin_neg hu with
    ⟨δ, hδ, hδu, hlocal⟩
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  have htu : t < u := lt_of_lt_of_le htδ hδu
  exact lt_trans
    (c5CompletedMasterReservedCompensationMargin_lt_adaptiveReserved ht htu)
    (hlocal t ht htδ)

/-- No positive seam centre admits universal nonnegativity of the master-reserved margin. -/
theorem not_forall_c5CompletedMasterReservedCompensationMargin_nonneg
    {u : ℝ} (hu : 0 < u) :
    ¬ ∀ t : ℝ, 0 < t → t < u →
      0 ≤ c5CompletedMasterReservedCompensationMargin u t := by
  rcases eventually_c5CompletedMasterReservedCompensationMargin_neg hu with
    ⟨δ, hδ, hδu, hlocal⟩
  intro hnonneg
  let t := δ / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have htδ : t < δ := by dsimp only [t]; linarith
  have htu : t < u := lt_of_lt_of_le htδ hδu
  exact (not_lt_of_ge (hnonneg t ht htu)) (hlocal t ht htδ)

/-- Strict scale-gap surplus lost by replacing adaptive curvature with six master units. -/
def c5CompletedMasterAdaptiveScaleGap (u t : ℝ) : ℝ :=
  5 * t ^ 2 * thetaCuspCompletedReflectedCumulantJetOne u t *
    (c5LikelihoodAdaptiveMasterCurvature u t -
      6 * (-thetaCuspReflectedLikelihoodCumulantJetTwo u t))

/-- Full reserve discarded by the one-scalar master endpoint. -/
def c5CompletedMasterResidualReserve (u t : ℝ) : ℝ :=
  c5CompletedCompensationMargin u t -
    c5CompletedMasterReservedCompensationMargin u t

/-- The discarded master residual splits into scale-gap surplus and exact third-channel reserve. -/
theorem c5CompletedMasterResidualReserve_eq_scaleGap_add_adaptiveResidual
    (u t : ℝ) :
    c5CompletedMasterResidualReserve u t =
      c5CompletedMasterAdaptiveScaleGap u t +
        c5CompletedAdaptiveResidualReserve u t := by
  unfold c5CompletedMasterResidualReserve
  rw [c5CompletedCompensationMargin_eq_adaptive_add_residual]
  unfold c5CompletedMasterAdaptiveScaleGap
    c5CompletedAdaptiveReservedCompensationMargin
    c5CompletedMasterReservedCompensationMargin
  ring

/-- The scale-gap part of the discarded master residual is strictly positive. -/
theorem c5CompletedMasterAdaptiveScaleGap_pos
    {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    0 < c5CompletedMasterAdaptiveScaleGap u t := by
  have ha := c5CompletedActionJetOne_pos ht htu
  have hz := six_mul_neg_reflectedJetTwo_lt_c5LikelihoodAdaptiveMasterCurvature
    ht.le htu.le
  unfold c5CompletedMasterAdaptiveScaleGap
  positivity

/-- On the structural tail, both exact channels discarded by the master endpoint are strict. -/
theorem c5CompletedMasterResidualReserve_pos
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5CompletedMasterResidualReserve u t := by
  rw [c5CompletedMasterResidualReserve_eq_scaleGap_add_adaptiveResidual]
  exact add_pos
    (c5CompletedMasterAdaptiveScaleGap_pos ht htu)
    (c5CompletedAdaptiveResidualReserve_pos ht htu hscale)

/-- Exact replacement endpoint retaining every channel discarded by master reduction. -/
theorem c5CompletedCompensationMargin_pos_iff_master_gt_neg_residual
    (u t : ℝ) :
    0 < c5CompletedCompensationMargin u t ↔
      -c5CompletedMasterResidualReserve u t <
        c5CompletedMasterReservedCompensationMargin u t := by
  unfold c5CompletedMasterResidualReserve
  constructor <;> intro h <;> linarith

/-- Where exact seam orientation is positive, literal compensation and its master surrogate have
opposite signs in one punctured seam neighbourhood. -/
theorem eventually_completedCompensation_pos_and_masterReserved_neg_of_exactSeamOrientation
    {u : ℝ} (hu : 0 < u)
    (hΩ : 0 < thetaCuspC5ExactCompletedSeamOrientation u) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ u ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < c5CompletedCompensationMargin u t ∧
        c5CompletedMasterReservedCompensationMargin u t < 0 := by
  rcases eventually_c5CompletedCompensationMargin_pos_of_exactSeamOrientation hu hΩ with
    ⟨δp, hδp, hδpu, hp⟩
  rcases eventually_c5CompletedMasterReservedCompensationMargin_neg hu with
    ⟨δn, hδn, hδnu, hn⟩
  let δ := min δp δn
  have hδ : 0 < δ := lt_min hδp hδn
  have hδu : δ ≤ u := le_trans (min_le_left _ _) hδpu
  refine ⟨δ, hδ, hδu, ?_⟩
  intro t ht htδ
  exact ⟨hp t ht (lt_of_lt_of_le htδ (min_le_left _ _)),
    hn t ht (lt_of_lt_of_le htδ (min_le_right _ _))⟩

end

end RHTower
