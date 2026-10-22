import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedCurvatureArchRenormalization
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadGammaWallOutgoingProducer

/-!
# Suzuki curvature as literal CCM prime--polar--Gamma cells

Suzuki's regular curvature kernel deletes exactly the higher Binet modes of the CCM Gamma
translation density. Pointwise, the deleted tail is identical and

`screwRegularKernel + ccmGammaTranslationDensity = 2 * cosh (t / 2)`.

Therefore every signed Suzuki checkpoint atom is not merely analogous to a completed CCM source:
it is exactly one polar-minus-Gamma-minus-prime logarithmic cell. Its event-label first moment
lands in the central CCM-UR/HG coherent source with only the `o(N)` source-free renormalization
proved previously. This preserves prime--polar--Gamma cancellation before Route-O matched-head
damping and does not identify the distinct common-clock and actual-head operators.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open scoped Interval

theorem suzukiCheckpointArchTail_eq_ccmGammaHigherBinetModeDensity (t : ℝ) :
    suzukiCheckpointArchTail t = ccmGammaHigherBinetModeDensity t := by
  unfold suzukiCheckpointArchTail ccmGammaHigherBinetModeDensity
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

theorem screwRegularKernel_eq_polar_sub_ccmGammaTranslationDensity
    {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t =
      2 * Real.cosh (t / 2) - ccmGammaTranslationDensity t := by
  rw [ccmGammaTranslationDensity_eq_first_add_higher ht,
    ccmGammaFirstBinetModeWeight,
    ← suzukiCheckpointArchTail_eq_ccmGammaHigherBinetModeDensity]
  unfold screwRegularKernel suzukiCheckpointArchTail
  rw [Real.cosh_eq]
  ring

theorem screwRegularKernel_add_ccmGammaTranslationDensity_eq_polar
    {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t + ccmGammaTranslationDensity t =
      2 * Real.cosh (t / 2) := by
  rw [screwRegularKernel_eq_polar_sub_ccmGammaTranslationDensity ht]
  ring

/-- Literal polar-minus-Gamma-minus-prime cell on one logarithmic checkpoint interval. -/
def ccmSuzukiPrimePolarGammaCurvatureCell (N : ℕ) : ℝ :=
  (∫ t in Real.log (N : ℝ)..Real.log ((N + 1 : ℕ) : ℝ),
      2 * Real.cosh (t / 2)) -
    (∫ t in Real.log (N : ℝ)..Real.log ((N + 1 : ℕ) : ℝ),
      ccmGammaTranslationDensity t) -
    criticalMellinAtomWeight (N + 1)

theorem suzukiCheckpointSignedCurvatureCell_eq_primePolarGamma
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointSignedCurvatureCell N =
      ccmSuzukiPrimePolarGammaCurvatureCell N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogle : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr
      (by exact_mod_cast (Nat.le_succ N))
  have hgammaCont : ContinuousOn ccmGammaTranslationDensity
      (Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      exact ne_of_gt (one_sub_exp_neg_two_mul_pos (hlogpos.trans_le ht.1))
  have hgammaInt : IntervalIntegrable ccmGammaTranslationDensity volume
      (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)) := by
    have hcont : ContinuousOn ccmGammaTranslationDensity
        (uIcc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) := by
      simpa only [uIcc_of_le hlogle] using hgammaCont
    exact hcont.intervalIntegrable
  have hpolarInt : IntervalIntegrable (fun t : ℝ => 2 * Real.cosh (t / 2)) volume
      (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => 2 * Real.cosh (t / 2)).intervalIntegrable _ _
  unfold suzukiCheckpointSignedCurvatureCell ccmSuzukiPrimePolarGammaCurvatureCell
  rw [← intervalIntegral.integral_sub hpolarInt hgammaInt]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Icc (Real.log (N : ℝ))
      (Real.log ((N + 1 : ℕ) : ℝ)) := by
    simpa only [uIcc_of_le hlogle] using ht
  rw [screwRegularKernel_eq_polar_sub_ccmGammaTranslationDensity
    (hlogpos.trans_le htIcc.1)]

/-- Event-label first moment of literal prime--polar--Gamma curvature cells. -/
def ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    ccmSuzukiPrimePolarGammaCurvatureCell (k - 1)

theorem weightedSignedCurvaturePrefix_eq_primePolarGamma (N : ℕ) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N =
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N := by
  rw [suzukiCheckpointWeightedSignedCurvaturePrefix,
    ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix]
  apply Finset.sum_congr rfl
  intro k hk
  rw [suzukiCheckpointSignedCurvatureCell_eq_primePolarGamma
    (by have := (Finset.mem_Ico.mp hk).1; omega : 2 ≤ k - 1)]

theorem unitRiesz_center_eq_weightedPrimePolarGammaCurvature_add_arch
    {N : ℕ} (hN : 1 ≤ N) :
    ((N + 2 : ℕ) : ℝ) *
        unitRieszCompletedCoherentBarycenter (N + 2) 0 =
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N +
        suzukiCheckpointWeightedArchRenormalization N := by
  rw [← weightedSignedCurvaturePrefix_eq_primePolarGamma]
  exact unitRiesz_center_eq_weightedSignedCurvature_add_arch hN

theorem tendsto_normalizedPrimePolarGammaCurvature_sub_unitRieszCenter_zero :
    Tendsto (fun N : ℕ =>
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N / (N + 2 : ℕ) -
        unitRieszCompletedCoherentBarycenter (N + 2) 0)
      atTop (nhds 0) := by
  have h :=
    tendsto_normalizedSignedCurvatureFirstMoment_sub_unitRieszCenter_zero
  apply h.congr'
  exact Eventually.of_forall fun N => by
    unfold suzukiCheckpointNormalizedSignedCurvatureFirstMoment
    change suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 2 : ℕ) - _ =
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N / (N + 2 : ℕ) - _
    rw [weightedSignedCurvaturePrefix_eq_primePolarGamma]

theorem tendsto_normalizedPrimePolarGammaCurvature_iff_unitRieszCenter
    (L : ℝ) :
    Tendsto (fun N : ℕ =>
      ccmSuzukiWeightedPrimePolarGammaCurvaturePrefix N / (N + 2 : ℕ))
        atTop (nhds L) ↔
      Tendsto (fun N : ℕ =>
        unitRieszCompletedCoherentBarycenter (N + 2) 0) atTop (nhds L) := by
  have hdiff :=
    tendsto_normalizedPrimePolarGammaCurvature_sub_unitRieszCenter_zero
  constructor
  · intro hcurv
    have h := hcurv.sub hdiff
    simpa only [sub_zero] using h.congr'
      (Eventually.of_forall fun N => by ring)
  · intro hcenter
    have h := hdiff.add hcenter
    simpa only [zero_add] using h.congr'
      (Eventually.of_forall fun N => by ring)

end RHTower
