import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSevenTenthsSevenCenterReceiver
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalPhaseSourceDecomposition
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryCapacityAsymptotic

/-!
# Finite source receiver for the seven-center HCF threshold

The seven-center receiver is stated for the canonical lattice widened by two sites.  Fixed-height
reindexing is asymptotically invisible by Riemann--von Mangoldt, so the existing finite regular
pole--Gamma source majorants transfer to that widened lattice with no constant loss.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A fixed forward shift preserves every nonnegative canonical asymptotic ceiling. -/
theorem criticalFeatureCanonicalAsymptoticUpper_comp_add
    {B : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (d : ℕ)
    (hB : CriticalFeatureCanonicalAsymptoticUpper B c) :
    CriticalFeatureCanonicalAsymptoticUpper (fun n => B (n + d)) c := by
  intro eps heps
  let e : ℝ := min eps 1
  let delta : ℝ := e / (2 * (c + 2))
  have hepos : 0 < e := by
    dsimp [e]
    exact lt_min heps zero_lt_one
  have heleps : e ≤ eps := by
    dsimp [e]
    exact min_le_left _ _
  have heleone : e ≤ 1 := by
    dsimp [e]
    exact min_le_right _ _
  have hc2 : 0 < c + 2 := by linarith
  have hden : 0 < 2 * (c + 2) := by positivity
  have hdeltapos : 0 < delta := div_pos hepos hden
  have hdeltale : delta ≤ 1 := by
    dsimp [delta]
    rw [div_le_one hden]
    nlinarith
  have hdeltaBudget : delta * (c + 2) = e / 2 := by
    dsimp [delta]
    field_simp [ne_of_gt hc2]
  have hshift : Tendsto (fun n : ℕ => n + d) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hBshift : ∀ᶠ n : ℕ in atTop,
      B (n + d) ≤ (c + delta) * criticalFeatureCanonicalZeroCount (n + d) :=
    hshift.eventually (hB delta hdeltapos)
  have hratio : ∀ᶠ n : ℕ in atTop,
      criticalFeatureCanonicalZeroCount (n + d) /
          criticalFeatureCanonicalZeroCount n < 1 + delta :=
    (tendsto_order.1 (tendsto_criticalFeatureCanonicalZeroCount_nat_add_div d)).2
      (1 + delta) (by linarith)
  filter_upwards [hBshift, hratio, eventually_criticalFeatureCanonicalZeroCount_pos]
    with n hBn hratioN hN
  have hNshift : criticalFeatureCanonicalZeroCount (n + d) <
      (1 + delta) * criticalFeatureCanonicalZeroCount n :=
    (div_lt_iff₀ hN).mp hratioN
  have hcdelta : 0 ≤ c + delta := by linarith
  have hmain : B (n + d) ≤
      (c + delta) * (1 + delta) * criticalFeatureCanonicalZeroCount n := by
    calc
      B (n + d) ≤ (c + delta) * criticalFeatureCanonicalZeroCount (n + d) := hBn
      _ ≤ (c + delta) * ((1 + delta) *
          criticalFeatureCanonicalZeroCount n) :=
        mul_le_mul_of_nonneg_left hNshift.le hcdelta
      _ = _ := by ring
  have hcoeff : (c + delta) * (1 + delta) ≤ c + eps := by
    have hdeltaSq : delta ^ 2 ≤ delta := by nlinarith
    nlinarith
  exact hmain.trans (mul_le_mul_of_nonneg_right hcoeff hN.le)

/-- Any standard regular finite-covariance ceiling transfers to the widened seven-center Plemelj
window without changing its constant. -/
theorem canonicalSevenCenter_plemeljCovariance_ceiling_of_regularFiniteCovariance
    {c : ℝ} (hc : 0 ≤ c)
    (hfinite : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance c) :
    CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalSevenCenterLatticeWindow n)) c := by
  have hplemelj : CriticalFeatureCanonicalAsymptoticUpper
      (fun n => criticalFeaturePoleGammaPlemeljCovariance
        (criticalFeatureCanonicalLatticeWindow n)) c :=
    (canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling c).1 hfinite
  have hshifted := criticalFeatureCanonicalAsymptoticUpper_comp_add hc 2 hplemelj
  simpa only [criticalFeatureCanonicalSevenCenterLatticeWindow] using hshifted

/-- Exact seven-center 75% theorem with the remaining premise expressed as a finite, explicit
pole--Gamma source-piece majorant rather than an infinite Plemelj covariance. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_regularSourcePieceMajorant_sevenCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularSourcePieceMajorant
        (criticalFeatureShallowReflectedSevenCenterCharge / 8)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  apply
    criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_canonicalSevenCenter_plemelj_exactCharge
  apply canonicalSevenCenter_plemeljCovariance_ceiling_of_regularFiniteCovariance
  · positivity
  · exact canonicalRegularLatticeSummedDisplacement_ceiling_of_sourcePieceMajorant hsource

/-- Phase-preserving finite source majorant version of the exact seven-center 75% receiver. -/
theorem criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_regularPhaseSourcePieceMajorant_sevenCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularPhaseSourcePieceMajorant
        (criticalFeatureShallowReflectedSevenCenterCharge / 8)) :
    CriticalFeatureCanonicalAsymptoticLower
      criticalFeatureCanonicalCriticalLineCount (3 / 4) := by
  apply
    criticalFeatureCanonicalCriticalLineCount_threeQuarters_lower_of_canonicalSevenCenter_plemelj_exactCharge
  apply canonicalSevenCenter_plemeljCovariance_ceiling_of_regularFiniteCovariance
  · positivity
  · exact canonicalRegularLatticeSummedDisplacement_ceiling_of_phaseSourcePieceMajorant hsource

end

end RHTower
