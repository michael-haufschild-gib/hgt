import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureStationaryAcceleration
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSourceCumulativeFluxBalance

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Fifth-root curvature after removing the strictly positive accumulated-drop square. -/
def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
    (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceFifthRootCurvatureNumerator u t /
    thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ)

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_eq_four_cumulative
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t =
      4 * thetaCuspReflectedSourceCumulativeFluxC5Balance u t := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_cumulativeFluxC5Balance
    u ht]
  field_simp [(thetaCuspReflectedSourceFirstDrop_pos u ht).ne']

theorem hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u)
      ((thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
            thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ) -
          thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
            (2 * thetaCuspReflectedSourceFirstDrop u t *
              thetaCuspReflectedSourceDecayFlux u t)) /
        (thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ)) ^ (2 : ℕ)) t := by
  have hN := hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator u t
  have hA := hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hraw := hN.div (hA.pow 2)
    (pow_ne_zero 2 (thetaCuspReflectedSourceFirstDrop_pos u ht).ne')
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
  change HasDerivAt
    (thetaCuspReflectedSourceFifthRootCurvatureNumerator u /
      thetaCuspReflectedSourceFirstDrop u ^ (2 : ℕ)) _ t
  simpa only [Pi.pow_apply, Pi.div_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    using hraw

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t < 0 ↔
      thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
  have hden := sq_pos_of_pos (thetaCuspReflectedSourceFirstDrop_pos u ht)
  rw [div_neg_iff]
  simp [hden, not_lt_of_ge hden.le]

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_pos_iff
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t ↔
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator u t := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance
  have hden := sq_pos_of_pos (thetaCuspReflectedSourceFirstDrop_pos u ht)
  rw [div_pos_iff]
  simp [hden, not_lt_of_ge hden.le]

/-- An intrinsic-balance local minimum satisfies an exact falling-flank law for raw C5. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t) :
    thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
        thetaCuspReflectedSourceFirstDrop u t =
      2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
        thetaCuspReflectedSourceDecayFlux u t := by
  have hzero := hmin.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u ht)
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hden :
      (thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ)) ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (pow_ne_zero 2 hA.ne')
  simp only [div_eq_zero_iff, hden, or_false] at hzero
  have hfactor :
      thetaCuspReflectedSourceFirstDrop u t *
          (thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
              thetaCuspReflectedSourceFirstDrop u t -
            2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
              thetaCuspReflectedSourceDecayFlux u t) = 0 := by
    calc
      _ = thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
              thetaCuspReflectedSourceFirstDrop u t ^ (2 : ℕ) -
            thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
              (2 * thetaCuspReflectedSourceFirstDrop u t *
                thetaCuspReflectedSourceDecayFlux u t) := by ring
      _ = 0 := hzero
  have hinner := (mul_eq_zero.mp hfactor).resolve_left hA.ne'
  linarith

/-- A negative intrinsic-balance local minimum lies strictly on the descending flank of raw C5. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureVelocity_neg_of_intrinsicBalance_localMin_neg
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t)
    (hneg : thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u t < 0) :
    thetaCuspReflectedSourceFifthRootCurvatureVelocity u t < 0 := by
  have hN : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0 :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff u ht).mp hneg
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hD := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hrel :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
      u ht hmin
  have hprod :
      thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
          thetaCuspReflectedSourceFirstDrop u t < 0 := by
    rw [hrel]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hN) hD
  by_contra hnot
  exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hnot) hA.le)) hprod

/-- A negative raw-C5 stationary point is strictly ascending after intrinsic normalization. -/
theorem deriv_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_pos_of_velocity_zero_neg
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hvelocity : thetaCuspReflectedSourceFifthRootCurvatureVelocity u t = 0)
    (hneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator u t < 0) :
    0 < deriv (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t := by
  rw [(hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u ht).deriv,
    hvelocity]
  simp only [zero_mul, zero_sub]
  have hA := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hD := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hweight :
      0 < 2 * thetaCuspReflectedSourceFirstDrop u t *
        thetaCuspReflectedSourceDecayFlux u t := by positivity
  have hnum :
      0 < -(thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
        (2 * thetaCuspReflectedSourceFirstDrop u t *
          thetaCuspReflectedSourceDecayFlux u t)) :=
    neg_pos.mpr (mul_neg_of_neg_of_pos hneg hweight)
  exact div_pos hnum (sq_pos_of_pos (sq_pos_of_pos hA))

/-- Every modular-center C5 failure has a negative local minimum of the bounded intrinsic
cumulative balance.  At that same point raw C5 is still strictly descending, the native fourth
Turán ceiling holds, and the exact cofinal likelihood tax overspends its nonlocal reserve. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicBalance_localMin
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t *
          thetaCuspReflectedSourceFirstDrop 0 t =
        2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t *
          thetaCuspReflectedSourceDecayFlux 0 t ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t < 0 ∧
      thetaCuspReflectedLogJetFour_thetaCuspFifthRootCurvatureStationaryAcceleration 0 t + 320 <
        2 * thetaCuspReflectedLogJetTwo 0 t ^ (2 : ℕ) ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  rcases hfail with ⟨t0, ht0, hneg0⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right 0 with
    ⟨delta0, hdelta0, hnear⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos_tail with
    ⟨T0, hT0, htail⟩
  let delta := min (delta0 / 2) (t0 / 2)
  let T := max T0 (t0 + 1)
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdeltadelta0 : delta < delta0 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdeltat0 : delta < t0 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ht0T : t0 < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT0T : T0 ≤ T := le_max_left _ _
  have hdeltaNpos :
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 delta :=
    hnear delta hdelta hdeltadelta0
  have hTNpos : 0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 T :=
    htail T hT0T
  have hdeltaBpos :
      0 < thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 delta :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_pos_iff 0 hdelta).2
      hdeltaNpos
  have hTBpos :
      0 < thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 T :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_pos_iff 0
      (hdelta.trans (show delta < T from hdeltat0.trans ht0T))).2 hTNpos
  have hnegB0 :
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t0 < 0 :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff 0 ht0).2 hneg0
  have hcont : ContinuousOn
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) (Icc delta T) := by
    intro x hx
    have hxpos : 0 < x := hdelta.trans_le hx.1
    exact
      (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 hxpos).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t0, hdeltat0.le, ht0T.le⟩ hcont
  have hnegB :
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 t < 0 :=
    lt_of_le_of_lt (hmin ⟨hdeltat0.le, ht0T.le⟩) hnegB0
  have hdeltat : delta < t := by
    exact lt_of_le_of_ne ht.1 (fun h => by
      subst t
      linarith)
  have htT : t < T := by
    exact lt_of_le_of_ne ht.2 (fun h => by
      subst t
      linarith)
  have hlocal : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t :=
    hmin.isLocalMin (Icc_mem_nhds hdeltat htT)
  have htpos : 0 < t := hdelta.trans hdeltat
  have hrel :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
      0 htpos hlocal
  have hvelneg :=
    thetaCuspReflectedSourceFifthRootCurvatureVelocity_neg_of_intrinsicBalance_localMin_neg
      0 htpos hlocal hnegB
  have hNneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
    (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_neg_iff 0 htpos).mp hnegB
  have hover :
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
    apply lt_of_not_ge
    intro hreserve
    have hnonneg :=
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        htpos).mpr hreserve
    exact (not_lt_of_ge hnonneg) hNneg
  exact ⟨t, htpos, hnegB, hlocal, hrel, hvelneg,
    thetaCuspReflectedLogJetFour_zero_add_threeHundredTwenty_lt_two_sq htpos, hover⟩

/-- Two-critical-point failure law.  A modular-center C5 failure forces two distinct exact
likelihood-tax overspends: one at a negative local minimum of the intrinsic cumulative balance,
where raw C5 is descending, and another at a negative stationary local minimum of raw C5, where
its acceleration is nonnegative. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_two_distinct_critical_taxOverspends
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ s t : ℝ,
      0 < s ∧ 0 < t ∧ s ≠ t ∧
      IsLocalMin
        (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) s ∧
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0 s < 0 ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 s < 0 ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero s <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero s ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 ∧
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureAcceleration 0 t ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  obtain ⟨s, hs, hsnegB, hslocal, _hsrel, hsvelneg, _hsfour, hsover⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicBalance_localMin
      hfail
  obtain ⟨t, ht, htneg, htvelocity, htacc, _htfour⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_acceleration
      hfail
  have htover :
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
    apply lt_of_not_ge
    intro hreserve
    have hnonneg :=
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mpr hreserve
    exact (not_lt_of_ge hnonneg) htneg
  have hne : s ≠ t := by
    intro hst
    subst t
    linarith
  exact ⟨s, t, hs, ht, hne, hslocal, hsnegB, hsvelneg, hsover,
    htneg, htvelocity, htacc, htover⟩

/-- Exact intrinsic local-minimum reduction: modular-center C5 is global if and only if the
cofinal likelihood tax is absorbed at every positive local minimum of the bounded cumulative
mass/elasticity balance. -/
theorem
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicBalance_localMin_taxReserve :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        IsLocalMin
          (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance 0) t →
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
          thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t := by
  constructor
  · intro h t ht _hlocal
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mp (h t ht)
  · intro h t ht
    by_contra hnot
    obtain ⟨s, hs, _hsnegB, hslocal, _hsrel, _hsvelneg, _hsfour, hsover⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicBalance_localMin
        ⟨t, ht, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge (h s hs hslocal)) hsover

end

end RHTower
