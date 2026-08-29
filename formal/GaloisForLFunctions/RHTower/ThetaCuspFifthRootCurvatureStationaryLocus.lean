import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCompactCore

/-!
# Stationary-locus reduction for modular-center theta C5

The corpus proves strict modular-center C5 near coalescence and again on a cofinal tail.  Hence a
failure cannot escape through either boundary: it attains a negative interior minimum.  This
module differentiates the exact C5 numerator and formalizes that failure localization.

Consequently the all-radius center problem is equivalent to the nonlocal chord reserve beating
the likelihood tax only where one explicit third-jet velocity vanishes.  This is the surviving
stationary-locus burden feeding source C5, the rank-four odd wall, higher-packet/no-escape
transport, TTF/Weil positivity, and the existing RH endpoint.  It does not assert the still-open
stationary-locus inequality or the off-center and higher-packet joins.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Third ordinary jet of the positive reflected-source decay flux. -/
def thetaCuspReflectedSourceDecayFluxThirdJet (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t *
    (thetaCuspReflectedLogJetThree u t -
      3 * thetaCuspReflectedLogJetOne u t * thetaCuspReflectedLogJetTwo u t +
      thetaCuspReflectedLogJetOne u t ^ 3)

theorem hasDerivAt_thetaCuspReflectedSourceDecayFluxCurvature
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceDecayFluxCurvature u)
      (thetaCuspReflectedSourceDecayFluxThirdJet u t) t := by
  have hp := hasDerivAt_thetaCuspReflectedSourceProduct u t
  have hq₁ := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hq₂ := hasDerivAt_thetaCuspReflectedLogJetTwo u t
  have hinside := hq₂.sub (hq₁.pow 2)
  have hraw := hp.mul hinside
  unfold thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceDecayFluxThirdJet
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  unfold thetaCuspReflectedSourceDecayFlux
  simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- Ordinary displacement velocity of the source fifth-root curvature numerator. -/
def thetaCuspReflectedSourceFifthRootCurvatureVelocity (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let K := thetaCuspReflectedSourceDecayFluxThirdJet u t
  39 * A * D + t * A * J - 17 * t * D ^ 2 +
    t ^ 2 * (5 * A * K - 3 * D * J)

theorem hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceFifthRootCurvatureNumerator u)
      (thetaCuspReflectedSourceFifthRootCurvatureVelocity u t) t := by
  let A : ℝ → ℝ := thetaCuspReflectedSourceFirstDrop u
  let D : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux u
  let J : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxCurvature u
  let K : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxThirdJet u
  have hA : HasDerivAt A (D t) t := by
    simpa only [A, D] using hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hD : HasDerivAt D (J t) t := by
    simpa only [D, J] using hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hJ : HasDerivAt J (K t) t := by
    simpa only [J, K] using hasDerivAt_thetaCuspReflectedSourceDecayFluxCurvature u t
  have hfirst := (hA.pow 2).const_mul 24
  have hsecond := (((hasDerivAt_id t).mul hA).mul hD).const_mul 9
  have hinner := (hA.mul hJ).const_mul 5 |>.sub ((hD.pow 2).const_mul 4)
  have hthird := ((hasDerivAt_id t).pow 2).mul hinner
  have hraw := hfirst.sub hsecond |>.add hthird
  have hraw' : HasDerivAt
      (((fun y => 24 * (A ^ 2) y) -
          fun y => 9 * ((id : ℝ → ℝ) * A * D) y) +
        (id : ℝ → ℝ) ^ 2 * ((fun y => 5 * (A * J) y) -
          fun y => 4 * (D ^ 2) y))
      (39 * A t * D t + t * A t * J t - 17 * t * D t ^ 2 +
        t ^ 2 * (5 * A t * K t - 3 * D t * J t)) t := by
    refine hraw.congr_deriv ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    ring
  unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    thetaCuspReflectedSourceFifthRootCurvatureVelocity
  dsimp only [A, D, J, K]
  refine hraw'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq]
  ring

theorem continuous_thetaCuspReflectedSourceFifthRootCurvatureNumerator
    (u : ℝ) :
    Continuous (thetaCuspReflectedSourceFifthRootCurvatureNumerator u) := by
  exact continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator u t).continuousAt

/-- Every modular-center C5 failure has a negative stationary witness. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_neg
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 := by
  rcases hfail with ⟨t₀, ht₀, hneg₀⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right 0 with
    ⟨δ₀, hδ₀, hnear⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos_tail with
    ⟨T₀, hT₀, htail⟩
  let δ := min (δ₀ / 2) (t₀ / 2)
  let T := max T₀ (t₀ + 1)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδδ₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδt₀ : δ < t₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ht₀T : t₀ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hδpos : 0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 δ :=
    hnear δ hδ hδδ₀
  have hTpos : 0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 T :=
    htail T hT₀T
  have hcont : ContinuousOn
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) (Icc δ T) :=
    (continuous_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0).continuousOn
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t₀, hδt₀.le, ht₀T.le⟩ hcont
  have hneg : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0 :=
    lt_of_le_of_lt (hmin ⟨hδt₀.le, ht₀T.le⟩) hneg₀
  have hδt : δ < t := by
    exact lt_of_le_of_ne ht.1 (fun h => by
      subst t
      linarith)
  have htT : t < T := by
    exact lt_of_le_of_ne ht.2 (fun h => by
      subst t
      linarith)
  have hlocal : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) t :=
    hmin.isLocalMin (Icc_mem_nhds hδt htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t)
  exact ⟨t, hδ.trans hδt, hneg, hstationary⟩

/-- Global modular-center C5 is equivalent to positivity only on its stationary locus. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 →
        0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t := by
  constructor
  · intro h t ht _
    exact h t ht
  · intro h t ht
    by_contra hneg
    obtain ⟨s, hs, hsneg, hsstat⟩ :=
      thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_neg
        ⟨t, ht, lt_of_not_ge hneg⟩
    exact (not_lt_of_ge (h s hs hsstat)) hsneg

/-- The exact surviving compact-core burden: the nonlocal likelihood reserve only needs to beat
its tax density where the C5 velocity vanishes. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_taxReserve :
    (∀ t : ℝ, 0 < t →
      0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
      ∀ t : ℝ, 0 < t →
        thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 →
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t ≤
          thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary]
  constructor
  · intro h t ht hstationary
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mp (h t ht hstationary)
  · intro h t ht hstationary
    exact
      (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
        ht).mpr (h t ht hstationary)

/-- Any modular-center failure therefore produces a stationary strict overspend of the exact
nonlocal chord reserve. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_taxOverspend
    (hfail : ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t < 0) :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t = 0 ∧
      thetaCuspCompletedProductFiberCofinalLikelihoodIntegralDriftReserveAtZero t <
        thetaCuspCompletedProductFiberCofinalLikelihoodTaxDensityAtZero t := by
  obtain ⟨t, ht, hneg, hstationary⟩ :=
    thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_neg hfail
  refine ⟨t, ht, hstationary, ?_⟩
  apply lt_of_not_ge
  intro hreserve
  have hnonneg :=
    (thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve
      ht).mpr hreserve
  exact (not_lt_of_ge hnonneg) hneg

end

end RHTower
