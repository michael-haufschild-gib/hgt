import GaloisForLFunctions.HilbertMetric.RiccatiCorrelationAngle
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.ThetaCuspSingleAtomReflectedRiccatiContraction
import GaloisForLFunctions.RHTower.ThetaCuspReflectedLikelihoodCumulantObstruction

/-!
# Theta-cusp reflected Riccati-angle connector

The exact single-atom Riccati margin transports to correlation-angle subadditivity on every
same-half-line packet.  For the completed source, the same connector identifies the likelihood
cumulant correction as the only remaining input.
-/

open Set

namespace RHTower

noncomputable section

/-- The reflected action of one theta atom is strictly positive away from the normalized seam. -/
theorem thetaCuspSingleAtomReflectedAction_pos_of_sameHalfLine
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspSingleAtomReflectedAction
      (thetaCuspSingleAtomReflectionScale n u) t := by
  let A := thetaCuspSingleAtomReflectionScale n u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hu : 0 ≤ u := le_trans ht.le htu
  have hA : 3 < A := by
    simpa only [A] using three_lt_thetaCuspSingleAtomReflectionScale hn hu
  have hz : 0 < z := by
    dsimp [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hr : 0 < r := by
    simpa only [A, z, r] using
      thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine hn ht.le htu
  have hrlt : r < 1 := by
    dsimp [r, thetaCuspSingleAtomReflectionFactor]
    nlinarith [mul_pos hl hz]
  have hlog : Real.log r < 0 := Real.log_neg hr hrlt
  dsimp [thetaCuspSingleAtomReflectedAction, A, z, r] at hlog ⊢
  nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < A)) hz]

/-- Exponentiating the negative atom action recovers its normalized reflected model. -/
theorem exp_neg_thetaCuspSingleAtomReflectedAction_eq_model
    {n : ℕ} (hn : 0 < n) {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    Real.exp
        (-thetaCuspSingleAtomReflectedAction
          (thetaCuspSingleAtomReflectionScale n u) t) =
      thetaCuspSingleAtomReflectedNormalizedModel
        (thetaCuspSingleAtomReflectionScale n u)
        (thetaCuspSingleAtomReflectionDefect t) := by
  have hr :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine hn ht htu
  have hmodel :
      0 < thetaCuspSingleAtomReflectedNormalizedModel
        (thetaCuspSingleAtomReflectionScale n u)
        (thetaCuspSingleAtomReflectionDefect t) := by
    unfold thetaCuspSingleAtomReflectedNormalizedModel
    exact mul_pos hr (Real.exp_pos _)
  rw [thetaCuspSingleAtomReflectedAction_eq_neg_log_model hr.ne']
  simp only [neg_neg]
  exact Real.exp_log hmodel

/-- **Unconditional atom angle law.**  Every ordered same-half-line packet of a theta atom obeys
the correlation-angle triangle inequality. -/
theorem thetaCuspSingleAtomReflectedCorrelationAngle_subadditive
    {n : ℕ} (hn : 0 < n) {u x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u) :
    Real.arccos
        (thetaCuspSingleAtomReflectedNormalizedModel
          (thetaCuspSingleAtomReflectionScale n u)
          (thetaCuspSingleAtomReflectionDefect (x + y))) ≤
      Real.arccos
          (thetaCuspSingleAtomReflectedNormalizedModel
            (thetaCuspSingleAtomReflectionScale n u)
            (thetaCuspSingleAtomReflectionDefect x)) +
        Real.arccos
          (thetaCuspSingleAtomReflectedNormalizedModel
            (thetaCuspSingleAtomReflectionScale n u)
            (thetaCuspSingleAtomReflectionDefect y)) := by
  let A := thetaCuspSingleAtomReflectionScale n u
  let q : ℝ → ℝ := thetaCuspSingleAtomReflectedAction A
  let q₁ : ℝ → ℝ := fun t =>
    thetaCuspSingleAtomReflectedActionJetOne A
      (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t))
  let q₂ : ℝ → ℝ := fun t =>
    thetaCuspSingleAtomReflectedActionJetTwo A
      (thetaCuspSingleAtomReflectionDefect t)
  let q₃ : ℝ → ℝ := fun t =>
    thetaCuspSingleAtomReflectedActionJetThree A
      (thetaCuspSingleAtomReflectionDefect t) (2 * Real.sinh (2 * t))
  have hT : 0 ≤ x + y := add_nonneg hx hy
  have hfactor (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 < thetaCuspSingleAtomReflectionFactor A
        (thetaCuspSingleAtomReflectionDefect t) := by
    simpa only [A] using
      thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
        hn ht.1 (ht.2.trans hxyu)
  have hq (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q (q₁ t) t := by
    exact hasDerivAt_thetaCuspSingleAtomReflectedAction (hfactor t ht).ne'
  have hq₁ (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q₁ (q₂ t) t := by
    exact hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne (hfactor t ht).ne'
  have hq₂ (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q₂ (q₃ t) t := by
    exact hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo (hfactor t ht).ne'
  have hqnonneg (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 ≤ q t := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · simp [q, thetaCuspSingleAtomReflectedAction,
        thetaCuspSingleAtomReflectionDefect,
        thetaCuspSingleAtomReflectionFactor]
    · exact (thetaCuspSingleAtomReflectedAction_pos_of_sameHalfLine
        hn htpos (ht.2.trans hxyu)).le
  have hqpos (t : ℝ) (ht : t ∈ interior (Icc 0 (x + y))) :
      0 < q t := by
    have ht' : t ∈ Icc 0 (x + y) := interior_subset ht
    have htpos : 0 < t := by
      rw [interior_Icc] at ht
      exact ht.1
    exact thetaCuspSingleAtomReflectedAction_pos_of_sameHalfLine
      hn htpos (ht'.2.trans hxyu)
  have hmargin (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 ≤ 2 * q₁ t * q₂ t - q₃ t := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · simp [q₁, q₂, q₃, thetaCuspSingleAtomReflectedActionJetOne,
        thetaCuspSingleAtomReflectedActionJetThree,
        thetaCuspSingleAtomReflectionDefect]
    · simpa only [q₁, q₂, q₃,
        thetaCuspSingleAtomReflectedRiccatiMargin] using
        (thetaCuspSourceTerm_reflectedRiccatiMargin_pos
          hn htpos (ht.2.trans hxyu)).le
  have hangle :=
    HilbertMetric.riccatiCorrelationAngle_subadditive_of_margin_nonneg
      hT
      (q := q) (q₁ := q₁) (q₂ := q₂) (q₃ := q₃)
      (by
        simp [q, thetaCuspSingleAtomReflectedAction,
          thetaCuspSingleAtomReflectionDefect,
          thetaCuspSingleAtomReflectionFactor])
      (by
        simp [q₁, thetaCuspSingleAtomReflectedActionJetOne,
          thetaCuspSingleAtomReflectionDefect])
      hq hq₁ hq₂ hqnonneg hqpos hmargin hx hy le_rfl
  simp only [HilbertMetric.riccatiCorrelationAngle, q] at hangle
  have hxyexp :=
    exp_neg_thetaCuspSingleAtomReflectedAction_eq_model hn hT hxyu
  have hxexp :=
    exp_neg_thetaCuspSingleAtomReflectedAction_eq_model hn hx
      ((le_add_of_nonneg_right hy).trans hxyu)
  have hyexp :=
    exp_neg_thetaCuspSingleAtomReflectedAction_eq_model hn hy
      ((le_add_of_nonneg_left hx).trans hxyu)
  rw [show
      Real.exp (-thetaCuspSingleAtomReflectedAction A (x + y)) =
        thetaCuspSingleAtomReflectedNormalizedModel A
          (thetaCuspSingleAtomReflectionDefect (x + y)) by
        simpa only [A] using hxyexp,
    show
      Real.exp (-thetaCuspSingleAtomReflectedAction A x) =
        thetaCuspSingleAtomReflectedNormalizedModel A
          (thetaCuspSingleAtomReflectionDefect x) by
        simpa only [A] using hxexp,
    show
      Real.exp (-thetaCuspSingleAtomReflectedAction A y) =
        thetaCuspSingleAtomReflectedNormalizedModel A
          (thetaCuspSingleAtomReflectionDefect y) by
        simpa only [A] using hyexp] at hangle
  simpa only [A] using hangle

/-- Source-product form of the unconditional atom angle law. -/
theorem thetaCuspSourceTerm_reflectedCorrelationAngle_subadditive
    {n : ℕ} (hn : 0 < n) {u x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u) :
    Real.arccos
        (thetaCuspSourceTerm (u + (x + y)) n *
            thetaCuspSourceTerm (u - (x + y)) n /
          thetaCuspSourceTerm u n ^ (2 : ℕ)) ≤
      Real.arccos
          (thetaCuspSourceTerm (u + x) n *
              thetaCuspSourceTerm (u - x) n /
            thetaCuspSourceTerm u n ^ (2 : ℕ)) +
        Real.arccos
          (thetaCuspSourceTerm (u + y) n *
              thetaCuspSourceTerm (u - y) n /
            thetaCuspSourceTerm u n ^ (2 : ℕ)) := by
  rw [
    thetaCuspSourceTerm_reflected_normalized_eq_singleAtomModel hn
      (add_nonneg hx hy) hxyu,
    thetaCuspSourceTerm_reflected_normalized_eq_singleAtomModel hn hx
      ((le_add_of_nonneg_right hy).trans hxyu),
    thetaCuspSourceTerm_reflected_normalized_eq_singleAtomModel hn hy
      ((le_add_of_nonneg_left hx).trans hxyu)]
  exact thetaCuspSingleAtomReflectedCorrelationAngle_subadditive
    hn hx hy hxyu

/-! ## Completed-source transport -/

/-- First jet of the completed reflected atom-plus-likelihood action. -/
def thetaCuspCompletedReflectedCumulantJetOne (u t : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectedActionJetOne
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t)
      (2 * Real.sinh (2 * t)) +
    thetaCuspReflectedLikelihoodCumulantJetOne u t

/-- Second jet of the completed reflected atom-plus-likelihood action. -/
def thetaCuspCompletedReflectedCumulantJetTwo (u t : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectedActionJetTwo
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) +
    thetaCuspReflectedLikelihoodCumulantJetTwo u t

/-- Third jet of the completed reflected atom-plus-likelihood action. -/
def thetaCuspCompletedReflectedCumulantJetThree (u t : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectedActionJetThree
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t)
      (2 * Real.sinh (2 * t)) +
    thetaCuspReflectedLikelihoodCumulantJetThree u t

/-- The previously isolated completed Riccati margin is literally the margin of the named
completed jets. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_jets
    (u t : ℝ) :
    thetaCuspCompletedReflectedCumulantRiccatiMargin u t =
      2 * thetaCuspCompletedReflectedCumulantJetOne u t *
          thetaCuspCompletedReflectedCumulantJetTwo u t -
        thetaCuspCompletedReflectedCumulantJetThree u t := by
  rfl

/-- The completed reflected logarithmic action is strictly positive away from the normalized
seam in the same-half-line chamber. -/
theorem thetaCuspCompletedReflectedCumulantAction_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspCompletedReflectedCumulantAction u t := by
  let ratio :=
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
      thetaCuspFullSource u ^ (2 : ℕ)
  have hden : 0 < thetaCuspFullSource u ^ (2 : ℕ) :=
    sq_pos_of_pos (thetaCuspFullSource_pos_all u)
  have hnum :
      0 < thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) :=
    mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hprod :
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) <
        thetaCuspFullSource (u + 0) * thetaCuspFullSource (u - 0) :=
    strictAntiOn_thetaCuspFullSource_mul_reflect u
      (by norm_num) ht.le ht
  have hratioPos : 0 < ratio := by
    exact div_pos hnum hden
  have hratioLt : ratio < 1 := by
    apply (div_lt_one hden).2
    simpa only [add_zero, sub_zero, pow_two] using hprod
  have hlog : Real.log ratio < 0 := Real.log_neg hratioPos hratioLt
  rw [← neg_log_thetaCuspFullSource_reflected_normalized_eq_completedCumulantAction
    ht.le htu]
  simpa only [ratio] using neg_pos.mpr hlog

/-- Exponentiating the completed action recovers the exact normalized completed-source product. -/
theorem exp_neg_thetaCuspCompletedReflectedCumulantAction
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    Real.exp (-thetaCuspCompletedReflectedCumulantAction u t) =
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
        thetaCuspFullSource u ^ (2 : ℕ) := by
  let ratio :=
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
      thetaCuspFullSource u ^ (2 : ℕ)
  have hratioPos : 0 < ratio := by
    dsimp [ratio]
    exact div_pos
      (mul_pos (thetaCuspFullSource_pos_all _)
        (thetaCuspFullSource_pos_all _))
      (sq_pos_of_pos (thetaCuspFullSource_pos_all u))
  have haction :=
    neg_log_thetaCuspFullSource_reflected_normalized_eq_completedCumulantAction
      ht htu
  rw [← haction]
  simp only [neg_neg]
  exact Real.exp_log hratioPos

/-- A nonnegative completed Riccati margin forces completed-source angle subadditivity on the
same-half-line packet. -/
theorem thetaCuspFullSource_reflectedCorrelationAngle_subadditive_of_margin_nonneg
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u)
    (hmargin : ∀ t ∈ Icc 0 (x + y),
      0 ≤ thetaCuspCompletedReflectedCumulantRiccatiMargin u t) :
    Real.arccos
        (thetaCuspFullSource (u + (x + y)) *
            thetaCuspFullSource (u - (x + y)) /
          thetaCuspFullSource u ^ (2 : ℕ)) ≤
      Real.arccos
          (thetaCuspFullSource (u + x) * thetaCuspFullSource (u - x) /
            thetaCuspFullSource u ^ (2 : ℕ)) +
        Real.arccos
          (thetaCuspFullSource (u + y) * thetaCuspFullSource (u - y) /
            thetaCuspFullSource u ^ (2 : ℕ)) := by
  let q : ℝ → ℝ := thetaCuspCompletedReflectedCumulantAction u
  let q₁ : ℝ → ℝ := thetaCuspCompletedReflectedCumulantJetOne u
  let q₂ : ℝ → ℝ := thetaCuspCompletedReflectedCumulantJetTwo u
  let q₃ : ℝ → ℝ := thetaCuspCompletedReflectedCumulantJetThree u
  have hT : 0 ≤ x + y := add_nonneg hx hy
  have hu : 0 ≤ u := hT.trans hxyu
  have hfactor (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 < thetaCuspSingleAtomReflectionFactor
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (by norm_num) ht.1 (ht.2.trans hxyu)
  have hplus (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (add_nonneg hu ht.1)
  have hminus (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by
      have := ht.2.trans hxyu
      linarith)
  have hq (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q (q₁ t) t := by
    exact (hasDerivAt_thetaCuspSingleAtomReflectedAction
      (hfactor t ht).ne').add
        (hasDerivAt_thetaCuspReflectedLikelihoodCumulantAction
          (hplus t ht) (hminus t ht))
  have hq₁ (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q₁ (q₂ t) t := by
    exact (hasDerivAt_thetaCuspSingleAtomReflectedActionJetOne
      (hfactor t ht).ne').add
        (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne
          (hplus t ht) (hminus t ht))
  have hq₂ (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      HasDerivAt q₂ (q₃ t) t := by
    exact (hasDerivAt_thetaCuspSingleAtomReflectedActionJetTwo
      (hfactor t ht).ne').add
        (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo
          (hplus t ht) (hminus t ht))
  have hqnonneg (t : ℝ) (ht : t ∈ Icc 0 (x + y)) :
      0 ≤ q t := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · simp [q, thetaCuspCompletedReflectedCumulantAction,
        thetaCuspSingleAtomReflectedAction,
        thetaCuspSingleAtomReflectionDefect,
        thetaCuspSingleAtomReflectionFactor,
        thetaCuspReflectedLikelihoodCumulantAction]
      ring_nf
      exact le_rfl
    · exact (thetaCuspCompletedReflectedCumulantAction_pos
        htpos (ht.2.trans hxyu)).le
  have hqpos (t : ℝ) (ht : t ∈ interior (Icc 0 (x + y))) :
      0 < q t := by
    have ht' : t ∈ Icc 0 (x + y) := interior_subset ht
    have htpos : 0 < t := by
      rw [interior_Icc] at ht
      exact ht.1
    exact thetaCuspCompletedReflectedCumulantAction_pos
      htpos (ht'.2.trans hxyu)
  have hangle :=
    HilbertMetric.riccatiCorrelationAngle_subadditive_of_margin_nonneg
      hT (q := q) (q₁ := q₁) (q₂ := q₂) (q₃ := q₃)
      (by
        simp [q, thetaCuspCompletedReflectedCumulantAction,
          thetaCuspSingleAtomReflectedAction,
          thetaCuspSingleAtomReflectionDefect,
          thetaCuspSingleAtomReflectionFactor,
          thetaCuspReflectedLikelihoodCumulantAction]
        ring)
      (by
        simp [q₁, thetaCuspCompletedReflectedCumulantJetOne,
          thetaCuspSingleAtomReflectedActionJetOne,
          thetaCuspSingleAtomReflectionDefect,
          thetaCuspReflectedLikelihoodCumulantJetOne])
      hq hq₁ hq₂ hqnonneg hqpos
      (fun t ht => by
        rw [← thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_jets]
        exact hmargin t ht)
      hx hy le_rfl
  simp only [HilbertMetric.riccatiCorrelationAngle, q] at hangle
  rw [
    exp_neg_thetaCuspCompletedReflectedCumulantAction hT hxyu,
    exp_neg_thetaCuspCompletedReflectedCumulantAction hx
      ((le_add_of_nonneg_right hy).trans hxyu),
    exp_neg_thetaCuspCompletedReflectedCumulantAction hy
      ((le_add_of_nonneg_left hx).trans hxyu)] at hangle
  exact hangle

/-- The exact cumulant lower bound, rather than a free angle hypothesis, is sufficient for the
completed-source angle triangle law. -/
theorem thetaCuspFullSource_reflectedCorrelationAngle_subadditive_of_cumulantCorrection
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u)
    (hcorrection : ∀ t ∈ Icc 0 (x + y),
      -thetaCuspSingleAtomReflectedRiccatiMargin
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) ≤
        thetaCuspReflectedLikelihoodCumulantCorrection u t) :
    Real.arccos
        (thetaCuspFullSource (u + (x + y)) *
            thetaCuspFullSource (u - (x + y)) /
          thetaCuspFullSource u ^ (2 : ℕ)) ≤
      Real.arccos
          (thetaCuspFullSource (u + x) * thetaCuspFullSource (u - x) /
            thetaCuspFullSource u ^ (2 : ℕ)) +
        Real.arccos
          (thetaCuspFullSource (u + y) * thetaCuspFullSource (u - y) /
            thetaCuspFullSource u ^ (2 : ℕ)) := by
  apply thetaCuspFullSource_reflectedCorrelationAngle_subadditive_of_margin_nonneg
    hx hy hxyu
  intro t ht
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_correction]
  linarith [hcorrection t ht]

end

end RHTower
