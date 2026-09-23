import GaloisForLFunctions.RHTower.C5FrozenJetGrowthBound
import GaloisForLFunctions.RHTower.ThetaCuspC5CompletedGateReduction
import GaloisForLFunctions.RHTower.ThetaCuspCompletedCurvatureProjectiveFarTail

/-!
# The frozen-jet growth bound for the completed C5 gate

Instantiation of `C5FrozenJetGrowthBound` with the theta-cusp data: `σ = thetaCuspLogDecaySlope`,
`c = thetaCuspLogCurvature` and its jets.  The corpus jets of the reflected action are exactly
twice the even/odd data, so `H = 4N` and the time jet of `H` is `4M`; the scaling excess is
`G = 4(tM − 5N)`.  The growth bound `5|G| < 12 Φ (−H)` then follows from the component bounds
once the explicit numeric key inequality holds, and the gate `M(1) > 0` follows.
-/

open Set

namespace RHTower

/-- `c⁽⁴⁾ = −ℓ⁽⁶⁾`. -/
noncomputable def thetaCuspLogCurvatureJetFour (x : ℝ) : ℝ := -iteratedDeriv 6 thetaCuspLogSource x

/-- `c⁽⁵⁾ = −ℓ⁽⁷⁾`. -/
noncomputable def thetaCuspLogCurvatureJetFive (x : ℝ) : ℝ := -iteratedDeriv 7 thetaCuspLogSource x

theorem hasDerivAt_thetaCuspLogCurvatureJetThree (x : ℝ) :
    HasDerivAt thetaCuspLogCurvatureJetThree (thetaCuspLogCurvatureJetFour x) x := by
  unfold thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJetFour
  exact (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).neg

theorem hasDerivAt_thetaCuspLogCurvatureJetFour (x : ℝ) :
    HasDerivAt thetaCuspLogCurvatureJetFour (thetaCuspLogCurvatureJetFive x) x := by
  unfold thetaCuspLogCurvatureJetFour thetaCuspLogCurvatureJetFive
  exact (hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x).neg

/-- `H = 4 N`. -/
theorem centerNumerator_eq_four_fjN (u t : ℝ) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t =
      4 * fjN thetaCuspLogDecaySlope thetaCuspLogCurvature u t := by
  unfold thetaCuspReflectedActionVelocityFixedActionCenterNumerator fjN fjOdd fjEven fjE fjO
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo thetaCuspReflectedLogCenterJetOne
    thetaCuspReflectedLogCenterMixedJetOne
  ring

/-- The time jet of `H` is `4 M`. -/
theorem timeJet_eq_four_fjM (u t : ℝ) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t =
      4 * fjM thetaCuspLogDecaySlope thetaCuspLogCurvature thetaCuspLogCurvatureJet u t := by
  unfold thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet fjM fjOdd fjEven fjE fjO
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo thetaCuspReflectedLogJetThree
    thetaCuspReflectedLogCenterJetOne thetaCuspReflectedLogCenterMixedJetThree
  ring

/-- `G = 4 (tM − 5N)`. -/
theorem scalingExcess_eq_four (u t : ℝ) :
    c5CompletedScalingExcess u t =
      4 * (t * fjM thetaCuspLogDecaySlope thetaCuspLogCurvature thetaCuspLogCurvatureJet u t -
        5 * fjN thetaCuspLogDecaySlope thetaCuspLogCurvature u t) := by
  unfold c5CompletedScalingExcess
  rw [timeJet_eq_four_fjM, centerNumerator_eq_four_fjN]
  ring

/-- `Φ' = 2E` in the frozen-jet notation. -/
theorem hasDerivAt_reflectedLogAction_fjE (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogAction u) (2 * fjE thetaCuspLogDecaySlope u t) t := by
  have := hasDerivAt_thetaCuspReflectedLogAction u t
  convert this using 1
  unfold fjE thetaCuspReflectedLogJetOne
  ring

theorem reflectedLogAction_zero (u : ℝ) : thetaCuspReflectedLogAction u 0 = 0 := by
  unfold thetaCuspReflectedLogAction
  simp
  ring

/-- Lower bound for `Φ` from the frozen jets. -/
theorem reflectedLogAction_frozen_bound {u t S₄ S₅ : ℝ} (ht : 0 ≤ t)
    (hS₄ : ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFour x| ≤ S₄)
    (hS₅ : ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFive x| ≤ S₅) :
    |thetaCuspReflectedLogAction u t -
      (thetaCuspLogCurvature u * t ^ (2 : ℕ) + thetaCuspLogCurvatureJetTwo u * t ^ (4 : ℕ) / 12)| ≤
      S₄ * t ^ (6 : ℕ) / 360 := by
  have hE : ∀ s ∈ Icc (0 : ℝ) t,
      |fjE thetaCuspLogDecaySlope u s - thetaCuspLogCurvature u * s -
        thetaCuspLogCurvatureJetTwo u * s ^ (3 : ℕ) / 6| ≤ S₄ * s ^ (5 : ℕ) / 120 := by
    intro s hs
    have hS₄' : ∀ x ∈ Icc (u - s) (u + s), |thetaCuspLogCurvatureJetFour x| ≤ S₄ := fun x hx =>
      hS₄ x ⟨by linarith [hx.1, hs.2], by linarith [hx.2, hs.2]⟩
    have hS₅' : ∀ x ∈ Icc (u - s) (u + s), |thetaCuspLogCurvatureJetFive x| ≤ S₅ := fun x hx =>
      hS₅ x ⟨by linarith [hx.1, hs.2], by linarith [hx.2, hs.2]⟩
    exact (fj_component_bounds hs.1 hasDerivAt_thetaCuspLogDecaySlope hasDerivAt_thetaCuspLogCurvature
      hasDerivAt_thetaCuspLogCurvatureJet hasDerivAt_thetaCuspLogCurvatureJetTwo
      hasDerivAt_thetaCuspLogCurvatureJetThree hasDerivAt_thetaCuspLogCurvatureJetFour
      hS₄' hS₅').2.2.2.2.1
  have key := abs_le_pow_div_of_abs_deriv_le (K := S₄ / 60) (k := 5) ht
    (h := fun s => thetaCuspReflectedLogAction u s -
      (thetaCuspLogCurvature u * s ^ (2 : ℕ) + thetaCuspLogCurvatureJetTwo u * s ^ (4 : ℕ) / 12))
    (h' := fun s => 2 * (fjE thetaCuspLogDecaySlope u s - thetaCuspLogCurvature u * s -
      thetaCuspLogCurvatureJetTwo u * s ^ (3 : ℕ) / 6)) (by simp [reflectedLogAction_zero]) ?_ ?_ t
    ⟨ht, le_rfl⟩
  · calc _ ≤ S₄ / 60 * t ^ (5 + 1) / (5 + 1) := key
      _ = S₄ * t ^ (6 : ℕ) / 360 := by ring
  · intro s _
    have h1 := hasDerivAt_reflectedLogAction_fjE u s
    have h2 := ((hasDerivAt_pow 2 s).const_mul (thetaCuspLogCurvature u)).add
      (((hasDerivAt_pow 4 s).const_mul (thetaCuspLogCurvatureJetTwo u)).div_const 12)
    have := h1.sub h2
    convert this using 1 <;> first | rfl | (push_cast; ring)
  · intro s hs
    have := hE s hs
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc 2 * |fjE thetaCuspLogDecaySlope u s - thetaCuspLogCurvature u * s -
          thetaCuspLogCurvatureJetTwo u * s ^ (3 : ℕ) / 6| ≤ 2 * (S₄ * s ^ (5 : ℕ) / 120) := by gcongr
      _ = S₄ / 60 * s ^ (5 : ℕ) := by ring

/-- **Strict assembly.**  `5|G| < 12Φ(−H)` (with `H < 0`, `2Φ ≤ v`) gives `M(1) > 0`. -/
theorem c5CompletedCompensationMargin_pos_of_strict_bounds {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hH : thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0)
    (hv : 2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t)
    (hG : 5 * |c5CompletedScalingExcess u t| <
      12 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t)) :
    0 < c5CompletedCompensationMargin u t := by
  have hΦ : 0 < thetaCuspReflectedLogAction u t := thetaCuspReflectedLogAction_pos ht
  rw [c5CompletedCompensationMargin_eq_excess_form ht htu]
  have hW := twelve_mul_action_le_boseWeight_sub_thirty hΦ hv
  have hHpos : 0 < -thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t := by linarith
  have h1 : 12 * thetaCuspReflectedLogAction u t *
      (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) ≤
      (c5CompletedBoseWeight u t - 30) *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) :=
    mul_le_mul_of_nonneg_right hW hHpos.le
  have h2 := (abs_le.mp (le_refl |c5CompletedScalingExcess u t|)).1
  linarith

/-- **The frozen-jet growth bound.**  With the jets `c₀ … c₃` of the curvature at `u`, sup-norms
`S₄, S₅` of `c⁽⁴⁾, c⁽⁵⁾` on `[u−t, u+t]`, and the explicit numeric key inequality, the scaling
excess is dominated: `5|G| < 12Φ(−H)`. -/
theorem growthBound_of_frozenJets {u t S₄ S₅ : ℝ} (ht : 0 < t)
    (hS₄ : ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFour x| ≤ S₄)
    (hS₅ : ∀ x ∈ Icc (u - t) (u + t), |thetaCuspLogCurvatureJetFive x| ≤ S₅)
    (hElow : 0 ≤ thetaCuspLogCurvature u * t + thetaCuspLogCurvatureJetTwo u * t ^ (3 : ℕ) / 6 -
      S₄ * t ^ (5 : ℕ) / 120)
    (hOlow : 0 ≤ thetaCuspLogCurvatureJet u * t ^ (2 : ℕ) / 2 + thetaCuspLogCurvatureJetThree u * t ^ (4 : ℕ) / 24 -
      S₅ * t ^ (6 : ℕ) / 720)
    (hYlow : 0 ≤ thetaCuspLogCurvatureJetTwo u * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30)
    (hΛup : 0 ≤ thetaCuspLogCurvatureJetThree u * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180)
    (hΦlow : 0 ≤ thetaCuspLogCurvature u * t ^ (2 : ℕ) + thetaCuspLogCurvatureJetTwo u * t ^ (4 : ℕ) / 12 -
      S₄ * t ^ (6 : ℕ) / 360)
    (hkey : 5 * ((thetaCuspLogCurvature u * t + |thetaCuspLogCurvatureJetTwo u| * t ^ (3 : ℕ) / 6 +
          S₄ * t ^ (5 : ℕ) / 120) * (2 / 45 * S₅ * t ^ (6 : ℕ)) +
        (thetaCuspLogCurvatureJet u * t ^ (2 : ℕ) / 2 + |thetaCuspLogCurvatureJetThree u| * t ^ (4 : ℕ) / 24 +
          S₅ * t ^ (6 : ℕ) / 720) * (2 / 15 * S₄ * t ^ (5 : ℕ))) <
      12 * (thetaCuspLogCurvature u * t ^ (2 : ℕ) + thetaCuspLogCurvatureJetTwo u * t ^ (4 : ℕ) / 12 -
          S₄ * t ^ (6 : ℕ) / 360) *
        ((thetaCuspLogCurvatureJet u * t ^ (2 : ℕ) / 2 + thetaCuspLogCurvatureJetThree u * t ^ (4 : ℕ) / 24 -
            S₅ * t ^ (6 : ℕ) / 720) *
          (thetaCuspLogCurvatureJetTwo u * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30) -
        (thetaCuspLogCurvature u * t + |thetaCuspLogCurvatureJetTwo u| * t ^ (3 : ℕ) / 6 +
            S₄ * t ^ (5 : ℕ) / 120) *
          (thetaCuspLogCurvatureJetThree u * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180))) :
    5 * |c5CompletedScalingExcess u t| <
      12 * thetaCuspReflectedLogAction u t *
        (-thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t) := by
  obtain ⟨hK₁, hK₂, hΛ, hY, hE, hO⟩ := fj_component_bounds ht.le hasDerivAt_thetaCuspLogDecaySlope
    hasDerivAt_thetaCuspLogCurvature hasDerivAt_thetaCuspLogCurvatureJet
    hasDerivAt_thetaCuspLogCurvatureJetTwo hasDerivAt_thetaCuspLogCurvatureJetThree
    hasDerivAt_thetaCuspLogCurvatureJetFour hS₄ hS₅
  have hΦ := reflectedLogAction_frozen_bound ht.le hS₄ hS₅
  rw [scalingExcess_eq_four, centerNumerator_eq_four_fjN, fj_excess_eq, fjN_eq]
  have hS₄0 : 0 ≤ S₄ := le_trans (abs_nonneg _) (hS₄ u ⟨by linarith, by linarith⟩)
  have hS₅0 : 0 ≤ S₅ := le_trans (abs_nonneg _) (hS₅ u ⟨by linarith, by linarith⟩)
  have ht3 : 0 ≤ t ^ (3 : ℕ) := by positivity
  have ht4 : 0 ≤ t ^ (4 : ℕ) := by positivity
  have ht5 : 0 ≤ t ^ (5 : ℕ) := by positivity
  have ht6 : 0 ≤ t ^ (6 : ℕ) := by positivity
  have hc₂abs := mul_le_mul_of_nonneg_right (le_abs_self (thetaCuspLogCurvatureJetTwo u)) ht3
  have hc₂abs' := mul_le_mul_of_nonneg_right (neg_abs_le (thetaCuspLogCurvatureJetTwo u)) ht3
  have hc₃abs := mul_le_mul_of_nonneg_right (le_abs_self (thetaCuspLogCurvatureJetThree u)) ht4
  -- names
  generalize hEdef : fjE thetaCuspLogDecaySlope u t = E at hE ⊢
  generalize hOdef : fjO thetaCuspLogDecaySlope u t = O at hO ⊢
  generalize hK₁def : fjK₁ thetaCuspLogDecaySlope thetaCuspLogCurvature thetaCuspLogCurvatureJet u t =
    K₁ at hK₁ ⊢
  generalize hK₂def : fjK₂ thetaCuspLogDecaySlope thetaCuspLogCurvature thetaCuspLogCurvatureJet u t =
    K₂ at hK₂ ⊢
  generalize hΛdef : fjLam thetaCuspLogDecaySlope thetaCuspLogCurvature u t = Λ at hΛ ⊢
  generalize hYdef : fjY thetaCuspLogDecaySlope thetaCuspLogCurvature u t = Y at hY ⊢
  generalize hΦdef : thetaCuspReflectedLogAction u t = Φ at hΦ ⊢
  generalize hc0 : thetaCuspLogCurvature u = c₀ at *
  generalize hc1 : thetaCuspLogCurvatureJet u = c₁ at *
  generalize hc2 : thetaCuspLogCurvatureJetTwo u = c₂ at *
  generalize hc3 : thetaCuspLogCurvatureJetThree u = c₃ at *
  have hE' := abs_le.mp hE
  have hO' := abs_le.mp hO
  have hΛ' := abs_le.mp hΛ
  have hY' := abs_le.mp hY
  have hΦ' := abs_le.mp hΦ
  generalize hEup : c₀ * t + |c₂| * t ^ (3 : ℕ) / 6 + S₄ * t ^ (5 : ℕ) / 120 = Eup at *
  generalize hOup : c₁ * t ^ (2 : ℕ) / 2 + |c₃| * t ^ (4 : ℕ) / 24 + S₅ * t ^ (6 : ℕ) / 720 = Oup at *
  generalize hOlowE : c₁ * t ^ (2 : ℕ) / 2 + c₃ * t ^ (4 : ℕ) / 24 - S₅ * t ^ (6 : ℕ) / 720 = Olow at *
  generalize hYlowE : c₂ * t ^ (3 : ℕ) / 3 - S₄ * t ^ (5 : ℕ) / 30 = Ylow at *
  generalize hΛupE : c₃ * t ^ (4 : ℕ) / 12 + S₅ * t ^ (6 : ℕ) / 180 = Λup at *
  generalize hΦlowE : c₀ * t ^ (2 : ℕ) + c₂ * t ^ (4 : ℕ) / 12 - S₄ * t ^ (6 : ℕ) / 360 = Φlow at *
  have hEle : E ≤ Eup := by linarith only [hE'.2, hc₂abs, hEup]
  have hEge : 0 ≤ E := by linarith only [hE'.1, hc₂abs', hElow]
  have hOle : O ≤ Oup := by linarith only [hO'.2, hc₃abs, hOup]
  have hOge : Olow ≤ O := by linarith only [hO'.1, hOlowE]
  have hYge : Ylow ≤ Y := by linarith only [hY'.1, hYlowE]
  have hΛle : Λ ≤ Λup := by linarith only [hΛ'.2, hΛupE]
  have hΦge : Φlow ≤ Φ := by linarith only [hΦ'.1, hΦlowE]
  have hOge0 : 0 ≤ O := le_trans hOlow hOge
  have hYge0 : 0 ≤ Y := le_trans hYlow hYge
  have hEup0 : 0 ≤ Eup := le_trans hEge hEle
  have hOup0 : 0 ≤ Oup := le_trans hOge0 hOle
  -- `−N ≥ Olow·Ylow − Eup·Λup`
  have h1 : Olow * Ylow ≤ O * Y := mul_le_mul hOge hYge hYlow hOge0
  have h2 : E * Λ ≤ Eup * Λup := by
    calc E * Λ ≤ E * Λup := mul_le_mul_of_nonneg_left hΛle hEge
      _ ≤ Eup * Λup := mul_le_mul_of_nonneg_right hEle hΛup
  have hN : Olow * Ylow - Eup * Λup ≤ O * Y - E * Λ := by linarith only [h1, h2]
  -- `|ε| ≤ Eup·(2/45)S₅t⁶ + Oup·(2/15)S₄t⁵`
  have hb1 : 0 ≤ 2 / 45 * S₅ * t ^ (6 : ℕ) := by positivity
  have hb2 : 0 ≤ 2 / 15 * S₄ * t ^ (5 : ℕ) := by positivity
  have hεK₁ : E * |K₁| ≤ Eup * (2 / 45 * S₅ * t ^ (6 : ℕ)) := mul_le_mul hEle hK₁ (abs_nonneg _) hEup0
  have hεK₂ : O * |K₂| ≤ Oup * (2 / 15 * S₄ * t ^ (5 : ℕ)) := mul_le_mul hOle hK₂ (abs_nonneg _) hOup0
  have hε : |E * K₁ + O * K₂| ≤ Eup * (2 / 45 * S₅ * t ^ (6 : ℕ)) + Oup * (2 / 15 * S₄ * t ^ (5 : ℕ)) := by
    calc |E * K₁ + O * K₂| ≤ |E * K₁| + |O * K₂| := abs_add_le _ _
      _ = E * |K₁| + O * |K₂| := by rw [abs_mul, abs_mul, abs_of_nonneg hEge, abs_of_nonneg hOge0]
      _ ≤ Eup * (2 / 45 * S₅ * t ^ (6 : ℕ)) + Oup * (2 / 15 * S₄ * t ^ (5 : ℕ)) := by
          linarith only [hεK₁, hεK₂]
  -- assemble
  have hεnn : 0 ≤ Eup * (2 / 45 * S₅ * t ^ (6 : ℕ)) + Oup * (2 / 15 * S₄ * t ^ (5 : ℕ)) := by positivity
  have hNlow : 0 < Olow * Ylow - Eup * Λup := by
    by_contra hcon
    have hcon' : Olow * Ylow - Eup * Λup ≤ 0 := not_lt.mp hcon
    have : 12 * Φlow * (Olow * Ylow - Eup * Λup) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon'
    linarith only [hkey, hεnn, this]
  have hprod : 12 * Φlow * (Olow * Ylow - Eup * Λup) ≤ 12 * Φ * (O * Y - E * Λ) := by
    have := mul_le_mul hΦge hN hNlow.le (le_trans hΦlow hΦge)
    linarith only [this]
  have habs4 : |4 * (E * K₁ + O * K₂)| = 4 * |E * K₁ + O * K₂| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  rw [habs4]
  have hfin : 12 * Φ * -(4 * (E * Λ - O * Y)) = 4 * (12 * Φ * (O * Y - E * Λ)) := by ring
  rw [hfin]
  linarith only [hε, hkey, hprod]

end RHTower
