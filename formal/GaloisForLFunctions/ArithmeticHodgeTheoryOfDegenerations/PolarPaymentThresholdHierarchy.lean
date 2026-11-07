import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# The Polar Payment Threshold Hierarchy

At critical overlap ratios `1 ≤ c`, `c⁸ ≤ R log N`, let `polarPaymentCriticalThreshold` denote the
supremum in `EReal` of positive ratios `R > 0` at which the low-packet Schur / polar capacity
inequality `PolarPaymentAt R A` holds on every compact terminal window `[-A, 0]` (`A ≥ 0`):
`generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R ≤ windowPencil R (halfWeight h)`.

Combining `polarPaymentAt_of_lt_criticalNonnegativityThreshold`,
`le_windowThreshold_of_polarPaymentAt`, and `highConductorCriticalThreshold_eq_iInf_windowThreshold`
places `polarPaymentCriticalThreshold` inside the critical positivity threshold chain:

`0 < criticalPositivityThreshold ≤ criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold`
`  ≤ highConductorCriticalThreshold = ⨅ A ≥ 0, windowThreshold A`,

with equality with `⊤` at every stage equivalent to `onsetAperture zetaZeroConfig = ⊤` and to
`RiemannHypothesis`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Zeta23 RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CriticalArithmeticCorrelationTheory CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
  WindowVisibilityLaw

/-- **The polar-payment critical threshold `R_c^{polar}(ζ)`**: the supremum in `EReal` of ratios
`R > 0` at which every compact terminal window `[-A, 0]` (`A ≥ 0`) pays the `m = 1` polar capacity
`generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R` out of `windowPencil R (halfWeight h)`. -/
def polarPaymentCriticalThreshold : EReal :=
  sSup ((fun R : ℝ => (R : EReal)) '' {R : ℝ | 0 < R ∧ ∀ A : ℝ, 0 ≤ A → PolarPaymentAt R A})

/-- Certified positive floor `0 < polarPaymentCriticalThreshold`. -/
theorem polarPaymentCriticalThreshold_pos : (0 : EReal) < polarPaymentCriticalThreshold := by
  obtain ⟨R₀, hR₀, hpay⟩ := exists_polarPaymentAt_on_every_window
  exact (EReal.coe_pos.mpr hR₀).trans_le (le_sSup ⟨R₀, ⟨hR₀, hpay R₀ hR₀ le_rfl⟩, rfl⟩)

/-- Whole-space critical nonnegativity implies polar payment on all compact terminal windows:
`criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold`. -/
theorem criticalNonnegativityThreshold_le_polarPaymentCriticalThreshold :
    criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold := by
  refine sSup_le ?_
  rintro _ ⟨R, ⟨hR, hnn⟩, rfl⟩
  have hle_thr : (R : EReal) ≤ criticalNonnegativityThreshold := le_sSup ⟨R, ⟨hR, hnn⟩, rfl⟩
  refine le_of_forall_lt fun c hc => ?_
  rcases le_or_gt c 0 with hc0 | hc0
  · exact lt_of_le_of_lt hc0 polarPaymentCriticalThreshold_pos
  · lift c to ℝ using ⟨(lt_trans EReal.bot_lt_zero hc0).ne', (hc.trans (EReal.coe_lt_top R)).ne⟩
    have hc_pos : 0 < c := EReal.coe_pos.mp hc0
    have hcR : c < R := EReal.coe_lt_coe_iff.mp hc
    set r : ℝ := (c + R) / 2
    have hr_pos : 0 < r := by dsimp only [r]; linarith
    have hcr : (c : EReal) < (r : EReal) := EReal.coe_lt_coe_iff.mpr (by dsimp only [r]; linarith)
    have hrR : (r : EReal) < criticalNonnegativityThreshold :=
      (EReal.coe_lt_coe_iff.mpr (by dsimp only [r]; linarith)).trans_le hle_thr
    exact hcr.trans_le (le_sSup ⟨r, ⟨hr_pos, fun A hA =>
      polarPaymentAt_of_lt_criticalNonnegativityThreshold hr_pos hA hrR⟩, rfl⟩)

/-- `criticalPositivityThreshold ≤ polarPaymentCriticalThreshold`. -/
theorem criticalPositivityThreshold_le_polarPaymentCriticalThreshold :
    criticalPositivityThreshold ≤ polarPaymentCriticalThreshold :=
  criticalPositivityThreshold_le_criticalNonnegativityThreshold.trans
    criticalNonnegativityThreshold_le_polarPaymentCriticalThreshold

/-- Polar payment on every window bounds the ratio by the infimum of continuum window thresholds:
`polarPaymentCriticalThreshold ≤ ⨅ A ≥ 0, windowThreshold A`. -/
theorem polarPaymentCriticalThreshold_le_iInf_windowThreshold :
    polarPaymentCriticalThreshold ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
  refine sSup_le ?_
  rintro _ ⟨R, ⟨hR, hpay⟩, rfl⟩
  exact le_iInf fun A => le_iInf fun hA => le_windowThreshold_of_polarPaymentAt hR (hpay A hA)

/-- Polar payment sits below the high-conductor critical positivity threshold:
`polarPaymentCriticalThreshold ≤ highConductorCriticalThreshold`. -/
theorem polarPaymentCriticalThreshold_le_highConductorCriticalThreshold :
    polarPaymentCriticalThreshold ≤ highConductorCriticalThreshold := by
  rw [highConductorCriticalThreshold_eq_iInf_windowThreshold]
  exact polarPaymentCriticalThreshold_le_iInf_windowThreshold

/-- **The critical threshold hierarchy.** -/
theorem criticalThreshold_hierarchy :
    (0 : EReal) < criticalPositivityThreshold ∧
      criticalPositivityThreshold ≤ criticalNonnegativityThreshold ∧
      criticalNonnegativityThreshold ≤ polarPaymentCriticalThreshold ∧
      polarPaymentCriticalThreshold ≤ highConductorCriticalThreshold ∧
      highConductorCriticalThreshold = ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A :=
  ⟨criticalPositivityThreshold_pos,
   criticalPositivityThreshold_le_criticalNonnegativityThreshold,
   criticalNonnegativityThreshold_le_polarPaymentCriticalThreshold,
   polarPaymentCriticalThreshold_le_highConductorCriticalThreshold,
   highConductorCriticalThreshold_eq_iInf_windowThreshold⟩

/-- `polarPaymentCriticalThreshold = ⊤` if and only if `RiemannHypothesis`. -/
theorem polarPaymentCriticalThreshold_eq_top_iff_riemannHypothesis :
    polarPaymentCriticalThreshold = ⊤ ↔ RiemannHypothesis :=
  ⟨fun htop => riemannHypothesis_iff_windowThreshold_eq_top.mpr fun A hA => top_le_iff.mp <|
    calc (⊤ : EReal)
        = polarPaymentCriticalThreshold := htop.symm
      _ ≤ ⨅ (B : ℝ) (_ : 0 ≤ B), windowThreshold B :=
          polarPaymentCriticalThreshold_le_iInf_windowThreshold
      _ ≤ windowThreshold A := iInf_le_of_le A (iInf_le _ hA),
   fun hRH => top_le_iff.mp
     (criticalPositivityThreshold_eq_top_of_riemannHypothesis hRH ▸
       criticalPositivityThreshold_le_polarPaymentCriticalThreshold)⟩

/-- `polarPaymentCriticalThreshold = ⊤` if and only if `onsetAperture zetaZeroConfig = ⊤`. -/
theorem polarPaymentCriticalThreshold_eq_top_iff_onsetAperture_eq_top :
    polarPaymentCriticalThreshold = ⊤ ↔ onsetAperture zetaZeroConfig = ⊤ :=
  polarPaymentCriticalThreshold_eq_top_iff_riemannHypothesis.trans
    riemannHypothesis_iff_onsetAperture_zeta_eq_top

#print axioms polarPaymentCriticalThreshold_pos
#print axioms criticalNonnegativityThreshold_le_polarPaymentCriticalThreshold
#print axioms polarPaymentCriticalThreshold_le_highConductorCriticalThreshold
#print axioms criticalThreshold_hierarchy
#print axioms polarPaymentCriticalThreshold_eq_top_iff_riemannHypothesis
#print axioms polarPaymentCriticalThreshold_eq_top_iff_onsetAperture_eq_top

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
