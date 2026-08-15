/-
Exact RH classification of the cofinal outer-power window interfaces.

Both interfaces quantify analytic witnesses only over `boxZeros T`.  Under RH every such set is
empty, so the window data hold vacuously at every height.  Combined with their existing forward
implications, this identifies each cofinal supply with RH and removes it as an independent
mathematical premise.
-/
import GaloisForLFunctions.RHTower.CarrierMassFloor

namespace RHTower

/-- A line package exists exactly when its indexing window has no right-half zeros. -/
theorem windowLinePackage_iff_boxZeros_empty (T : ℝ) :
    WindowLinePackage T ↔ boxZeros T = ∅ := by
  constructor
  · exact boxZeros_empty_of_windowLinePackage
  · intro hempty ρ hρ
    rw [hempty] at hρ
    exact (Set.notMem_empty ρ hρ).elim

/-- Cofinal line packages are exactly RH. -/
theorem cofinalWindowLinePackages_iff_riemannHypothesis :
    (∀ B : ℝ, ∃ T, B ≤ T ∧ WindowLinePackage T) ↔ RiemannHypothesis := by
  constructor
  · exact rh_of_cofinal_windowLinePackages
  · intro hRH B
    refine ⟨B, le_rfl, (windowLinePackage_iff_boxZeros_empty B).mpr ?_⟩
    exact (rh_iff_forall_boxZeros_empty.mp hRH) B

/-- The second-moment outer-power interface is exactly zero-freeness of its indexing window. -/
theorem secondMomentOrthogonalSavingOuterPowerWindowData_iff_boxZeros_empty (T : ℝ) :
    SecondMomentOrthogonalSavingOuterPowerWindowData T ↔ boxZeros T = ∅ := by
  constructor
  · intro hdata
    exact boxZeros_empty_of_windowLinePackage
      (windowLinePackage_of_secondMoment_orthogonal_saving_outer_power_endpoint_target hdata)
  · intro hempty ρ hρ
    rw [hempty] at hρ
    exact (Set.notMem_empty ρ hρ).elim

/-- Cofinal second-moment outer-power data are exactly RH. -/
theorem cofinalSecondMomentOrthogonalSavingOuterPowerWindowData_iff_riemannHypothesis :
    (∀ B : ℝ, ∃ T, B ≤ T ∧ SecondMomentOrthogonalSavingOuterPowerWindowData T) ↔
      RiemannHypothesis := by
  constructor
  · intro hdata
    apply rh_of_cofinal_windowLinePackages
    intro B
    obtain ⟨T, hBT, hT⟩ := hdata B
    exact ⟨T, hBT,
      windowLinePackage_of_secondMoment_orthogonal_saving_outer_power_endpoint_target hT⟩
  · intro hRH B
    refine ⟨B, le_rfl,
      (secondMomentOrthogonalSavingOuterPowerWindowData_iff_boxZeros_empty B).mpr ?_⟩
    exact (rh_iff_forall_boxZeros_empty.mp hRH) B

/-- RH supplies anchor-mass outer-power data at every height because every RH box is zero-free. -/
theorem anchorMassOuterPowerWindowData_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) :
    AnchorMassOuterPowerWindowData T := by
  intro ρ hρ
  have hempty : boxZeros T = ∅ := (rh_iff_forall_boxZeros_empty.mp hRH) T
  have : False := by
    rw [hempty] at hρ
    exact Set.notMem_empty ρ hρ
  exact this.elim

/-- Anchor-mass outer-power data are exactly zero-freeness of their indexing window. -/
theorem anchorMassOuterPowerWindowData_iff_boxZeros_empty (T : ℝ) :
    AnchorMassOuterPowerWindowData T ↔ boxZeros T = ∅ := by
  constructor
  · intro hdata
    exact boxZeros_empty_of_windowLinePackage
      (windowLinePackage_of_anchor_mass_outer_power_windowData hdata)
  · intro hempty ρ hρ
    rw [hempty] at hρ
    exact (Set.notMem_empty ρ hρ).elim

/-- The cofinal anchor-mass window interface is exactly RH. -/
theorem cofinalAnchorMassOuterPowerWindowData_iff_riemannHypothesis :
    CofinalAnchorMassOuterPowerWindowData ↔ RiemannHypothesis := by
  constructor
  · exact rh_of_cofinal_anchor_mass_outer_power_windowData
  · intro hRH B
    exact ⟨B, le_rfl, anchorMassOuterPowerWindowData_of_riemannHypothesis hRH B⟩

/-- RH supplies integral-ledger outer-power data at every height because every RH box is zero-free. -/
theorem integralLedgerOuterPowerWindowData_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) :
    IntegralLedgerOuterPowerWindowData T := by
  intro ρ hρ
  have hempty : boxZeros T = ∅ := (rh_iff_forall_boxZeros_empty.mp hRH) T
  have : False := by
    rw [hempty] at hρ
    exact Set.notMem_empty ρ hρ
  exact this.elim

/-- Integral-ledger outer-power data are exactly zero-freeness of their indexing window. -/
theorem integralLedgerOuterPowerWindowData_iff_boxZeros_empty (T : ℝ) :
    IntegralLedgerOuterPowerWindowData T ↔ boxZeros T = ∅ := by
  constructor
  · intro hdata
    exact boxZeros_empty_of_windowLinePackage
      (windowLinePackage_of_integral_ledger_outer_power_windowData hdata)
  · intro hempty ρ hρ
    rw [hempty] at hρ
    exact (Set.notMem_empty ρ hρ).elim

/-- The cofinal integral-ledger window interface is exactly RH. -/
theorem cofinalIntegralLedgerOuterPowerWindowData_iff_riemannHypothesis :
    CofinalIntegralLedgerOuterPowerWindowData ↔ RiemannHypothesis := by
  constructor
  · exact rh_of_cofinal_integral_ledger_outer_power_windowData
  · intro hRH B
    exact ⟨B, le_rfl, integralLedgerOuterPowerWindowData_of_riemannHypothesis hRH B⟩

/-- The second-moment outer-power interface is inhabited at the empty height window. -/
theorem secondMomentOrthogonalSavingOuterPowerWindowData_zero :
    SecondMomentOrthogonalSavingOuterPowerWindowData (0 : ℝ) :=
  (secondMomentOrthogonalSavingOuterPowerWindowData_iff_boxZeros_empty 0).mpr
    (boxZeros_eq_empty_of_nonpos le_rfl)

/-- The anchor-mass outer-power interface is inhabited at the empty height window. -/
theorem anchorMassOuterPowerWindowData_zero :
    AnchorMassOuterPowerWindowData (0 : ℝ) :=
  (anchorMassOuterPowerWindowData_iff_boxZeros_empty 0).mpr
    (boxZeros_eq_empty_of_nonpos le_rfl)

/-- The integral-ledger outer-power interface is inhabited at the empty height window. -/
theorem integralLedgerOuterPowerWindowData_zero :
    IntegralLedgerOuterPowerWindowData (0 : ℝ) :=
  (integralLedgerOuterPowerWindowData_iff_boxZeros_empty 0).mpr
    (boxZeros_eq_empty_of_nonpos le_rfl)

end RHTower
