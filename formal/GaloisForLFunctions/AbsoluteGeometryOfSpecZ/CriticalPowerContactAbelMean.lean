import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerCombGrowthDetectsRH
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactDirichletSymbol
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactSymbolIsRegularAtZero
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelIntegrability

/-!
# The actual Abel mean of the critical harmonic contacts

Under RH the harmonic contacts are subpolynomial. Their restored Mellin
transform is therefore holomorphic on the right half-plane and has the
actual contact symbol. The literal logarithmic Abel mean is the symbol
after its forced real pole is subtracted.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- Subpolynomial critical contacts provide the restored transform's
holomorphy without ordinary convergence. -/
theorem differentiableOn_criticalPowerContactMellin_of_rh
    (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ criticalPowerContactMellin {s : ℂ | 0 < s.re} := by
  have hg := strictGrowth_criticalHarmonicContacts_iff_rh.mpr hRH
  have hΦ := differentiableOn_complexMellinPairing_of_strict_power_growth
    criticalHarmonicContacts_zero (le_refl (0 : ℝ)) hg
  refine hΦ.add ?_
  intro s hs
  have hs1 : s + 1 ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re, one_re] at hr
    change 0 < s.re at hs
    linarith only [hr, hs]
  exact (((differentiableAt_riemannZeta hs1).comp s
    (differentiableAt_id.add_const 1)).const_mul _).differentiableWithinAt

private theorem criticalPowerContactMellin_initial_of_rh
    (hRH : RiemannHypothesis) {s : ℂ} (hs : 2 < s.re) :
    criticalPowerContactMellin s = riemannZeta (s + 1) * criticalPowerContactFactor s := by
  obtain ⟨C, hC, hb⟩ := (strictGrowth_criticalHarmonicContacts_iff_rh.mpr hRH) 1 (by norm_num)
  have hb' : ∀ N : ℕ, |criticalHarmonicContacts N| ≤ C * (N : ℝ) ^ (1 : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [criticalHarmonicContacts_zero, abs_zero]
      positivity
    · simpa only [zero_add] using hb N hN
  simpa [criticalPowerContactFactor] using
    criticalPowerContactMellin_initial_of_power_bound hC hb' hs (by linarith only [hs])

/-- RH continues the actual critical contact symbol to its full open
half-plane through subpolynomial growth. -/
theorem criticalPowerContactMellin_eq_of_rh
    (hRH : RiemannHypothesis) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s + 1 / 2 ≠ 1) (hζ : riemannZeta (s + 1 / 2) ≠ 0) :
    criticalPowerContactMellin s = riemannZeta (s + 1) * criticalPowerContactFactor s := by
  have hh := contactSymbol_eq_of_holomorphic (a := 1 / 2) (by norm_num)
    (F := criticalPowerContactMellin)
    (by simpa using differentiableOn_criticalPowerContactMellin_of_rh hRH)
    (fun z hz => by simpa [criticalPowerContactFactor] using
      criticalPowerContactMellin_initial_of_rh hRH hz)
    (s := s) (by simpa using hs) (by simpa using hs1) (by simpa using hζ)
  simpa [criticalPowerContactFactor] using hh

/-- On the positive real ray near zero, the actual harmonic-contact
Abel mean is the critical symbol with its real residue removed. -/
theorem logarithmicAbelMean_criticalHarmonicContacts_eq_of_rh
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    logarithmicAbelMean criticalHarmonicContacts ε =
      riemannZeta ((ε : ℂ) + 1) *
        (criticalPowerContactFactor (ε : ℂ) - (criticalPowerContactCoefficient : ℂ)) := by
  have hs : 0 < (ε : ℂ).re := by simpa only [ofReal_re] using hε
  have hsum := summable_mellin_majorant_of_strict_power_growth
    criticalHarmonicContacts_zero (strictGrowth_criticalHarmonicContacts_iff_rh.mpr hRH) hs
  rw [logarithmicAbelMean_eq_oneSidedStepMellin,
    oneSidedStepMellin_eq_complexMellinPairing criticalHarmonicContacts_zero hs hsum]
  have hs1 : (ε : ℂ) + 1 / 2 ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num only [add_re, ofReal_re, div_ofNat_re, one_re] at hr
    linarith only [hr, hε2]
  have hζ : riemannZeta ((ε : ℂ) + 1 / 2) ≠ 0 := by
    simpa only [ofReal_add, ofReal_div, ofReal_one, ofReal_ofNat] using
      _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (by linarith only [hε] : 0 < ε + 1 / 2)
        (by linarith only [hε2] : ε + 1 / 2 < 1)
  have hh := criticalPowerContactMellin_eq_of_rh hRH hs hs1 hζ
  rw [criticalPowerContactMellin] at hh
  linear_combination hh

/-- The finite part of the actual harmonic-contact Abel mean is the
derivative of the analytic contact factor. -/
theorem tendsto_logarithmicAbelMean_criticalHarmonicContacts_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto (logarithmicAbelMean criticalHarmonicContacts)
      (𝓝[>] 0) (𝓝 (deriv criticalPowerContactFactor 0)) := by
  have heps : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hh := analyticAt_criticalPowerContactRegularPart.continuousAt.tendsto.comp heps
  rw [criticalPowerContactRegularPart_zero] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
  rw [logarithmicAbelMean_criticalHarmonicContacts_eq_of_rh hRH hε.1 hε.2]
  exact criticalPowerContactRegularPart_eq (ofReal_ne_zero.mpr (ne_of_gt hε.1))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
