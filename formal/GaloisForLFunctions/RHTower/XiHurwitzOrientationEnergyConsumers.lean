import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergy
import GaloisForLFunctions.RHTower.XiCentralHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Consumers of the Xi--Hurwitz scalar orientation energy

The scalar equality `xiHurwitzOrientationEnergy = 0` discharges the RH input of the central
trace/Hankel and complete Weil-positivity theorem surfaces.  These are bridge results: they expose
the exact reuse of the new scalar law without adding a second mathematical hypothesis.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The first analytic-multiplicity copy of an actual Xi-divisor support point. -/
def xiFirstZeroCopy (ρ : XiDivisorSupport) : XiZeroCopy := by
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  exact ⟨ρ, ⟨0, hn⟩⟩

@[simp] theorem xiFirstZeroCopy_fst (ρ : XiDivisorSupport) :
    (xiFirstZeroCopy ρ).1 = ρ := rfl

/-- The explicit conjugate-pair Weil sign test attached to one Xi-divisor support point. -/
def xiHurwitzExplicitWeilSignTest (ρ : XiDivisorSupport) : ℂ → ℂ :=
  xiOffRealSignTest (xiSpectralPoint (xiFirstZeroCopy ρ))

theorem xiHurwitzExplicitWeilSignTest_squareSummable (ρ : XiDivisorSupport) :
    XiWeilSquareSummable (xiHurwitzExplicitWeilSignTest ρ) := by
  exact xiOffRealSignTest_squareSummable _

/-- An explicit off-critical-line Xi point gives an explicit strictly negative Weil square. -/
theorem xiHurwitzExplicitWeilSignTest_negative
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re ≠ 1 / 2) :
    (xiWeilPolarization (xiHurwitzExplicitWeilSignTest ρ)
      (xiHurwitzExplicitWeilSignTest ρ)).re < 0 := by
  let q := xiFirstZeroCopy ρ
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him0
    apply hρ
    change ((((ρ : ℂ) - 1 / 2) * (-Complex.I)).im = 0) at him0
    simp at him0
    linarith
  have hconj : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q :=
    Complex.conj_eq_iff_im.not.mpr him
  simpa only [xiHurwitzExplicitWeilSignTest, q] using
    xiWeilPolarization_offRealSignTest_re_neg q hconj

/-- **Constructive local witness law.**  An explicit off-critical-line Xi-divisor point supplies
both its explicit positive contribution to the scalar energy and an explicit negative vector for
the complete Xi Weil/Krein form. -/
theorem xiHurwitz_offCritical_constructive_energy_weil_witness
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re ≠ 1 / 2) :
    0 < xiHurwitzOrientationEnergyTerm ρ ∧
      xiHurwitzOrientationEnergyTerm ρ ≤ xiHurwitzOrientationEnergy ∧
      XiWeilSquareSummable (xiHurwitzExplicitWeilSignTest ρ) ∧
      (xiWeilPolarization (xiHurwitzExplicitWeilSignTest ρ)
        (xiHurwitzExplicitWeilSignTest ρ)).re < 0 := by
  exact ⟨mul_pos (xiHurwitzOrientationWeight_pos ρ)
      ((xiHurwitzOrientationDefect_pos_iff_re_ne_half ρ).mpr hρ),
    xiHurwitzOrientationEnergyTerm_le_energy ρ,
    xiHurwitzExplicitWeilSignTest_squareSummable ρ,
    xiHurwitzExplicitWeilSignTest_negative ρ hρ⟩

/-- The scalar zero-energy law is exactly the existing complete trace-Hankel positivity law. -/
theorem xiHurwitzOrientationEnergy_eq_zero_iff_traceHankelNonnegative :
    xiHurwitzOrientationEnergy = 0 ↔ XiCentralTraceHankelNonnegative := by
  exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.symm.trans
    xiCentralTraceHankelNonnegative_iff_riemannHypothesis.symm

/-- The scalar zero-energy law is exactly positivity of every leading central Hankel
determinant. -/
theorem xiHurwitzOrientationEnergy_eq_zero_iff_hankelDeterminantsPositive :
    xiHurwitzOrientationEnergy = 0 ↔
      XiCentralMomentHankelDeterminantsPositive := by
  exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.symm.trans
    xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis.symm

/-- One scalar equality discharges the RH hypothesis in every central moment Hankel
positive-definiteness conclusion. -/
theorem xiCentralMomentHankelPosDef_of_xiHurwitzOrientationEnergy_eq_zero
    (henergy : xiHurwitzOrientationEnergy = 0) :
    XiCentralMomentHankelPosDef := by
  apply xiCentralMomentHankelPosDef_iff_riemannHypothesis.mpr
  exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr henergy

/-- One scalar equality discharges the RH hypothesis in the complete square-summable Xi Weil
positivity theorem. -/
theorem xiWeilPolarization_nonneg_of_xiHurwitzOrientationEnergy_eq_zero
    (henergy : xiHurwitzOrientationEnergy = 0) :
    ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      0 ≤ (xiWeilPolarization F F).re := by
  apply riemannHypothesis_iff_xiWeilPolarization_nonneg.mp
  exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr henergy

/-- Positive scalar energy is classically equivalent to existence of a negative trace-Hankel
polynomial witness. -/
theorem xiHurwitzOrientationEnergy_pos_iff_exists_traceHankel_negative :
    0 < xiHurwitzOrientationEnergy ↔
      ∃ p : Polynomial ℝ, (xiCentralTraceHankel p).re < 0 := by
  classical
  constructor
  · intro henergy
    have hnotRH :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mp henergy
    have hnotTrace : ¬XiCentralTraceHankelNonnegative := by
      intro htrace
      exact hnotRH
        (xiCentralTraceHankelNonnegative_iff_riemannHypothesis.mp htrace)
    change ¬∀ p : Polynomial ℝ, 0 ≤ (xiCentralTraceHankel p).re at hnotTrace
    push Not at hnotTrace
    exact hnotTrace
  · rintro ⟨p, hp⟩
    apply xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mpr
    intro hRH
    have hpos :=
      xiCentralTraceHankelNonnegative_iff_riemannHypothesis.mpr hRH p
    exact (not_lt_of_ge hpos) hp

/-- Positive scalar energy is classically equivalent to failure of one finite leading central
Hankel determinant. -/
theorem xiHurwitzOrientationEnergy_pos_iff_exists_hankelDet_nonpos :
    0 < xiHurwitzOrientationEnergy ↔
      ∃ n : ℕ, (xiCentralMomentHankelMatrix n).det ≤ 0 := by
  classical
  constructor
  · intro henergy
    have hnotRH :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mp henergy
    have hnotDet : ¬XiCentralMomentHankelDeterminantsPositive := by
      intro hdet
      exact hnotRH
        (xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp hdet)
    change ¬∀ n : ℕ, 0 < (xiCentralMomentHankelMatrix n).det at hnotDet
    push Not at hnotDet
    exact hnotDet
  · rintro ⟨n, hn⟩
    apply xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mpr
    intro hRH
    have hpos :=
      xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH n
    exact (not_lt_of_ge hn) hpos

/-- Positive scalar energy is classically equivalent to existence of a negative square in the
complete square-summable Xi Weil/Krein form. -/
theorem xiHurwitzOrientationEnergy_pos_iff_exists_weil_negativeSquare :
    0 < xiHurwitzOrientationEnergy ↔
      ∃ F : ℂ → ℂ, XiWeilSquareSummable F ∧
        (xiWeilPolarization F F).re < 0 := by
  classical
  constructor
  · intro henergy
    have hnotRH :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mp henergy
    have hnotWeil : ¬(∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re) := by
      intro hweil
      exact hnotRH (riemannHypothesis_iff_xiWeilPolarization_nonneg.mpr hweil)
    push Not at hnotWeil
    exact hnotWeil
  · rintro ⟨F, hF, hneg⟩
    apply xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.mpr
    intro hRH
    have hnonneg :=
      riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH F hF
    exact (not_lt_of_ge hnonneg) hneg

/-- **Scalar positivity-compression law.**  Vanishing of the one Xi--Hurwitz orientation energy
is equivalent simultaneously to the full trace-Hankel positivity cone, the complete leading-Hankel
determinant chamber, and the full square-summable Xi Weil positivity cone. -/
theorem xi_hurwitz_orientation_energy_positivity_compression_law :
    xiHurwitzOrientationEnergy = 0 ↔
      XiCentralTraceHankelNonnegative ∧
      XiCentralMomentHankelDeterminantsPositive ∧
      (∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re) := by
  constructor
  · intro henergy
    have hRH :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr henergy
    exact ⟨xiCentralTraceHankelNonnegative_iff_riemannHypothesis.mpr hRH,
      xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH,
      riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH⟩
  · rintro ⟨htrace, -, -⟩
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mp
    exact xiCentralTraceHankelNonnegative_iff_riemannHypothesis.mp htrace

end

end RHTower
