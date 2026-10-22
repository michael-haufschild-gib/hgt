import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowExcessEnergyGate
import GaloisForLFunctions.RHTower.CCM.CCMRectangularSparseExceptionCompleteness
import GaloisForLFunctions.RHTower.CCM.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.GammaCellDegreeZeroAction

/-!
# Finite-exception closure for CCM Dirichlet-energy gates

Finite exceptional sets carry finite-support coefficient streams.  The existing finite-support
L-series theorem therefore discharges every exceptional-energy interface used by the sharp-window
and fixed rectangular Weil routes.

For a finite exceptional set, the rectangular criterion needs neither a separately supplied
energy certificate nor a preselected admissible cutoff: existence of one tail with one-sided
subpower control is exactly RH.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- `[BRIDGE]` A finite-support indicator coefficient has an absolutely convergent L-series at
every complex argument. -/
theorem lSeriesSummable_indicator_of_finite
    {E : Set ℕ} (hE : E.Finite) (a : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (E.indicator a) s := by
  let b : ArithmeticFunction ℂ :=
    ZeroHom.mk (fun n => if n = 0 then 0 else E.indicator a n) (by simp)
  have hsupport : (Function.support (fun n => b n)).Finite := by
    apply hE.subset
    intro n hn
    by_contra hnE
    apply hn
    simp [b, Set.indicator_of_notMem hnE]
  have hb := lSeriesSummable_of_finite_coefficient_support (a := b) hsupport s
  change Summable (LSeries.term (E.indicator a) s)
  change Summable (LSeries.term (fun n => b n) s) at hb
  exact hb.congr fun n => by
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [LSeries.term_zero, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp [b, hn0]

/-- The actual sharp-window positive excess on a finite exceptional set has finite Dirichlet
energy, with no analytic hypothesis. -/
theorem dyadicSharpExceptionalPositiveExcessEnergy_of_finite
    {E : Set ℕ} (hE : E.Finite) :
    DyadicSharpExceptionalPositiveExcessEnergy E := by
  intro epsilon _hepsilon
  convert
    lSeriesSummable_indicator_of_finite hE
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) using 1
  funext n
  by_cases hn : n ∈ E <;>
    simp [dyadicSharpExceptionalPositiveExcess, hn]

/-- The universal half-power majorant on a finite sharp-window exceptional set has finite
Dirichlet energy, with no analytic hypothesis. -/
theorem dyadicSharpHalfPowerExceptionalEnergy_of_finite
    {E : Set ℕ} (hE : E.Finite) :
    DyadicSharpHalfPowerExceptionalEnergy E := by
  intro epsilon _hepsilon
  convert
    lSeriesSummable_indicator_of_finite hE
      (fun n => ((powerCorrectionCoefficient (1 / 2 : ℝ) n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) using 1
  funext n
  by_cases hn : n ∈ E <;>
    simp [dyadicSharpHalfPowerExceptionalCoefficient, hn]

/-- Finite exceptions discharge the energy premise from the sparse sharp-window RH criterion. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff_finite
    {E : Set ℕ} (hE : E.Finite)
    (hupper : DyadicWeightedPrimeWindowSubpowerUpperOff E) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff
    E (dyadicSharpExceptionalPositiveExcessEnergy_of_finite hE) hupper

/-- The rectangular half-power exceptional-energy interface is automatic on finite sets. -/
theorem xiRectangularHalfPowerExceptionalEnergy_of_finite
    {E : Set ℕ} (hE : E.Finite) :
    XiRectangularHalfPowerExceptionalEnergy E := by
  intro epsilon _hepsilon
  convert
    lSeriesSummable_indicator_of_finite hE
      (fun n => ((powerCorrectionCoefficient (1 / 2 : ℝ) n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) using 1
  funext n
  by_cases hn : n ∈ E <;>
    simp [xiRectangularHalfPowerExceptionalCoefficient, hn]

/-- The exact negative-mass energy interface is automatic on finite exceptional sets. -/
theorem xiRectangularExceptionalNegativeEnergy_of_finite
    (L : ℝ) (N : ℕ) {E : Set ℕ} (hE : E.Finite) :
    XiRectangularExceptionalNegativeEnergy L N E := by
  intro epsilon _hepsilon
  convert
    lSeriesSummable_indicator_of_finite hE
      (fun n => ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) using 1
  funext n
  by_cases hn : n ∈ E <;>
    simp [xiRectangularExceptionalNegativeCoefficient, hn]

/-- Every power-weighted rectangular exceptional-energy interface is automatic on finite sets. -/
theorem xiRectangularPowerExceptionalEnergy_of_finite
    (beta : ℝ) {E : Set ℕ} (hE : E.Finite) :
    XiRectangularPowerExceptionalEnergy beta E := by
  intro epsilon _hepsilon
  convert
    lSeriesSummable_indicator_of_finite hE
      (fun n => ((powerCorrectionCoefficient beta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) using 1
  funext n
  by_cases hn : n ∈ E <;>
    simp [xiRectangularPowerExceptionalCoefficient, hn]

/-- In particular, the divisor-calibrated transverse exceptional-energy interface is automatic
on finite sets. -/
theorem xiRectangularTransverseExceptionalEnergy_of_finite
    {E : Set ℕ} (hE : E.Finite) :
    XiRectangularTransverseExceptionalEnergy E :=
  xiRectangularPowerExceptionalEnergy_of_finite xiRightTransverseSup hE

/-- For a fixed admissible tail and a finite exceptional set, off-exception subpower lower
control is exactly RH; no exceptional-energy premise remains. -/
theorem riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff_of_finite
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (E : Set ℕ) (hE : E.Finite) :
    RiemannHypothesis ↔ XiRectangularWeilSubpowerLowerOff L N E :=
  riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff
    hL hN E (xiRectangularHalfPowerExceptionalEnergy_of_finite hE)

/-- `[BRIDGE]` Cutoff-free finite-exception completeness.  For every positive rectangular width
and finite exceptional set, RH is equivalent to existence of one tail satisfying off-exception
subpower lower control.  The admissible cutoff and every Dirichlet-energy condition are supplied
by existing corpus theorems. -/
theorem riemannHypothesis_iff_exists_xiRectangularWeilSubpowerLowerOff_finite
    {L : ℝ} (hL : 0 < L) {E : Set ℕ} (hE : E.Finite) :
    RiemannHypothesis ↔
      ∃ N : ℕ, XiRectangularWeilSubpowerLowerOff L N E := by
  constructor
  · intro hRH
    obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff L
    exact ⟨N,
      (riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff_of_finite
        hL hN E hE).mp hRH⟩
  · rintro ⟨N, hlower⟩
    obtain ⟨M, hM⟩ := exists_xiRectangularAdmissibleCutoff L
    have hmax :
        ∀ n : ℕ, max N M ≤ n →
          1 ≤ n ∧ L ≤ Real.log n / 2 := by
      intro n hn
      exact hM n ((le_max_right N M).trans hn)
    apply
      (riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff_of_finite
        hL hmax E hE).mpr
    intro delta hdelta
    obtain ⟨C, hC, hlowerC⟩ := hlower delta hdelta
    exact ⟨C, hC, fun n hn hnE =>
      hlowerC n ((le_max_left N M).trans hn) hnE⟩

end

end RHTower
