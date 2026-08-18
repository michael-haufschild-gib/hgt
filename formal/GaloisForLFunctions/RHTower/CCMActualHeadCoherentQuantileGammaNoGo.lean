import GaloisForLFunctions.RHTower.CCMActualHeadCoherentQuantileGammaProducer
import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalGroundHeadConvergence
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# No-go for a phase-free coherent quantile Γ budget

The coherent quantile chi-square preserves cross-prime and prime--terminal autocorrelations, but
completion of the higher-Γ square still discards the phase between the translation increment and
the coherent field.  The proposed final estimate

`2 * coherentChiSquare(f) ≤ (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖²`

cannot hold: Gauss's quarter-digamma identity makes its scalar budget strictly negative, whereas
the coherent chi-square is nonnegative.  This module proves the contradiction for every nonzero
vector and then proves that it occurs eventually on the literal canonical finite Gamma--Slepian
ground heads.  Thus Route O must sign the joint higher-Γ/current block without separating a
nonnegative coherent-field norm cost.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Exact central Gamma scalar from Gauss's quarter-digamma value. -/
theorem gammaHardyPhaseRate_zero_closed :
    gammaHardyPhaseRate 0 =
      -(3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2) / 2 -
        Real.log Real.pi / 2 := by
  have hline : linePt 0 / 2 = (1 / 4 : ℂ) := by
    unfold linePt
    norm_num
  unfold gammaHardyPhaseRate
  rw [hline, GaloisForLFunctions.RHTower.digamma_quarter]
  simp only [Complex.neg_re, Complex.ofReal_re]

/-- The scalar reserve left after the polar endpoint cancellation is strictly negative. -/
theorem two_gammaHardyPhaseRate_zero_add_four_neg :
    2 * gammaHardyPhaseRate 0 + 4 < 0 := by
  rw [gammaHardyPhaseRate_zero_closed]
  have hgamma : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hlogTwo := Real.log_two_gt_d9
  have hpi := Real.pi_gt_three
  have hlogPi : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  nlinarith

/-- No nonzero actual head can pay a nonnegative coherent chi-square from the negative central
Gamma--polar scalar budget. -/
theorem not_coherentChiSquare_le_centralBudget_of_ne_zero
    (T : ℝ) (N : ℕ) {f : SoninL2} (hf : f ≠ 0) :
    ¬ 2 * ccmActualHeadCoherentQuantileGammaChiSquare T N f ≤
        (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 := by
  intro h
  have hchi := ccmActualHeadCoherentQuantileGammaChiSquare_nonneg T N f
  have hnorm : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hbudget := two_gammaHardyPhaseRate_zero_add_four_neg
  nlinarith

/-- Literal canonical finite Gamma--Slepian heads are physically nonzero cofinally. -/
theorem eventually_ccmRestrictedWeilCanonicalGroundHead_physical_ne_zero
    (a : SuzukiPositiveAperture) :
    ∀ᶠ n in atTop,
      ((ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilCanonicalGroundHead a n) :
          suzukiApertureHilbert a) : SoninL2) ≠ 0 := by
  let J := ccmArchimedeanFormToAperture a
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  have hu : J u ≠ 0 := by
    rw [show J u =
        (ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a) by
      exact ccmRestrictedWeilCanonicalGroundFormLift_embedding a]
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a
  have hnorm : Tendsto
      (fun n => ‖J (ccmRestrictedWeilCanonicalGroundHead a n)‖)
      atTop (nhds ‖J u‖) :=
    (continuous_norm.tendsto _).comp
      ((J.continuous.tendsto _).comp
        (tendsto_ccmRestrictedWeilCanonicalGroundHead a))
  have hpos : 0 < ‖J u‖ := norm_pos_iff.mpr hu
  have heventually : ∀ᶠ n in atTop,
      0 < ‖J (ccmRestrictedWeilCanonicalGroundHead a n)‖ :=
    hnorm.eventually (Ioi_mem_nhds hpos)
  filter_upwards [heventually] with n hn
  intro hz
  have hzero : J (ccmRestrictedWeilCanonicalGroundHead a n) = 0 :=
    Subtype.ext hz
  rw [hzero, norm_zero] at hn
  exact (lt_irrefl 0 hn)

/-- **Cofinal coherent-chi-square no-go on canonical actual heads.**  The proposed bound is not
merely unavailable: its negation holds eventually at every positive aperture. -/
theorem eventually_not_ccmRestrictedWeilCanonicalGroundHead_coherentChiSquare_le_centralBudget
    (a : SuzukiPositiveAperture) :
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ∀ᶠ n in atTop,
      ¬ 2 * ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N
          ((ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n) :
              suzukiApertureHilbert a) : SoninL2) ≤
        (2 * gammaHardyPhaseRate 0 + 4) *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 := by
  dsimp only
  filter_upwards [eventually_ccmRestrictedWeilCanonicalGroundHead_physical_ne_zero a]
    with n hn
  exact not_coherentChiSquare_le_centralBudget_of_ne_zero
    (2 * a.1) (Nat.floor (Real.exp (2 * a.1)) + 1) hn

end RHTower
