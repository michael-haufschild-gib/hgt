import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.Lemmas

/-!
# The arithmetic theta-wall profile has the wrong topology for ordinary Fourier transport

At aperture `a = 1/6`, the ordered-pair coefficient of the paper wall asymptotic is
`∑_(n,m≥1; m/n=exp(2b)) (nm)^(-2/3)`. It is positive at zero but zero almost everywhere as
an ordinary Lebesgue function, hence cannot be continuous. Every Lebesgue test annihilates it.
The analytic identification with the center-integrated theta current remains paper-level;
this module proves the exact arithmetic-profile claims without an RH premise.
-/

open MeasureTheory
open scoped ENNReal

namespace RHTower

noncomputable section

private def wallRatio (nm : ℕ × ℕ) : ℝ :=
  ((nm.2 + 1 : ℕ) : ℝ) / ((nm.1 + 1 : ℕ) : ℝ)

private def wallCenter (nm : ℕ × ℕ) : ℝ := Real.log (wallRatio nm) / 2

private def wallWeight (nm : ℕ × ℕ) : ℝ≥0∞ :=
  (((nm.1 + 1) * (nm.2 + 1) : ℕ) : ℝ≥0∞) ^ (-(2 / 3 : ℝ))

/-- The exact ordered-pair arithmetic coefficient of the leading theta wall at aperture `1/6`,
before multiplication by its positive analytic constant. -/
def thetaWallRatioAutocorrelation (b : ℝ) : ℝ≥0∞ :=
  ∑' nm : ℕ × ℕ,
    if Real.exp (2 * b) = wallRatio nm then wallWeight nm else 0

private theorem wallRatio_pos (nm : ℕ × ℕ) : 0 < wallRatio nm := by
  unfold wallRatio
  positivity

theorem thetaWallRatioAutocorrelation_eq_zero_of_not_mem
    {b : ℝ} (hb : b ∉ Set.range wallCenter) :
    thetaWallRatioAutocorrelation b = 0 := by
  have hfalse : ∀ nm : ℕ × ℕ, Real.exp (2 * b) ≠ wallRatio nm := by
    intro nm heq
    apply hb
    refine ⟨nm, ?_⟩
    unfold wallCenter
    have hlog := congrArg Real.log heq
    rw [Real.log_exp] at hlog
    linarith
  simp [thetaWallRatioAutocorrelation, hfalse]

theorem thetaWallRatioAutocorrelation_ae_eq_zero :
    thetaWallRatioAutocorrelation =ᵐ[(volume : Measure ℝ)] (fun _ => 0) := by
  have hnull : (volume : Measure ℝ) (Set.range wallCenter) = 0 :=
    (Set.countable_range wallCenter).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with b hb
  exact thetaWallRatioAutocorrelation_eq_zero_of_not_mem hb

/-- Every ordinary Lebesgue test annihilates the literal ratio coefficient, regardless of its
pointwise rational spikes. -/
theorem thetaWallRatioAutocorrelation_lintegral_test_zero (test : ℝ → ℝ≥0∞) :
    (∫⁻ b : ℝ, test b * thetaWallRatioAutocorrelation b) = 0 := by
  rw [lintegral_congr_ae (show
    (fun b : ℝ => test b * thetaWallRatioAutocorrelation b) =ᵐ[(volume : Measure ℝ)]
      (fun _ => 0) by
        filter_upwards [thetaWallRatioAutocorrelation_ae_eq_zero] with b hb
        rw [hb, mul_zero])]
  simp

theorem thetaWallRatioAutocorrelation_zero_pos :
    (1 : ℝ≥0∞) ≤ thetaWallRatioAutocorrelation 0 := by
  have h := ENNReal.le_tsum
    (f := fun nm : ℕ × ℕ =>
      if Real.exp (2 * (0 : ℝ)) = wallRatio nm then wallWeight nm else 0)
    (0, 0)
  simpa [thetaWallRatioAutocorrelation, wallRatio, wallWeight] using h

theorem thetaWallRatioAutocorrelation_not_continuous :
    ¬ Continuous thetaWallRatioAutocorrelation := by
  intro hc
  have hEq : thetaWallRatioAutocorrelation = (fun _ : ℝ => (0 : ℝ≥0∞)) :=
    Measure.eq_of_ae_eq thetaWallRatioAutocorrelation_ae_eq_zero hc continuous_const
  have hzero := congrFun hEq 0
  have hpos := thetaWallRatioAutocorrelation_zero_pos
  rw [hzero] at hpos
  norm_num at hpos

end

end RHTower
