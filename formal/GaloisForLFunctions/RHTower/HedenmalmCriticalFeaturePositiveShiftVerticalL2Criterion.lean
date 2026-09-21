import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSourceHorizontalPoleBlindness
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Vertical square-regularity criterion for the positive-shift HCF source

The continued pole--Gamma source is horizontally blind to a local Xi zero, but its vertical
restriction has a simple pole.  Consequently, finite squared source energy on every compact
positive-shift vertical segment is neither a heuristic proxy nor a density estimate: it is exactly
the Riemann hypothesis.  The forward implication uses the local source pole law; the reverse
implication uses only zero-freeness above the real centered axis and continuity away from zeros.

This is a sharp source-side interface.  It does not provide the arithmetic finite-trace estimate
which would prove the regularity unconditionally.
-/

open Complex Filter Topology Set MeasureTheory
open RHTower.RealBoundaryDivisor

namespace RHTower

noncomputable section

/-- On a compact positive-shift vertical segment, zero-freeness makes the continued pole--Gamma
source continuous. -/
theorem continuousOn_criticalFeaturePositiveShiftPoleGammaDensity_vertical_of_noZero
    {x a b : ℝ} (ha : 0 < a) (hb : b < 1 / 2)
    (hzero : ∀ eta ∈ Icc a b, XiC ((x : ℂ) + (eta : ℂ) * I) ≠ 0) :
    ContinuousOn (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x) (Icc a b) := by
  have hpath : Continuous (fun eta : ℝ => (x : ℂ) + (eta : ℂ) * I) := by
    fun_prop
  have hlog : ContinuousOn
      (fun eta : ℝ => logDeriv XiC ((x : ℂ) + (eta : ℂ) * I)) (Icc a b) := by
    intro eta heta
    have hA : AnalyticAt ℂ (logDeriv XiC) ((x : ℂ) + (eta : ℂ) * I) := by
      rw [show logDeriv XiC = fun w => deriv XiC w / XiC w from rfl]
      exact (XiC_analytic _ (Set.mem_univ _)).deriv.div
        (XiC_analytic _ (Set.mem_univ _)) (hzero eta heta)
    have hcomp : ContinuousAt
        ((logDeriv XiC) ∘ fun y : ℝ => (x : ℂ) + (y : ℂ) * I) eta :=
      ContinuousAt.comp (g := logDeriv XiC)
        (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * I)
        hA.continuousAt hpath.continuousAt
    change ContinuousWithinAt
      ((logDeriv XiC) ∘ fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (Icc a b) eta
    exact hcomp.continuousWithinAt
  have hboundary : ContinuousOn (fun eta => boundaryDensity XiC eta x) (Icc a b) := by
    unfold boundaryDensity
    exact continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hlog)
  have heq : EqOn (fun eta => boundaryDensity XiC eta x)
      (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x) (Icc a b) := by
    intro eta heta
    have hlow : XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0 := by
      have hconj := XiC_ne_zero_conj (hzero eta heta)
      have hcoord : (starRingEnd ℂ) ((x : ℂ) + (eta : ℂ) * I) =
          (x : ℂ) - (eta : ℂ) * I := by
        simp only [map_add, map_mul, conj_ofReal, conj_I]
        ring
      rwa [hcoord] at hconj
    exact boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
      (lt_of_lt_of_le ha heta.1) (lt_of_le_of_lt heta.2 hb) hlow
  exact hboundary.congr heq.symm

/-- The source-only vertical regularity property whose exact content is RH.  It quantifies over
literal positive-shift pole--Gamma values, rather than a selected zero divisor. -/
def CriticalFeaturePositiveShiftVerticalSquareRegularity : Prop :=
  ∀ x a b : ℝ, 0 < a → a ≤ b → b < 1 / 2 →
    IntervalIntegrable
      (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x ^ 2)
      volume a b

/-- **Exact source criterion.**  Finite squared continued pole--Gamma source energy on every
compact positive-shift vertical line holds exactly when all XiC zeros are on the real axis. -/
theorem criticalFeaturePositiveShiftVerticalSquareRegularity_iff_riemannHypothesis :
    CriticalFeaturePositiveShiftVerticalSquareRegularity ↔ RiemannHypothesis := by
  constructor
  · intro hregular
    rw [riemannHypothesis_iff_XiC_zeros_real]
    intro z hzero
    by_contra him
    have him0 : z.im ≠ 0 := him
    obtain hneg | hpos := lt_or_gt_of_ne him0
    · let x : ℝ := z.re
      let eta : ℝ := -z.im
      have heta : 0 < eta := by dsimp [eta]; linarith
      have hconj : XiC ((starRingEnd ℂ) z) = 0 := by
        rw [XiC_conj, hzero, map_zero]
      have hcoord : (x : ℂ) + (eta : ℂ) * I = (starRingEnd ℂ) z := by
        apply Complex.ext <;> simp [x, eta]
      have hzero' : XiC ((x : ℂ) + (eta : ℂ) * I) = 0 := by
        rw [hcoord]
        exact hconj
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hzero
      have hstrip := abs_xiSpectralPoint_im_lt_half q
      rw [hq] at hstrip
      have hetaHalf : eta < 1 / 2 := by
        dsimp [eta]
        rw [abs_of_neg hneg] at hstrip
        exact hstrip
      let b : ℝ := (eta + 1 / 2) / 2
      have hetab : eta < b := by dsimp [b]; linarith
      have hbh : b < 1 / 2 := by dsimp [b]; linarith
      exact (not_intervalIntegrable_sq_criticalFeaturePositiveShiftPoleGammaDensity_of_XiC_zero
        heta hetaHalf hzero' hetab) (hregular x eta b heta hetab.le hbh)
    · let x : ℝ := z.re
      let eta : ℝ := z.im
      have heta : 0 < eta := by dsimp [eta]; exact hpos
      have hcoord : (x : ℂ) + (eta : ℂ) * I = z := by
        apply Complex.ext <;> simp [x, eta]
      have hzero' : XiC ((x : ℂ) + (eta : ℂ) * I) = 0 := by
        rw [hcoord]
        exact hzero
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hzero
      have hstrip := abs_xiSpectralPoint_im_lt_half q
      rw [hq] at hstrip
      have hetaHalf : eta < 1 / 2 := by
        dsimp [eta]
        rw [abs_of_pos hpos] at hstrip
        exact hstrip
      let b : ℝ := (eta + 1 / 2) / 2
      have hetab : eta < b := by dsimp [b]; linarith
      have hbh : b < 1 / 2 := by dsimp [b]; linarith
      exact (not_intervalIntegrable_sq_criticalFeaturePositiveShiftPoleGammaDensity_of_XiC_zero
        heta hetaHalf hzero' hetab) (hregular x eta b heta hetab.le hbh)
  · intro hRH x a b ha hab hb
    have hcont : ContinuousOn
        (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact continuousOn_criticalFeaturePositiveShiftPoleGammaDensity_vertical_of_noZero
        ha hb (fun eta heta =>
          XiC_ne_zero_upperHalf_of_rh hRH (by
            rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq]
            simp
            exact lt_of_lt_of_le ha heta.1))
    have hsq : ContinuousOn
        (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x ^ 2) (uIcc a b) := by
      have hfun : (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x ^ 2) =
          (fun eta => criticalFeaturePositiveShiftPoleGammaDensity eta x) ^ 2 := by
        funext eta
        rfl
      rw [hfun]
      exact hcont.pow 2
    exact hsq.intervalIntegrable

end

end RHTower
