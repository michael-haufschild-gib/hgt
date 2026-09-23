import GaloisForLFunctions.RHTower.XiShiftedHankelDefectRecession
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceIntegralLaw

/-!
# Shifted-Xi defect escape as a finite-action ultraviolet anomaly

At every fixed Hankel cutoff, all shifted-Xi blocks become positive far enough along the mass ray.
If RH is false, failure nevertheless persists above that cutoff.  This module packages simultaneous
fixed-cutoff restoration and higher-degree failure as one source-side ultraviolet-anomaly predicate
and proves that it is exactly false RH.

The mass direction behaves differently from degree refinement.  At each fixed positive degree,
far-right positivity supplies a complete outgoing chamber on which literal arithmetic source action
is integrable and equals current Jacobi flux.  Thus a false-RH defect is not failure of fixed-degree
finite action: it survives only by escaping to unbounded degree.
-/

open Filter Matrix MeasureTheory Set

namespace RHTower

noncomputable section

open XiShiftedCanonicalAdmission

/-- A shifted-Hankel ultraviolet anomaly: every fixed cutoff is eventually strictly positive,
while some strictly higher block remains indefinite at the same mass. -/
def XiShiftedHankelUVAnomaly : Prop :=
  ∀ d : ℕ, ∀ᶠ w : ℝ in atTop,
    (∀ n ≤ d, (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef) ∧
      ∃ n : ℕ, d < n ∧
        ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosSemidef

/-- **Ultraviolet anomaly classification.** False RH is exactly simultaneous far-right
restoration at every fixed Hankel cutoff and persistent failure above that cutoff. -/
theorem xiShiftedHankelUVAnomaly_iff_not_riemannHypothesis :
    XiShiftedHankelUVAnomaly ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hanomaly hRH
    obtain ⟨w, hw⟩ := (hanomaly 0).exists
    obtain ⟨n, _hn, hfail⟩ := hw.2
    exact hfail
      ((xiShiftedMomentHankelMatrix_forall_posSemidef_iff_riemannHypothesis
        (sq_nonneg w)).2 hRH n)
  · intro hnot d
    filter_upwards
      [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually_forall_size_le d,
        xiShiftedHankelDefectDegree_escapes_atTop_of_not_riemannHypothesis hnot d]
      with w hpositive hdefect
    exact ⟨hpositive, hdefect⟩

/-- **Unconditional fixed-degree finite-action law.** Every fixed positive shifted-Hankel degree
has a far-right mass threshold beyond which literal completed source action is integrable on the
whole outgoing ray and its total action is exactly the entry cumulative Jacobi flux. -/
theorem exists_fixedDegree_integrable_literalMassSourceAction_tail
    {n : ℕ} (hn : 0 < n) :
    ∃ a : ℝ, 1 / 4 < a ∧
      IntegrableOn
        (fun y =>
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
            (Real.sqrt y) n)
        (Ioi a) ∧
      (∫ y in Ioi a,
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
            (Real.sqrt y) n) =
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n := by
  have hSquare : ∀ᶠ w : ℝ in atTop,
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 2)).PosDef :=
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2)
  have hSqrt := Real.tendsto_sqrt_atTop.eventually hSquare
  have hEvent : ∀ᶠ y : ℝ in atTop,
      (xiShiftedMomentHankelMatrix y (n + 2)).PosDef := by
    filter_upwards [hSqrt, eventually_ge_atTop (0 : ℝ)]
      with y hpositive hy
    simpa only [Real.sq_sqrt hy] using hpositive
  obtain ⟨A, hA⟩ := eventually_atTop.1 hEvent
  let a : ℝ := max 1 A
  have ha : 1 / 4 < a := lt_of_lt_of_le (by norm_num) (le_max_left 1 A)
  have hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    intro y hy
    change (xiShiftedMomentHankelMatrix y (n + 2)).PosDef
    exact hA y ((le_max_right 1 A).trans hy)
  exact ⟨a, ha,
    integral_Ioi_literalMassSourceAction_eq_currentFlux ha hn hH⟩

end

end RHTower
