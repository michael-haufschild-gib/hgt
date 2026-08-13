import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceReciprocalClock
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceDegreeCoercivity

/-!
# Full-tail degree law for adaptive mixed arithmetic source

Fixed-degree source tightness and pointwise degree coercivity combine into a genuine
discrete--continuous tail law.  On a common complete positive chamber, difference between adjacent
literal adaptive mixed/completed source actions integrates exactly to adjacent cumulative-flux
edge at chamber entry.  Moreover that degree connector belongs to `L²` on the whole outgoing ray,
with norm paid by newborn entry flux.

Thus inter-degree leakage is neither an unspecified boundary term nor reusable local reporting:
it is an exact source plaquette with finite Dirichlet capital.
-/

open Matrix Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators Interval

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- **Exact full-tail source plaquette.**  Adjacent source-action difference is integrable and its
entire outgoing integral is exactly the degree connector at entry. -/
theorem integral_Ioi_literalMassSourceAction_succ_sub_eq_degreeEdge
    {a : ℝ} (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    IntegrableOn
        (fun y =>
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
              (Real.sqrt y) (n + 1) -
            xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
              (Real.sqrt y) n)
        (Ioi a) ∧
      (∫ y in Ioi a,
          (xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
              (Real.sqrt y) (n + 1) -
            xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
              (Real.sqrt y) n)) =
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux a (n + 1) -
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux a n := by
  have hHnext : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hH
  have hHcurrent : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef := by
    intro y hy
    exact xiShiftedMomentHankel_posDef_of_le (by omega) (hH y hy)
  have hnext := integral_Ioi_literalMassSourceAction_eq_currentFlux
    ha (by omega : 0 < n + 1) hHnext
  have hcurrent := integral_Ioi_literalMassSourceAction_eq_currentFlux
    ha hn hHcurrent
  refine ⟨hnext.1.sub hcurrent.1, ?_⟩
  rw [integral_sub hnext.1 hcurrent.1, hnext.2, hcurrent.2]

/-- Source plaquette in Jacobi endpoint coordinates. -/
theorem integral_Ioi_literalMassSourceAction_succ_sub_eq_adjacentAlpha
    {a : ℝ} (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    (∫ y in Ioi a,
        (xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
            (Real.sqrt y) (n + 1) -
          xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
            (Real.sqrt y) n)) =
      HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment a k).re) n +
        HTGeometry.monicOrthoAlpha
          (fun k => (xiShiftedReciprocalMoment a k).re) (n + 1) := by
  rw [(integral_Ioi_literalMassSourceAction_succ_sub_eq_degreeEdge ha hn hH).2]
  have hedge := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_succ_sub_eq_adjacentAlpha
    (w := Real.sqrt a) hn
  have hasq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (le_trans (by norm_num) ha.le)
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt a)) (n + 3)).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt a) ^ 2) k).re) (n + 3)).PosDef
    rw [hasq]
    exact hH a self_mem_Ici
  have hseq : xiShiftedRealMomentSequence (Real.sqrt a) =
      (fun k => (xiShiftedReciprocalMoment a k).re) := by
    funext k
    rw [xiShiftedRealMomentSequence, hasq]
  have hHactual : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment a k).re) (n + 3)).PosDef := by
    rwa [← hseq]
  rw [hasq, hseq] at hedge
  exact hedge hHactual

/-- **Full-tail degree Dirichlet budget.**  Adjacent cumulative-flux connector is square-integrable
on the whole outgoing ray, and its total `L²` capital is at most `3/2` times newborn entry flux. -/
theorem integrableOn_Ioi_degreeEdge_sq_and_integral_le_entryFlux
    {a : ℝ} (ha : 1 / 4 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    IntegrableOn
        (fun y =>
          (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (n + 1) -
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n) ^ 2)
        (Ioi a) ∧
      (∫ y in Ioi a,
          (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (n + 1) -
            xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n) ^ 2) ≤
        (3 / 2 : ℝ) *
          xiShiftedCanonicalAdmissionCumulativeJacobiFlux a (n + 1) := by
  let E : ℝ → ℝ := fun y =>
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (n + 1) -
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux y n) ^ 2
  let J : ℝ → ℝ := fun y =>
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction
      (Real.sqrt y) (n + 1)
  have hHnext : ∀ y ∈ Ici a,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) ((n + 1) + 2)).PosDef := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hH
  have htail := integral_Ioi_literalMassSourceAction_eq_currentFlux
    ha (by omega : 0 < n + 1) hHnext
  have hJint : IntegrableOn J (Ioi a) := by simpa only [J] using htail.1
  have hmajorInt : IntegrableOn (fun y => (3 / 2 : ℝ) * J y) (Ioi a) :=
    hJint.const_mul (3 / 2 : ℝ)
  have hpoint : ∀ y ∈ Ioi a, E y < (3 / 2 : ℝ) * J y := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_trans ha hy
    have hysq : (Real.sqrt y) ^ 2 = y :=
      Real.sq_sqrt (le_trans (by norm_num) hyquarter.le)
    have hsqrt : 1 / 2 < Real.sqrt y := by
      nlinarith [Real.sqrt_nonneg y]
    have hHsqrt : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 3)).PosDef := by
      change (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment ((Real.sqrt y) ^ 2) k).re)
          (n + 3)).PosDef
      rw [hysq]
      exact hH y (Set.mem_Ici.mpr hy.le)
    have hcoercive :=
      xiShiftedCanonicalAdmissionCumulativeJacobiFlux_degreeEdge_sq_lt_sourceAction_succ
        hsqrt hn hHsqrt
    rw [hysq] at hcoercive
    simpa only [E, J] using hcoercive
  have hEcont : ContinuousOn E (Ioi a) := by
    intro y hy
    have hyquarter : 1 / 4 < y := lt_trans ha hy
    have hHnexty := hH y (Set.mem_Ici.mpr hy.le)
    have hHcurrenty : (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
      xiShiftedMomentHankel_posDef_of_le (by omega) hHnexty
    have hnext := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter (by omega : 0 < n + 1) hHnexty
    have hcurrent := hasDerivAt_flux_eq_neg_literalMassSourceAction
      hyquarter hn hHcurrenty
    exact ((hnext.sub hcurrent).continuousAt.pow 2).continuousWithinAt
  have hEaes : AEStronglyMeasurable E (volume.restrict (Ioi a)) :=
    hEcont.aestronglyMeasurable measurableSet_Ioi
  have hnormBound : ∀ᵐ y ∂volume.restrict (Ioi a),
      ‖E y‖ ≤ (3 / 2 : ℝ) * J y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => ?_)
    have hlt := hpoint y hy
    have hJpos : 0 < J y := by
      dsimp only [J]
      exact literalMassSourceAction_pos (lt_trans ha hy) (by omega)
        (hH y (Set.mem_Ici.mpr hy.le))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hlt.le
  have hEint : IntegrableOn E (Ioi a) :=
    hmajorInt.mono' hEaes hnormBound
  have hleAE : ∀ᵐ y ∂volume.restrict (Ioi a), E y ≤ (3 / 2 : ℝ) * J y := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y hy => (hpoint y hy).le)
  have hintegral := integral_mono_ae hEint hmajorInt hleAE
  refine ⟨hEint, ?_⟩
  dsimp only [E, J] at hintegral ⊢
  rw [integral_const_mul, htail.2] at hintegral
  exact hintegral

end
end XiShiftedCanonicalAdmission
end RHTower
