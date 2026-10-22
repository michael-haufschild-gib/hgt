import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerGreenInternalDefectCancellationLaw

/-!
# Resolved internal defect of the Deninger Green factorization

The composite Green map observes only the sum of its two transported internal covariance defects.
This file retains them as two coordinates.  Their codiagonal vanishes unconditionally, whereas
vanishing of the resolved pair for every source vector is equivalent to the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The two transported internal covariance defects before the Green codiagonal adds them. -/
def deningerArithmeticGreenResolvedDefect
    (a : DeningerArithmeticGradedH1) :
    DeningerArithmeticGradedH1 × DeningerArithmeticGradedH1 :=
  (deningerArithmeticGradedHodgeCovarianceDefect
      (deningerArithmeticGradedRieszConjugation a),
    deningerArithmeticGradedOrientedHodge.sigma
      (deningerArithmeticGradedRieszCovarianceDefect a))

/-- The resolved Green defect is exactly antidiagonal. -/
theorem deningerArithmeticGreenResolvedDefect_eq_antidiagonal
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGreenResolvedDefect a =
      resolvedDefectAntidiagonal
        (R := ℂ)
        (deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a)) := by
  apply Prod.ext
  · rfl
  · change
      deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedRieszCovarianceDefect a) =
        -deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a)
    exact eq_neg_of_add_eq_zero_right
      (deningerArithmeticGreen_internalDefects_cancel a)

/-- Total Green covariance is the codiagonal quotient of the resolved defect and therefore
vanishes without any critical-line hypothesis. -/
theorem deningerArithmeticGreenResolvedDefect_codiagonal
    (a : DeningerArithmeticGradedH1) :
    resolvedDefectCodiagonal (R := ℂ)
        (deningerArithmeticGreenResolvedDefect a) = 0 := by
  exact deningerArithmeticGreen_internalDefects_cancel a

/-- **Resolved Green criterion.**  RH is exactly vanishing of the two internal covariance defects
before their unconditional antidiagonal cancellation. -/
theorem deningerArithmeticGreenResolvedDefect_vanishes_iff_riemannHypothesis :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGreenResolvedDefect a = 0) ↔
        RiemannHypothesis := by
  constructor
  · intro hresolved
    rw [← deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis]
    intro b
    obtain ⟨a, rfl⟩ :=
      deningerArithmeticGradedRieszConjugation.surjective b
    have hpair := hresolved a
    have hfst := congrArg Prod.fst hpair
    change
      deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) = 0 at hfst
    exact sub_eq_zero.mp hfst
  · intro hRH a
    have hcomm :=
      deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis.mpr
        hRH (deningerArithmeticGradedRieszConjugation a)
    have hfirst :
        deningerArithmeticGradedHodgeCovarianceDefect
            (deningerArithmeticGradedRieszConjugation a) = 0 :=
      sub_eq_zero.mpr hcomm
    have hcancel := deningerArithmeticGreen_internalDefects_cancel a
    have hsecond :
        deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedRieszCovarianceDefect a) = 0 := by
      rw [hfirst, zero_add] at hcancel
      exact hcancel
    apply Prod.ext
    · exact hfirst
    · exact hsecond

/-- A single basis source already resolves one divisor copy: its two-channel defect vanishes
exactly when that copy lies on the critical line. -/
theorem deningerArithmeticGreenResolvedDefect_single_eq_zero_iff
    (q : XiZeroCopy) :
    deningerArithmeticGreenResolvedDefect (Finsupp.single q 1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hresolved
    have hsecond := congrArg Prod.snd hresolved
    change
      deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedRieszCovarianceDefect
            (Finsupp.single q 1)) = 0 at hsecond
    have hdefect :
        deningerArithmeticGradedRieszCovarianceDefect
            (Finsupp.single q 1) = 0 := by
      have hs :=
        congrArg deningerArithmeticGradedOrientedHodge.sigma hsecond
      rw [deningerArithmeticGradedOrientedHodge.sq] at hs
      simpa [GaloisForLFunctions.RHTower.kRealParityAction] using hs
    have hq := congrArg (fun x : DeningerArithmeticGradedH1 => x q) hdefect
    simpa using
      (deningerArithmeticGradedRieszCovarianceDefect_single_apply_eq_zero_iff q).mp
        hq
  · intro hline
    have hq :
        deningerArithmeticGradedRieszCovarianceDefect
            (Finsupp.single q 1) q = 0 :=
      (deningerArithmeticGradedRieszCovarianceDefect_single_apply_eq_zero_iff q).mpr
        hline
    have hdefect :
        deningerArithmeticGradedRieszCovarianceDefect
            (Finsupp.single q 1) = 0 := by
      ext r
      by_cases hr : r = q
      · subst r
        exact hq
      · rw [deningerArithmeticGradedRieszCovarianceDefect_apply]
        simp [deningerArithmeticGradedRieszConjugation_apply, hr]
    have hsecond :
        deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedRieszCovarianceDefect
              (Finsupp.single q 1)) = 0 := by
      rw [hdefect]
      exact deningerArithmeticGradedOrientedHodge.sigma.map_zero
    have hcancel := deningerArithmeticGreen_internalDefects_cancel
      (Finsupp.single q 1)
    rw [hsecond, add_zero] at hcancel
    apply Prod.ext
    · exact hcancel
    · exact hsecond

end

end RHTower
