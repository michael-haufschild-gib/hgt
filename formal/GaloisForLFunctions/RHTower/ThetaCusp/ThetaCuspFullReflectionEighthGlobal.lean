import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeCompactReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularCompactTube
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthGeneralModularClosure
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthScaleEighteenFifthsDirectAffineJoint

/-!
# Global strict rank-three reflected curvature of the theta source

The autonomous modular differential bounds put the missing compact part of the
literal source orbit in a polynomial chamber with a fixed positive reserve.
Together with the outer source estimate and the modular seam theorem, this
proves strict native rank-three curvature on the entire nonnegative ray.
-/

namespace RHTower
noncomputable section

/-- The literal modular value is the full real compact-chart polynomial. -/
theorem thetaCuspReflectedEighthLyapunovModularValue_eq_compactD1 (x : ℝ) :
    thetaCuspReflectedEighthLyapunovModularValue x =
      (HTGeometry.modularThetaCompactD1 (thetaCuspModularDrift x).re
        (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) : ℂ) := by
  unfold thetaCuspReflectedEighthLyapunovModularValue
  have hs : (fun i => thetaCuspModularLyapunovState i x) =
      (fun i : HTGeometry.ModularThetaLyapunovState => match i with
        | .S => ((thetaCuspModularDrift x).re : ℂ)
        | .A => (thetaCuspModularGapAmplitude x : ℂ)
        | .W => (thetaCuspModularTransverseShear x : ℂ)) := by
    funext i
    cases i <;> rfl
  rw [hs]
  exact HTGeometry.modularThetaLyapunovReflectedEighthPolynomial_eval_ofReal _ _ _

/-- The full mass-normalized determinant has a fixed arithmetic reserve on the compact orbit. -/
theorem thetaCuspCompactD1_lower {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (137 / 2000)) :
    (1000000000 : ℝ) ≤ HTGeometry.modularThetaCompactD1 (thetaCuspModularDrift x).re
      (thetaCuspModularGapAmplitude x) (thetaCuspModularTransverseShear x) := by
  obtain ⟨hS0,hS1,hA0,hA1,hW0,_⟩ := thetaCuspModularLyapunovState_compact_box hx
  exact HTGeometry.modularThetaCompactD1_lower_on_tight_box hS0 hS1 hA0 hA1 hW0
    (thetaCuspModularTransverseShear_le_one_on_compact hx)

/-- Raw reflected rank-three curvature is strictly positive throughout the compact orbit. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_pos_on_compact {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (137 / 2000)) :
    0 < thetaCuspFullSourceReflectionEighthHankelCurvature x := by
  apply (thetaCuspFullSourceReflectionEighthHankelCurvature_pos_iff_lyapunovModular x).mpr
  rw [thetaCuspReflectedEighthLyapunovModularValue_eq_compactD1, Complex.ofReal_re]
  have h := thetaCuspCompactD1_lower hx
  linarith

/-- The literal theta source has strict native rank-three reflected curvature everywhere on its
nonnegative physical ray, with no unproved source-sign input. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_on_nonnegative :
    ∀ x : ℝ, 0 ≤ x → 0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  intro x hx
  rcases hx.eq_or_lt with rfl | hxpos
  · exact thetaCuspFullReflectionEighthHankelCurvature_zero_pos
  by_cases houter : (137 / 2000 : ℝ) ≤ x
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_oneHundredThirtySevenTwoThousandths_le
      houter
  have hraw := thetaCuspFullSourceReflectionEighthHankelCurvature_pos_on_compact
    (show x ∈ Set.Icc (0 : ℝ) (137 / 2000) from ⟨hxpos.le,(lt_of_not_ge houter).le⟩)
  rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hxpos] at hraw
  rcases mul_pos_iff.mp hraw with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge (by positivity)) hneg.1)

end
end RHTower
