import GaloisForLFunctions.HTGeometry.PolynomialODE.JetOddRankThreeClosure
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5JacobianSeamOrientation

/-!
# All-order source jets at the modular seam

The public source-positive chart and its exact chart equivalences identify every
literal source derivative with the four-state formal jet. This interface needs
only the existing first-order source equations.
-/

namespace HTGeometry
noncomputable section

theorem eval_sourcePositiveJet_seam_eq_formalJet (R : ℝ) (n : ℕ) :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState (R^(2 : ℕ)))
      (modularThetaSourcePositiveNormalizedSourceJet n) =
    MvPolynomial.eval (modularThetaODESeamState (R : ℂ)) (modularThetaODESourceJet n) := by
  rw [← modularThetaSourcePositiveChart_sourceJet,
    eval_modularThetaSourcePositiveChartPullback_seam,
    ← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_normalizedSourceJet]
  have h := congrArg (MvPolynomial.eval (modularThetaODESeamState (R : ℂ)))
    (modularThetaODESourceJet_eq_X_H_mul_normalized n)
  simpa [modularThetaODESeamState] using h.symm

/-- The normalized odd rank-three block is the exact degree-fifteen seam polynomial. -/
theorem oddHankelThree_formalJet_seam (R : ℂ) :
    let f := fun n => MvPolynomial.eval (modularThetaODESeamState R) (modularThetaODESourceJet n)
    signedEvenHankelThreeDetC
      (-2*f 0*f 2) (2*f 0*f 4+6*f 2^(2 : ℕ)) (-2*f 0*f 6-30*f 2*f 4)
      (2*f 0*f 8+56*f 2*f 6+70*f 4^(2 : ℕ))
      (-2*f 0*f 10-90*f 2*f 8-420*f 4*f 6) =
      modularThetaReflectedTenthSeamPolynomial (R^(2 : ℕ)) := by
  let v := modularThetaODESeamState R
  have h := modularThetaReflectedTenthSeamJetElimination (1 : ℂ) R
    (evalModularThetaODEFormalJet v .H) (evalModularThetaODEFormalJet v .Z)
    (evalModularThetaODEFormalJet v .R) (evalModularThetaODEFormalJet v .P)
    (by simp [v,modularThetaODESeamState]) (by simp [v,modularThetaODESeamState])
    (by simp [v,modularThetaODESeamState]) (by simp [v,modularThetaODESeamState])
    (evalModularThetaODEFormalJet_H_succ v) (evalModularThetaODEFormalJet_Z_succ v)
    (evalModularThetaODEFormalJet_R_succ v) (evalModularThetaODEFormalJet_P_succ v)
  simpa only [eval_modularThetaODESourceJet_eq_formalJet, one_pow, one_mul] using h

end
end HTGeometry

namespace RHTower
noncomputable section

/-- Every literal theta derivative at zero is mass times its normalized formal ODE jet. -/
theorem thetaCuspFullSource_seamJet_eq_formalJet (n : ℕ) :
    ((iteratedDeriv n thetaCuspFullSource 0 : ℝ) : ℂ) =
      (thetaCuspSelfDualThetaMass : ℂ) *
      MvPolynomial.eval (HTGeometry.modularThetaODESeamState (thetaCuspSelfDualModularScale : ℂ))
        (HTGeometry.modularThetaODESourceJet n) := by
  rw [← SchwartzMap.iteratedDeriv_ofReal thetaCuspFullSource contDiff_thetaCuspFullSource]
  have hfun : (fun x : ℝ => (thetaCuspFullSource x : ℂ)) =
      fun x => thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        thetaCuspModularSourcePositiveState HTGeometry.ModularThetaSourcePositiveState.Q x :=
    funext ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ
  rw [hfun, HTGeometry.iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet
    thetaCuspModularSourcePositiveState hasDerivAt_thetaCuspModularSourcePositiveState
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H)
    hasDerivAt_thetaCuspModularMass_sourcePositive]
  dsimp only
  rw [thetaCuspModularSourcePositiveState_zero_eq_seam,
    HTGeometry.eval_sourcePositiveJet_seam_eq_formalJet,
    thetaCuspModularODEState_H_eq_completedThetaProfile]
  simp [Bottcher.completedThetaProfile,thetaCuspSelfDualThetaMass]

/-- Literal odd rank-three source seam before reflection-product substitution. -/
theorem thetaCuspFullSource_oddHankelThreeSeam_eq_modularPolynomial :
    let f := fun n => ((iteratedDeriv n thetaCuspFullSource 0 : ℝ) : ℂ)
    HTGeometry.signedEvenHankelThreeDetC
      (-2*f 0*f 2) (2*f 0*f 4+6*f 2^(2 : ℕ)) (-2*f 0*f 6-30*f 2*f 4)
      (2*f 0*f 8+56*f 2*f 6+70*f 4^(2 : ℕ))
      (-2*f 0*f 10-90*f 2*f 8-420*f 4*f 6) =
      (thetaCuspSelfDualThetaMass : ℂ)^(6 : ℕ) *
        HTGeometry.modularThetaReflectedTenthSeamPolynomial ((thetaCuspSelfDualModularScale : ℂ)^(2 : ℕ)) := by
  dsimp only
  simp_rw [thetaCuspFullSource_seamJet_eq_formalJet]
  rw [← HTGeometry.oddHankelThree_formalJet_seam]
  dsimp only
  unfold HTGeometry.signedEvenHankelThreeDetC
  ring

end
end RHTower
