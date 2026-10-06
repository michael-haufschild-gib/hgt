import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalAbsorbedPrincipal
namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial ThetaRatioInfinity

theorem gradedReducedRead_swap_eval (h z : ℂ) :
    (Bivariate.swap (gradedReducedRead z)).map (evalRingHom h)=
      (gradedReducedRead z).eval (C h) := by
  ext n
  rw [coeff_map]
  exact gradedSurplusSlice_eval z n h

theorem gradedAbsorbedFamily_eval (h z : ℂ) :
    (gradedAbsorbedFamily z).map (evalRingHom h)=
      absorbEighth ((gradedReducedRead z).eval (C h)) ((1-h)^2/36) := by
  rw [gradedAbsorbedFamily,map_absorbEighth,gradedReducedRead_swap_eval]
  congr 1
  simp only [coe_evalRingHom,eval_mul,eval_C,eval_pow,eval_sub,eval_one,eval_X]
  ring

theorem surplusSubstitution_eval (h : ℂ) (P : Polynomial ℂ) (e : ℂ) :
    (surplusSubstitution h P).eval e=P.eval (e/h^2) := by
  change (P.comp (C (1/h^2)*X)).eval e=P.eval (e/h^2)
  rw [eval_comp]
  simp only [eval_mul,eval_C,eval_X]
  congr 1
  ring

theorem complete_terminal_absorbed_source (h z : ℂ) (hh : h≠0) :
    (gradedAbsorbedFamily z).map (evalRingHom h)=
      C (h^22)*surplusSubstitution h
        (absorbEighth (flatSourceSurplus (inverseClockK h) z)
          (9*(boundaryA 9 (inverseClockK h)+(boundaryB (inverseClockK h))^2/4))) := by
  rw [gradedAbsorbedFamily_eval]
  apply Polynomial.funext
  intro e
  simp only [absorbEighth,eval_add,eval_sub,eval_mul,eval_C,eval_pow,eval_X]
  rw [gradedReducedRead_coeff _ _ hh,gradedReducedRead_eval _ _ hh]
  simp only [eval_mul,eval_C,surplusSubstitution_eval,
    eval_add,eval_sub,eval_pow,eval_X]
  rw [←terminalAbsorptionMass h hh]
  field_simp [hh]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
