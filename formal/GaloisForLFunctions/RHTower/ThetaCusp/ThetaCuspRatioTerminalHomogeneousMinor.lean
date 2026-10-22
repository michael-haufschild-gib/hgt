import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalHomogeneousReflections
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalPrincipalAlgebra

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def reflectionHomogeneousRows (Y T : ℂ) : Fin 5 → Polynomial ℂ :=
  ![reflectionHomogeneous 2 Y T,reflectionHomogeneous 4 Y T,
    reflectionHomogeneous 6 Y T,reflectionHomogeneous 8 Y T,reflectionHomogeneous 10 Y T]

theorem reflectionHomogeneousRows_zero (Y T : ℂ) :
    (fun i => (reflectionHomogeneousRows Y T i).coeff 0)=
      leadingRows (-12*Y*(T+Y)*T) (8*Y^2*T) T := by
  funext i
  fin_cases i <;> simp only [reflectionHomogeneousRows,leadingRows,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals
    rw [reflectionHomogeneous_zero (by norm_num) (by omega)]
    norm_num <;> ring

theorem reflectionHomogeneousRows_one (Y T : ℂ) :
    (fun i => (reflectionHomogeneousRows Y T i).coeff 1)=
      nextRows (-6*Y*(T+Y)) (24*Y^2) (48*Y^2*T^2) T := by
  funext i
  fin_cases i <;> simp only [reflectionHomogeneousRows,nextRows,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals
    rw [reflectionHomogeneous_one (by norm_num) (by omega)]
    norm_num
    ring

theorem hankel_coeff_zero (P : Fin 5 → Polynomial ℂ) :
    (hankel (P 0) (P 1) (P 2) (P 3) (P 4)).coeff 0=
      hankel ((P 0).coeff 0) ((P 1).coeff 0) ((P 2).coeff 0)
        ((P 3).coeff 0) ((P 4).coeff 0) := by
  norm_num [hankel,pow_succ]

theorem hankel_coeff_one (P : Fin 5 → Polynomial ℂ) :
    (hankel (P 0) (P 1) (P 2) (P 3) (P 4)).coeff 1=
      direction (fun i => (P i).coeff 0) (fun i => (P i).coeff 1) := by
  norm_num [hankel,direction,pow_succ,Polynomial.mul_coeff_one]
  ring

def minorHomogeneous (Y T : ℂ) : Polynomial ℂ :=
  -Polynomial.C ((12:ℂ)^18)*hankel
    (reflectionHomogeneousRows Y T 0) (reflectionHomogeneousRows Y T 1)
    (reflectionHomogeneousRows Y T 2) (reflectionHomogeneousRows Y T 3)
    (reflectionHomogeneousRows Y T 4)

theorem minorHomogeneous_zero (Y T : ℂ) : (minorHomogeneous Y T).coeff 0=0 := by
  unfold minorHomogeneous
  rw [neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,hankel_coeff_zero]
  have he := reflectionHomogeneousRows_zero Y T
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  have h4 := congrFun he 4
  rw [h0,h1,h2,h3,h4,leading_determinant]
  ring

theorem minorHomogeneous_one (Y T : ℂ) :
    (minorHomogeneous Y T).coeff 1= -4608*(12:ℂ)^18*Y^4*(T+Y)^2*T^14 := by
  unfold minorHomogeneous
  rw [neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,hankel_coeff_one,
    reflectionHomogeneousRows_zero,reflectionHomogeneousRows_one,principal_direction_source]
  ring

theorem pull_integerThirdMinor : pull integerThirdMinor=
    -C ((12:ℂ)^18)*hankel (reflection 2) (reflection 4) (reflection 6)
      (reflection 8) (reflection 10) := by
  simp only [integerThirdMinor,integerSignedMoment,map_sub,map_add,map_mul,map_pow,
    map_neg,map_one,map_ofNat,pull_integerReflection]
  apply MvPolynomial.funext
  intro v
  norm_num [hankel,map_ofNat]
  ring

theorem minorHomogeneous_eval (Y T h : ℂ) (hh : h≠0) :
    (minorHomogeneous Y T).eval h=
      h^21*eval (terminalPoint (Y/h) (T/h)) (pull integerThirdMinor) := by
  change (-Polynomial.C ((12:ℂ)^18)*hankel (reflectionHomogeneous 2 Y T)
    (reflectionHomogeneous 4 Y T) (reflectionHomogeneous 6 Y T)
    (reflectionHomogeneous 8 Y T) (reflectionHomogeneous 10 Y T)).eval h= _
  rw [pull_integerThirdMinor]
  simp only [hankel,Polynomial.eval_neg,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_pow,
    Polynomial.eval_ofNat,map_sub,map_add,map_mul,map_pow,map_neg,
    map_ofNat]
  rw [reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh]
  ring

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
