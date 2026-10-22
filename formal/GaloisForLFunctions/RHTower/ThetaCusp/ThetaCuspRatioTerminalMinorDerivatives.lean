import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalReflectedDerivatives
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalHomogeneousMinor

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def linearRows (F N : Fin 5 → ℂ) (i : Fin 5) : Polynomial ℂ :=
  Polynomial.C (F i)+Polynomial.X*Polynomial.C (N i)

theorem direction_coeff_zero (P Q : Fin 5 → Polynomial ℂ) :
    (direction P Q).coeff 0=direction (fun i => (P i).coeff 0) (fun i => (Q i).coeff 0) := by
  norm_num [direction,pow_succ]

theorem direction_coeff_one_linearRows (P Q : Fin 5 → Polynomial ℂ) :
    (direction P Q).coeff 1=
      (direction (linearRows (fun i => (P i).coeff 0) (fun i => (P i).coeff 1))
        (linearRows (fun i => (Q i).coeff 0) (fun i => (Q i).coeff 1))).coeff 1 := by
  norm_num [direction,pow_succ,Polynomial.mul_coeff_one,linearRows]

theorem direction_leadingRows (A B a b T : ℂ) :
    direction (leadingRows A B T) (leadingRows a b T)=0 := by
  simp [direction,leadingRows]
  ring

theorem direction_linearRows_swap (F N G L : Fin 5 → ℂ) :
    (direction (linearRows F N) (linearRows G L)).coeff 1=
      (direction (linearRows F G) (linearRows N L)).coeff 1 := by
  norm_num [direction,linearRows,pow_succ,Polynomial.mul_coeff_one]
  ring

theorem linearRows_leading (A B a b T : ℂ) :
    linearRows (leadingRows A B T) (leadingRows a b T)=
      leadingRows (Polynomial.C A+Polynomial.X*Polynomial.C a)
        (Polynomial.C B+Polynomial.X*Polynomial.C b) (Polynomial.C T) := by
  funext i
  fin_cases i <;> simp [linearRows,leadingRows] <;> ring

theorem linearRows_next (C D E c d e T : ℂ) :
    linearRows (nextRows C D E T) (nextRows c d e T)=
      nextRows (Polynomial.C C+Polynomial.X*Polynomial.C c)
        (Polynomial.C D+Polynomial.X*Polynomial.C d)
        (Polynomial.C E+Polynomial.X*Polynomial.C e) (Polynomial.C T) := by
  funext i
  fin_cases i <;> simp [linearRows,nextRows,map_ofNat] <;> ring

theorem direction_linearRows_next (A B C D E a b c d e T : ℂ) :
    (direction (linearRows (leadingRows A B T) (nextRows C D E T))
      (linearRows (leadingRows a b T) (nextRows c d e T))).coeff 1=
      8*(a*B*C+A*b*C+A*B*c)*T^12 := by
  rw [direction_linearRows_swap,linearRows_leading,linearRows_next,principal_direction,
    ←Polynomial.C_pow]
  norm_num [Polynomial.mul_coeff_one]
  simp only [←Polynomial.C_pow,Polynomial.coeff_C_zero,Polynomial.coeff_C_succ]
  ring

def reflectionYHomogeneousRows (Y T : ℂ) : Fin 5 → Polynomial ℂ :=
  ![reflectionYHomogeneous 2 Y T,reflectionYHomogeneous 4 Y T,
    reflectionYHomogeneous 6 Y T,reflectionYHomogeneous 8 Y T,reflectionYHomogeneous 10 Y T]

def reflectionTHomogeneousRows (Y T : ℂ) : Fin 5 → Polynomial ℂ :=
  ![reflectionTHomogeneous 2 Y T,reflectionTHomogeneous 4 Y T,
    reflectionTHomogeneous 6 Y T,reflectionTHomogeneous 8 Y T,reflectionTHomogeneous 10 Y T]

theorem reflectionYHomogeneousRows_zero (Y T : ℂ) :
    (fun i => (reflectionYHomogeneousRows Y T i).coeff 0)=
      leadingRows (-12*(T+2*Y)*T) (16*Y*T) T := by
  funext i
  fin_cases i <;> simp only [reflectionYHomogeneousRows,leadingRows,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals
    rw [reflectionYHomogeneous_zero (by norm_num) (by omega)]
    norm_num <;> ring

theorem reflectionYHomogeneousRows_one (Y T : ℂ) :
    (fun i => (reflectionYHomogeneousRows Y T i).coeff 1)=
      nextRows (-6*(T+2*Y)) (48*Y) (96*Y*T^2) T := by
  funext i
  fin_cases i <;> simp only [reflectionYHomogeneousRows,nextRows,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals
    rw [reflectionYHomogeneous_one (by norm_num) (by omega)]
    norm_num
    ring

def minorYHomogeneous (Y T : ℂ) : Polynomial ℂ :=
  -Polynomial.C ((12:ℂ)^18)*direction (reflectionHomogeneousRows Y T)
    (reflectionYHomogeneousRows Y T)

def minorTHomogeneous (Y T : ℂ) : Polynomial ℂ :=
  -Polynomial.C ((12:ℂ)^18)*direction (reflectionHomogeneousRows Y T)
    (reflectionTHomogeneousRows Y T)

theorem minorYHomogeneous_zero (Y T : ℂ) : (minorYHomogeneous Y T).coeff 0=0 := by
  rw [minorYHomogeneous,neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,
    direction_coeff_zero,reflectionHomogeneousRows_zero,reflectionYHomogeneousRows_zero,
    direction_leadingRows]
  ring

theorem minorYHomogeneous_one (Y T : ℂ) :
    (minorYHomogeneous Y T).coeff 1= -9216*(12:ℂ)^18*Y^3*(T+Y)*(2*T+3*Y)*T^14 := by
  rw [minorYHomogeneous,neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,
    direction_coeff_one_linearRows,reflectionHomogeneousRows_zero,reflectionHomogeneousRows_one,
    reflectionYHomogeneousRows_zero,reflectionYHomogeneousRows_one,direction_linearRows_next]
  ring

theorem minorTHomogeneous_zero (Y T : ℂ) : (minorTHomogeneous Y T).coeff 0=0 := by
  rw [minorTHomogeneous,neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,direction_coeff_zero,
    reflectionHomogeneousRows_zero]
  simp only [direction,reflectionTHomogeneousRows,leadingRows,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  rw [reflectionTHomogeneous_zero (by norm_num) (by omega),
    reflectionTHomogeneous_zero (by norm_num) (by omega),
    reflectionTHomogeneous_zero (by norm_num) (by omega),
    reflectionTHomogeneous_zero (by norm_num) (by omega),
    reflectionTHomogeneous_zero (by norm_num) (by omega)]
  norm_num
  ring

theorem pderiv_hankel (i : Coord) (P : Fin 5 → Poly) :
    pderiv i (hankel (P 0) (P 1) (P 2) (P 3) (P 4))=
      direction P (fun j => pderiv i (P j)) := by
  simp [hankel,direction]
  ring

theorem minorYHomogeneous_eval (Y T h : ℂ) (hh : h≠0) :
    (minorYHomogeneous Y T).eval h=
      h^20*eval (terminalPoint (Y/h) (T/h)) (pderiv Coord.K (pull integerThirdMinor)) := by
  rw [pull_integerThirdMinor]
  have hp := pderiv_hankel Coord.K
    (![reflection 2,reflection 4,reflection 6,reflection 8,reflection 10])
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hp
  change (minorYHomogeneous Y T).eval h = h^20*eval _
    (pderiv Coord.K (-C ((12:ℂ)^18)*hankel (reflection 2) (reflection 4)
      (reflection 6) (reflection 8) (reflection 10)))
  rw [neg_mul,map_neg,pderiv_C_mul,hp]
  simp only [minorYHomogeneous,direction,reflectionHomogeneousRows,reflectionYHomogeneousRows,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,Polynomial.eval_neg,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_ofNat,map_neg,map_mul,map_sub,
    map_add,map_pow,map_ofNat]
  rw [reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionYHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionYHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionYHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionYHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionYHomogeneous_eval (by norm_num) (by omega) _ _ _ hh]
  norm_num
  ring

theorem minorTHomogeneous_eval (Y T h : ℂ) (hh : h≠0) :
    (minorTHomogeneous Y T).eval h=
      h^20*eval (terminalPoint (Y/h) (T/h)) (pderiv Coord.J (pull integerThirdMinor)) := by
  rw [pull_integerThirdMinor]
  have hp := pderiv_hankel Coord.J
    (![reflection 2,reflection 4,reflection 6,reflection 8,reflection 10])
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hp
  change (minorTHomogeneous Y T).eval h = h^20*eval _
    (pderiv Coord.J (-C ((12:ℂ)^18)*hankel (reflection 2) (reflection 4)
      (reflection 6) (reflection 8) (reflection 10)))
  rw [neg_mul,map_neg,pderiv_C_mul,hp]
  simp only [minorTHomogeneous,direction,reflectionHomogeneousRows,reflectionTHomogeneousRows,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,Polynomial.eval_neg,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_ofNat,map_neg,map_mul,map_sub,
    map_add,map_pow,map_ofNat]
  rw [reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionTHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionTHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionTHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionTHomogeneous_eval (by norm_num) (by omega) _ _ _ hh,
    reflectionTHomogeneous_eval (by norm_num) (by omega) _ _ _ hh]
  norm_num
  ring


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
