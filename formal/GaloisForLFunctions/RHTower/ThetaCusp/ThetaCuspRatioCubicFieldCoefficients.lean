import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicSourceFlow
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

private theorem coeff_const_pow (r : ℂ) (n i : ℕ) :
    (Polynomial.C r^n).coeff i=if i=0 then r^n else 0 := by
  rw [←Polynomial.C_pow,Polynomial.coeff_C]

private def lineB (r : ℂ) : Polynomial ℂ :=
  Polynomial.C r*(Polynomial.C (1/12)-Polynomial.C (7/72)*Polynomial.X)+
    Polynomial.C (1/144)*(Polynomial.C r)^2*Polynomial.X^2-
    Polynomial.C (7/432)*(Polynomial.C r)^2*Polynomial.X^3
private def lineV (r : ℂ) : Polynomial ℂ := 9-Polynomial.C r*Polynomial.X^2
private def lineW (r : ℂ) : Polynomial ℂ := 1-lineB r*Polynomial.X
private def lineH (r : ℂ) : Polynomial ℂ :=
  -Polynomial.C (4/3)*Polynomial.X^2*(3+Polynomial.X)*lineV r*lineW r
private def lineR (r : ℂ) : Polynomial ℂ :=
  Polynomial.C (8/3)*Polynomial.C r*Polynomial.X*(3+Polynomial.X)*lineV r*lineW r-
    12*lineV r*Polynomial.C r
private def lineT (r : ℂ) : Polynomial ℂ :=
  Polynomial.C (4/3)*lineB r*Polynomial.X*(3+Polynomial.X)*lineV r*lineW r-
    18*(Polynomial.C r-6*lineB r-Polynomial.C (2/3)*Polynomial.C r*Polynomial.X-
      4*lineB r*Polynomial.X+Polynomial.C (2/3)*Polynomial.C r*lineB r*Polynomial.X^2-
      Polynomial.C (4/9)*Polynomial.C r*Polynomial.X^2+
      Polynomial.C (4/9)*Polynomial.C r*lineB r*Polynomial.X^3)+
    6*Polynomial.C r*Polynomial.X*lineW r

private theorem sourceLines (r : ℂ) :
    affineLine r (nonlinearShift (infinityField .U))=lineH r ∧
    affineLine r (nonlinearShift (infinityField .K))=lineR r ∧
    affineLine r (nonlinearShift (infinityField .J))=lineT r := by
  norm_num [nonlinearCoord,nonlinearB,affineB,infinityField,driftSquare,deficit,speed,
    affineLineCoord,map_ofNat,lineH,lineR,lineT,lineB,lineV,lineW]

private theorem lineB_coeffs (r : ℂ) :
    (lineB r).coeff 0=r/12 ∧ (lineB r).coeff 1= -7*r/72 ∧
    (lineB r).coeff 2=r^2/144 ∧ (lineB r).coeff 3= -7*r^2/432 := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [lineB,coeff_const_pow,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ] <;> ring

private theorem lineW_coeffs (r : ℂ) :
    (lineW r).coeff 0=1 ∧ (lineW r).coeff 1= -r/12 ∧
    (lineW r).coeff 2=7*r/72 ∧ (lineW r).coeff 3= -r^2/144 := by
  have hb := lineB_coeffs r
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [lineW,Polynomial.coeff_one,Polynomial.coeff_mul,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      hb.1,hb.2.1,hb.2.2.1,hb.2.2.2] <;> ring

private theorem lineH_coeffs (r : ℂ) :
    (lineH r).coeff 0=0 ∧ (lineH r).coeff 1=0 ∧
    (lineH r).coeff 2= -36 ∧ (lineH r).coeff 3= -12+3*r := by
  have hw := lineW_coeffs r
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [lineH,lineV,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      hw.1,hw.2.1,hw.2.2.1,hw.2.2.2] <;> ring

private theorem lineR_coeffs (r : ℂ) :
    (lineR r).coeff 0= -108*r ∧ (lineR r).coeff 1=72*r ∧
    (lineR r).coeff 2=24*r+6*r^2 ∧ (lineR r).coeff 3= -3*r^2 := by
  have hw := lineW_coeffs r
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [lineR,lineV,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      hw.1,hw.2.1,hw.2.2.1,hw.2.2.2] <;> ring

private theorem lineT_coeffs (r : ℂ) :
    (lineT r).coeff 0= -9*r ∧ (lineT r).coeff 1=33*r/2 ∧
    (lineT r).coeff 2= -3*r/2-r^2 ∧ (lineT r).coeff 3= -7*r/6+r^2/4 := by
  have hb := lineB_coeffs r
  have hw := lineW_coeffs r
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [lineT,lineV,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2] <;> ring

theorem nonlinearField_J_coeffs (r : ℂ) :
    (affineLine r (nonlinearField .J)).coeff 0=0 ∧
    (affineLine r (nonlinearField .J)).coeff 1=0 ∧
    (affineLine r (nonlinearField .J)).coeff 2=0 ∧
    (affineLine r (nonlinearField .J)).coeff 3= -(21/8:ℂ)*r^2 := by
  have hs := sourceLines r
  have hh := lineH_coeffs r
  have hr := lineR_coeffs r
  have ht := lineT_coeffs r
  have hku : Coord.K≠Coord.U := by intro h; cases h
  have huk : Coord.U≠Coord.K := by intro h; cases h
  simp only [nonlinearField,map_sub,map_mul,hs.1,hs.2.1,hs.2.2]
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [nonlinearB,affineB,affineLineCoord,map_ofNat,coeff_const_pow,pderiv_mul,pderiv_pow,pderiv_X,
      Pi.single_apply,hku,huk,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,
      ht.1,ht.2.1,ht.2.2.1,ht.2.2.2] <;> ring

theorem nonlinearField_J_jets (r : ℂ) :
    planeValue r (nonlinearField .J)=0 ∧ planeJet1 r (nonlinearField .J)=0 ∧
    planeJet2 r (nonlinearField .J)=0 ∧ planeJet3 r (nonlinearField .J)= -(63/4:ℂ)*r^2 := by
  have he := nonlinearField_J_coeffs r
  simp only [planeJet1,planeJet2,planeJet3,planeValue,←affineLine_eval,
    ←affineLine_derivative,←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative]
  norm_num [he.1,he.2.1,he.2.2.1,he.2.2.2]
  ring

end
end HTGeometry.ThetaRatioInfinity
