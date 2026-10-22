import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockSlope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.SlopeCofactors
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def kineticUp (d : ℕ) (c : Poly) : Poly :=
  -(X Coord.U)^3*(12+4*X Coord.U)*X Coord.K*pderiv Coord.U c+
    C (d:ℂ)*(X Coord.U)^2*(12+4*X Coord.U)*X Coord.K*c

def kineticStay (j : ℕ) (c : Poly) : Poly :=
  12*X Coord.U*X Coord.K*(9-X Coord.K)*pderiv Coord.K c+
    (j:Poly)*((12*X Coord.U+8*(X Coord.U)^2)*X Coord.K-
      6*X Coord.U*(9-X Coord.K))*c

def kineticDown (j : ℕ) (c : Poly) : Poly :=
  (j:Poly)*(6*(9-X Coord.K)-36*X Coord.U-24*(X Coord.U)^2)*c

theorem clockFlow_kinetic_monomial (d j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    clockFlow d ((X Coord.J)^j*c)=
      (X Coord.J)^(j+1)*kineticUp d c+(X Coord.J)^j*kineticStay j c+
        (X Coord.J)^(j-1)*kineticDown j c := by
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  unfold clockFlow clockLie
  rw [flow_expand]
  simp only [pderiv_mul,pderiv_pow]
  cases j with
  | zero =>
    norm_num [clockField,kineticUp,kineticStay,
      kineticDown,pderiv_X,Pi.single_apply,hUJ,hKJ,hc]
    ring
  | succ j =>
    norm_num [clockField,kineticUp,kineticStay,
      kineticDown,pderiv_X,Pi.single_apply,hUJ,hKJ,hc,pow_succ]
    ring

def clockSlopeBlock (d : ℕ) (P : Poly) : Poly :=
  (6-X Coord.U)*clockFlow d P-
    12*(X Coord.U)^2*(12+4*X Coord.U)*X Coord.K*X Coord.J*P

theorem clearSlope_cofactors : clearSlope=
    cof2_75 clearMoment6 clearMoment8 clearMoment10*clockSlopeBlock 3 clearMoment2+
    cof4_75 clearMoment4 clearMoment6 clearMoment8 clearMoment10*clockSlopeBlock 5 clearMoment4+
    cof6_75 clearMoment2 clearMoment4 clearMoment6 clearMoment8 clearMoment10*clockSlopeBlock 7 clearMoment6+
    cof8_75 clearMoment2 clearMoment4 clearMoment6 clearMoment8*clockSlopeBlock 9 clearMoment8+
    cof10_75 clearMoment2 clearMoment4 clearMoment6*clockSlopeBlock 11 clearMoment10 := by
  unfold clearSlope clockSlopeBlock clockFlow clockLie clearMinor
    cof2_75 cof4_75 cof6_75 cof8_75 cof10_75
  simp only [flow_add,flow_sub75,flow_neg75,flow_mul,flow_pow75,flow_ofNat75]
  norm_num only [map_ofNat]
  ring

def kineticSlopeUp (d : ℕ) (c : Poly) : Poly :=
  (6-X Coord.U)*kineticUp d c-12*(X Coord.U)^2*(12+4*X Coord.U)*X Coord.K*c

theorem clockSlopeBlock_kinetic (d j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    clockSlopeBlock d ((X Coord.J)^j*c)=
      (X Coord.J)^(j+1)*kineticSlopeUp d c+
        (X Coord.J)^j*((6-X Coord.U)*kineticStay j c)+
        (X Coord.J)^(j-1)*((6-X Coord.U)*kineticDown j c) := by
  unfold clockSlopeBlock kineticSlopeUp
  rw [clockFlow_kinetic_monomial d j c hc]
  simp only [pow_succ]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
