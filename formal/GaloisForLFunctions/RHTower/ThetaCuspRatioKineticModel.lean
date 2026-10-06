import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFlow
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCoefficients2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCoefficients4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCoefficients6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCoefficients8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticCoefficients10
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

abbrev KineticPolynomial := Polynomial Poly

def kineticRead : KineticPolynomial →+* Poly := Polynomial.evalRingHom (X Coord.J)

@[simp] theorem kineticRead_C (c : Poly) : kineticRead (Polynomial.C c)=c := by
  simp [kineticRead]

@[simp] theorem kineticRead_X : kineticRead Polynomial.X=X Coord.J := by
  simp [kineticRead]

def kineticBlockTerm (d j : ℕ) (c : Poly) : KineticPolynomial :=
  Polynomial.C (kineticSlopeUp d c)*Polynomial.X^(j+1)+
    Polynomial.C ((6-X Coord.U)*kineticStay j c)*Polynomial.X^j+
    Polynomial.C ((6-X Coord.U)*kineticDown j c)*Polynomial.X^(j-1)

theorem kineticBlockTerm_read (d j : ℕ) (c : Poly) (hc : pderiv Coord.J c=0) :
    kineticRead (kineticBlockTerm d j c)=clockSlopeBlock d ((X Coord.J)^j*c) := by
  rw [clockSlopeBlock_kinetic d j c hc]
  simp only [kineticBlockTerm,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

theorem clockSlopeBlock_add (d : ℕ) (P Q : Poly) :
    clockSlopeBlock d (P+Q)=clockSlopeBlock d P+clockSlopeBlock d Q := by
  simp only [clockSlopeBlock,clockFlow_add]
  ring

def kineticMoment2 : KineticPolynomial :=
  (Polynomial.C clearMoment2KineticCoeff0*Polynomial.X^0 + (Polynomial.C clearMoment2KineticCoeff1*Polynomial.X^1 + Polynomial.C clearMoment2KineticCoeff2*Polynomial.X^2))

theorem kineticMoment2_read : kineticRead kineticMoment2=clearMoment2 := by
  rw [clearMoment2_kinetic]
  simp only [kineticMoment2,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

def kineticBlock2 : KineticPolynomial :=
  (kineticBlockTerm 3 0 clearMoment2KineticCoeff0 + (kineticBlockTerm 3 1 clearMoment2KineticCoeff1 + kineticBlockTerm 3 2 clearMoment2KineticCoeff2))

theorem kineticBlock2_read : kineticRead kineticBlock2=clockSlopeBlock 3 clearMoment2 := by
  rw [clearMoment2_kinetic]
  simp only [kineticBlock2,map_add,clockSlopeBlock_add]
  rw [kineticBlockTerm_read 3 0 clearMoment2KineticCoeff0 clearMoment2KineticCoeff0_noJ,kineticBlockTerm_read 3 1 clearMoment2KineticCoeff1 clearMoment2KineticCoeff1_noJ,kineticBlockTerm_read 3 2 clearMoment2KineticCoeff2 clearMoment2KineticCoeff2_noJ]

def kineticMoment4 : KineticPolynomial :=
  ((Polynomial.C clearMoment4KineticCoeff0*Polynomial.X^0 + Polynomial.C clearMoment4KineticCoeff1*Polynomial.X^1) + (Polynomial.C clearMoment4KineticCoeff2*Polynomial.X^2 + (Polynomial.C clearMoment4KineticCoeff3*Polynomial.X^3 + Polynomial.C clearMoment4KineticCoeff4*Polynomial.X^4)))

theorem kineticMoment4_read : kineticRead kineticMoment4=clearMoment4 := by
  rw [clearMoment4_kinetic]
  simp only [kineticMoment4,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

def kineticBlock4 : KineticPolynomial :=
  ((kineticBlockTerm 5 0 clearMoment4KineticCoeff0 + kineticBlockTerm 5 1 clearMoment4KineticCoeff1) + (kineticBlockTerm 5 2 clearMoment4KineticCoeff2 + (kineticBlockTerm 5 3 clearMoment4KineticCoeff3 + kineticBlockTerm 5 4 clearMoment4KineticCoeff4)))

theorem kineticBlock4_read : kineticRead kineticBlock4=clockSlopeBlock 5 clearMoment4 := by
  rw [clearMoment4_kinetic]
  simp only [kineticBlock4,map_add,clockSlopeBlock_add]
  rw [kineticBlockTerm_read 5 0 clearMoment4KineticCoeff0 clearMoment4KineticCoeff0_noJ,kineticBlockTerm_read 5 1 clearMoment4KineticCoeff1 clearMoment4KineticCoeff1_noJ,kineticBlockTerm_read 5 2 clearMoment4KineticCoeff2 clearMoment4KineticCoeff2_noJ,kineticBlockTerm_read 5 3 clearMoment4KineticCoeff3 clearMoment4KineticCoeff3_noJ,kineticBlockTerm_read 5 4 clearMoment4KineticCoeff4 clearMoment4KineticCoeff4_noJ]

def kineticMoment6 : KineticPolynomial :=
  ((Polynomial.C clearMoment6KineticCoeff0*Polynomial.X^0 + (Polynomial.C clearMoment6KineticCoeff1*Polynomial.X^1 + Polynomial.C clearMoment6KineticCoeff2*Polynomial.X^2)) + ((Polynomial.C clearMoment6KineticCoeff3*Polynomial.X^3 + Polynomial.C clearMoment6KineticCoeff4*Polynomial.X^4) + (Polynomial.C clearMoment6KineticCoeff5*Polynomial.X^5 + Polynomial.C clearMoment6KineticCoeff6*Polynomial.X^6)))

theorem kineticMoment6_read : kineticRead kineticMoment6=clearMoment6 := by
  rw [clearMoment6_kinetic]
  simp only [kineticMoment6,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

def kineticBlock6 : KineticPolynomial :=
  ((kineticBlockTerm 7 0 clearMoment6KineticCoeff0 + (kineticBlockTerm 7 1 clearMoment6KineticCoeff1 + kineticBlockTerm 7 2 clearMoment6KineticCoeff2)) + ((kineticBlockTerm 7 3 clearMoment6KineticCoeff3 + kineticBlockTerm 7 4 clearMoment6KineticCoeff4) + (kineticBlockTerm 7 5 clearMoment6KineticCoeff5 + kineticBlockTerm 7 6 clearMoment6KineticCoeff6)))

theorem kineticBlock6_read : kineticRead kineticBlock6=clockSlopeBlock 7 clearMoment6 := by
  rw [clearMoment6_kinetic]
  simp only [kineticBlock6,map_add,clockSlopeBlock_add]
  rw [kineticBlockTerm_read 7 0 clearMoment6KineticCoeff0 clearMoment6KineticCoeff0_noJ,kineticBlockTerm_read 7 1 clearMoment6KineticCoeff1 clearMoment6KineticCoeff1_noJ,kineticBlockTerm_read 7 2 clearMoment6KineticCoeff2 clearMoment6KineticCoeff2_noJ,kineticBlockTerm_read 7 3 clearMoment6KineticCoeff3 clearMoment6KineticCoeff3_noJ,kineticBlockTerm_read 7 4 clearMoment6KineticCoeff4 clearMoment6KineticCoeff4_noJ,kineticBlockTerm_read 7 5 clearMoment6KineticCoeff5 clearMoment6KineticCoeff5_noJ,kineticBlockTerm_read 7 6 clearMoment6KineticCoeff6 clearMoment6KineticCoeff6_noJ]

def kineticMoment8 : KineticPolynomial :=
  (((Polynomial.C clearMoment8KineticCoeff0*Polynomial.X^0 + Polynomial.C clearMoment8KineticCoeff1*Polynomial.X^1) + (Polynomial.C clearMoment8KineticCoeff2*Polynomial.X^2 + Polynomial.C clearMoment8KineticCoeff3*Polynomial.X^3)) + ((Polynomial.C clearMoment8KineticCoeff4*Polynomial.X^4 + Polynomial.C clearMoment8KineticCoeff5*Polynomial.X^5) + (Polynomial.C clearMoment8KineticCoeff6*Polynomial.X^6 + (Polynomial.C clearMoment8KineticCoeff7*Polynomial.X^7 + Polynomial.C clearMoment8KineticCoeff8*Polynomial.X^8))))

theorem kineticMoment8_read : kineticRead kineticMoment8=clearMoment8 := by
  rw [clearMoment8_kinetic]
  simp only [kineticMoment8,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

def kineticBlock8 : KineticPolynomial :=
  (((kineticBlockTerm 9 0 clearMoment8KineticCoeff0 + kineticBlockTerm 9 1 clearMoment8KineticCoeff1) + (kineticBlockTerm 9 2 clearMoment8KineticCoeff2 + kineticBlockTerm 9 3 clearMoment8KineticCoeff3)) + ((kineticBlockTerm 9 4 clearMoment8KineticCoeff4 + kineticBlockTerm 9 5 clearMoment8KineticCoeff5) + (kineticBlockTerm 9 6 clearMoment8KineticCoeff6 + (kineticBlockTerm 9 7 clearMoment8KineticCoeff7 + kineticBlockTerm 9 8 clearMoment8KineticCoeff8))))

theorem kineticBlock8_read : kineticRead kineticBlock8=clockSlopeBlock 9 clearMoment8 := by
  rw [clearMoment8_kinetic]
  simp only [kineticBlock8,map_add,clockSlopeBlock_add]
  rw [kineticBlockTerm_read 9 0 clearMoment8KineticCoeff0 clearMoment8KineticCoeff0_noJ,kineticBlockTerm_read 9 1 clearMoment8KineticCoeff1 clearMoment8KineticCoeff1_noJ,kineticBlockTerm_read 9 2 clearMoment8KineticCoeff2 clearMoment8KineticCoeff2_noJ,kineticBlockTerm_read 9 3 clearMoment8KineticCoeff3 clearMoment8KineticCoeff3_noJ,kineticBlockTerm_read 9 4 clearMoment8KineticCoeff4 clearMoment8KineticCoeff4_noJ,kineticBlockTerm_read 9 5 clearMoment8KineticCoeff5 clearMoment8KineticCoeff5_noJ,kineticBlockTerm_read 9 6 clearMoment8KineticCoeff6 clearMoment8KineticCoeff6_noJ,kineticBlockTerm_read 9 7 clearMoment8KineticCoeff7 clearMoment8KineticCoeff7_noJ,kineticBlockTerm_read 9 8 clearMoment8KineticCoeff8 clearMoment8KineticCoeff8_noJ]

def kineticMoment10 : KineticPolynomial :=
  (((Polynomial.C clearMoment10KineticCoeff0*Polynomial.X^0 + Polynomial.C clearMoment10KineticCoeff1*Polynomial.X^1) + (Polynomial.C clearMoment10KineticCoeff2*Polynomial.X^2 + (Polynomial.C clearMoment10KineticCoeff3*Polynomial.X^3 + Polynomial.C clearMoment10KineticCoeff4*Polynomial.X^4))) + ((Polynomial.C clearMoment10KineticCoeff5*Polynomial.X^5 + (Polynomial.C clearMoment10KineticCoeff6*Polynomial.X^6 + Polynomial.C clearMoment10KineticCoeff7*Polynomial.X^7)) + (Polynomial.C clearMoment10KineticCoeff8*Polynomial.X^8 + (Polynomial.C clearMoment10KineticCoeff9*Polynomial.X^9 + Polynomial.C clearMoment10KineticCoeff10*Polynomial.X^10))))

theorem kineticMoment10_read : kineticRead kineticMoment10=clearMoment10 := by
  rw [clearMoment10_kinetic]
  simp only [kineticMoment10,map_add,map_mul,map_pow,kineticRead_C,kineticRead_X]
  ring

def kineticBlock10 : KineticPolynomial :=
  (((kineticBlockTerm 11 0 clearMoment10KineticCoeff0 + kineticBlockTerm 11 1 clearMoment10KineticCoeff1) + (kineticBlockTerm 11 2 clearMoment10KineticCoeff2 + (kineticBlockTerm 11 3 clearMoment10KineticCoeff3 + kineticBlockTerm 11 4 clearMoment10KineticCoeff4))) + ((kineticBlockTerm 11 5 clearMoment10KineticCoeff5 + (kineticBlockTerm 11 6 clearMoment10KineticCoeff6 + kineticBlockTerm 11 7 clearMoment10KineticCoeff7)) + (kineticBlockTerm 11 8 clearMoment10KineticCoeff8 + (kineticBlockTerm 11 9 clearMoment10KineticCoeff9 + kineticBlockTerm 11 10 clearMoment10KineticCoeff10))))

theorem kineticBlock10_read : kineticRead kineticBlock10=clockSlopeBlock 11 clearMoment10 := by
  rw [clearMoment10_kinetic]
  simp only [kineticBlock10,map_add,clockSlopeBlock_add]
  rw [kineticBlockTerm_read 11 0 clearMoment10KineticCoeff0 clearMoment10KineticCoeff0_noJ,kineticBlockTerm_read 11 1 clearMoment10KineticCoeff1 clearMoment10KineticCoeff1_noJ,kineticBlockTerm_read 11 2 clearMoment10KineticCoeff2 clearMoment10KineticCoeff2_noJ,kineticBlockTerm_read 11 3 clearMoment10KineticCoeff3 clearMoment10KineticCoeff3_noJ,kineticBlockTerm_read 11 4 clearMoment10KineticCoeff4 clearMoment10KineticCoeff4_noJ,kineticBlockTerm_read 11 5 clearMoment10KineticCoeff5 clearMoment10KineticCoeff5_noJ,kineticBlockTerm_read 11 6 clearMoment10KineticCoeff6 clearMoment10KineticCoeff6_noJ,kineticBlockTerm_read 11 7 clearMoment10KineticCoeff7 clearMoment10KineticCoeff7_noJ,kineticBlockTerm_read 11 8 clearMoment10KineticCoeff8 clearMoment10KineticCoeff8_noJ,kineticBlockTerm_read 11 9 clearMoment10KineticCoeff9 clearMoment10KineticCoeff9_noJ,kineticBlockTerm_read 11 10 clearMoment10KineticCoeff10 clearMoment10KineticCoeff10_noJ]

def completeKineticSlope : KineticPolynomial :=
    cof2_75 kineticMoment6 kineticMoment8 kineticMoment10*kineticBlock2+
    cof4_75 kineticMoment4 kineticMoment6 kineticMoment8 kineticMoment10*kineticBlock4+
    cof6_75 kineticMoment2 kineticMoment4 kineticMoment6 kineticMoment8 kineticMoment10*kineticBlock6+
    cof8_75 kineticMoment2 kineticMoment4 kineticMoment6 kineticMoment8*kineticBlock8+
    cof10_75 kineticMoment2 kineticMoment4 kineticMoment6*kineticBlock10

theorem completeKineticSlope_read : kineticRead completeKineticSlope=clearSlope := by
  rw [clearSlope_cofactors]
  simp only [completeKineticSlope,cof2_75,cof4_75,cof6_75,cof8_75,cof10_75,
    map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    kineticMoment2_read,kineticMoment4_read,kineticMoment6_read,kineticMoment8_read,kineticMoment10_read,
    kineticBlock2_read,kineticBlock4_read,kineticBlock6_read,kineticBlock8_read,kineticBlock10_read]

end
end HTGeometry.ThetaRatioKineticContraction
