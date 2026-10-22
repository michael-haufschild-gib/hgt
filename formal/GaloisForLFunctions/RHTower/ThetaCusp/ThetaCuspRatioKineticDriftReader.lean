import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticCofactors
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def driftReaderCoord (h : ℂ) : Coord → Polynomial ℂ
  | .U => Polynomial.C h
  | .K => Polynomial.X
  | .J => 0

def driftReader (h : ℂ) : Poly →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (driftReaderCoord h)

@[simp] theorem driftReader_C (h c : ℂ) :
    driftReader h (C c)=Polynomial.C c := by simp [driftReader]

@[simp] theorem driftReader_X (h : ℂ) (i : Coord) :
    driftReader h (X i)=driftReaderCoord h i := by simp [driftReader]

theorem driftReader_eval (P : Poly) (h v : ℂ) :
    (driftReader h P).eval v=eval (basePoint h v 0) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,driftReaderCoord,basePoint]

end
end HTGeometry.ThetaRatioKineticContraction
