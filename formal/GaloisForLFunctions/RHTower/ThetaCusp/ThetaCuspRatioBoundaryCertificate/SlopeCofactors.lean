import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Dynamics
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def cubic75 {R : Type*} [CommRing R] (a b c d e : R) : R :=
  -a*c*e+a*d^2+b^2*e-2*b*c*d+c^3

def cof2_75 {R : Type*} [CommRing R] (c d e : R) := -c*e+d^2
def cof4_75 {R : Type*} [CommRing R] (b c d e : R) := 2*b*e-2*c*d
def cof6_75 {R : Type*} [CommRing R] (a b c d e : R) := -a*e-2*b*d+3*c^2
def cof8_75 {R : Type*} [CommRing R] (a b c d : R) := 2*a*d-2*b*c
def cof10_75 {R : Type*} [CommRing R] (a b c : R) := -a*c+b^2

theorem flow_ofNat75 (f : Coord → Poly) (n : ℕ) [n.AtLeastTwo] :
    flow f (ofNat(n) : Poly)=0 := by simp [flow]
theorem flow_one75 (f : Coord → Poly) : flow f 1=0 := by simp [flow]

theorem slope_cofactors75 : ThetaRatioSquare.slope =
    cof2_75 moment6 moment8 moment10*(seed*squareLie moment2-2*moment2*squareLie seed)+
    cof4_75 moment4 moment6 moment8 moment10*(seed*squareLie moment4-2*moment4*squareLie seed)+
    cof6_75 moment2 moment4 moment6 moment8 moment10*(seed*squareLie moment6-2*moment6*squareLie seed)+
    cof8_75 moment2 moment4 moment6 moment8*(seed*squareLie moment8-2*moment8*squareLie seed)+
    cof10_75 moment2 moment4 moment6*(seed*squareLie moment10-2*moment10*squareLie seed) := by
  unfold ThetaRatioSquare.slope minor cof2_75 cof4_75 cof6_75 cof8_75 cof10_75
  simp only [squareLie,flow_sub75,flow_neg75,flow_add,flow_mul,flow_pow75,flow_ofNat75]
  norm_num only
  ring

theorem squareLie_seed75 : squareLie seed=6*squareField .K := by
  unfold seed
  simp only [squareLie,flow_sub75,flow_mul,flow_ofNat75,flow_one75,flow_X]
  ring

end
end HTGeometry.ThetaRatioInfinity
