import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Numerals
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

theorem squareFlow_explicit75 (P : Poly) : squareLie P=
    pderiv Coord.U P*squareField .U+
      (pderiv Coord.K P*squareField .K+pderiv Coord.J P*squareField .J) := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  simp [squareLie,flow,hu]

theorem flow_sub75 (f : Coord → Poly) (P Q : Poly) :
    flow f (P-Q)=flow f P-flow f Q := by
  simp [flow,sub_mul,Finset.sum_sub_distrib]

theorem flow_neg75 (f : Coord → Poly) (P : Poly) : flow f (-P)= -flow f P := by
  simp [flow,Finset.sum_neg_distrib]

theorem flow_pow75 (f : Coord → Poly) (P : Poly) (n : ℕ) :
    flow f (P^n)=(n:Poly)*P^(n-1)*flow f P := by
  unfold flow
  simp only [pderiv_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end HTGeometry.ThetaRatioInfinity
