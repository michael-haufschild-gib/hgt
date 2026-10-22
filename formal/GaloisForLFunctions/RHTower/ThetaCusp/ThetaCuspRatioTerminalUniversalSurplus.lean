import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalGradedCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Algebra

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioInfinity
open scoped QuadraticAlgebra

def surplusParameterA : Poly :=
  C (1/9)*(X Coord.K-1-C (1/72)*X Coord.K*(6*X Coord.K-7)*(9-X Coord.U))

def surplusParameterB : Poly := C (1/3)*(2-X Coord.K)

theorem surplusParameterA_eval (v k z : ℂ) :
    eval (basePoint v k z) surplusParameterA=boundaryA v k := by
  simp [surplusParameterA,boundaryA,boundaryMass,basePoint,map_ofNat]
  ring

theorem surplusParameterB_eval (v k z : ℂ) :
    eval (basePoint v k z) surplusParameterB=boundaryB k := by
  simp [surplusParameterB,boundaryB,basePoint,map_ofNat]
  ring

abbrev UniversalSurplusQuadratic := QuadraticAlgebra (Polynomial Poly)
  (Polynomial.C surplusParameterA-Polynomial.C (C (1/9))*Polynomial.X)
  (Polynomial.C surplusParameterB)

def universalSurplusLift : Poly →+* UniversalSurplusQuadratic :=
  (algebraMap (Polynomial Poly) UniversalSurplusQuadratic).comp Polynomial.C

def universalSurplusCoord : Coord → UniversalSurplusQuadratic
  | .U => universalSurplusLift (X .U)
  | .K => universalSurplusLift (X .K)
  | .J => QuadraticAlgebra.omega

def universalSurplusNormal : Poly →+* UniversalSurplusQuadratic :=
  eval₂Hom (universalSurplusLift.comp C) universalSurplusCoord

theorem universalSurplusNormal_X (i : Coord) :
    universalSurplusNormal (X i)=universalSurplusCoord i := by simp [universalSurplusNormal]

def universalSurplusCoefficient (P : Poly) (n : ℕ) : Poly :=
  (universalSurplusNormal P).re.coeff n+X Coord.J*(universalSurplusNormal P).im.coeff n

abbrev SourceSurplusAt (v k : ℂ) := QuadraticAlgebra (Polynomial ℂ)
  (Polynomial.C (boundaryA v k)-Polynomial.C (1/9)*Polynomial.X)
  (Polynomial.C (boundaryB k))

def sourceSurplusScalar (v k : ℂ) : ℂ →+* SourceSurplusAt v k :=
  (algebraMap (Polynomial ℂ) (SourceSurplusAt v k)).comp Polynomial.C

def sourceSurplusNormal (v k : ℂ) : Polynomial ℂ →+* SourceSurplusAt v k :=
  Polynomial.eval₂RingHom (sourceSurplusScalar v k) QuadraticAlgebra.omega

def universalSurplusChange (v k z : ℂ) : UniversalSurplusQuadratic →+* SourceSurplusAt v k :=
  quadraticChange (Polynomial.mapRingHom (eval (basePoint v k z)))
    (by simp [Polynomial.mapRingHom,surplusParameterA_eval])
    (by simp [Polynomial.mapRingHom,surplusParameterB_eval])

theorem universalSurplusChange_lift (v k z : ℂ) (P : Poly) :
    universalSurplusChange v k z (universalSurplusLift P)=
      algebraMap (Polynomial ℂ) _ (Polynomial.C (eval (basePoint v k z) P)) := by
  simp [universalSurplusChange,universalSurplusLift,quadraticChange_scalar,Polynomial.mapRingHom]

theorem universalSurplusChange_omega (v k z : ℂ) :
    universalSurplusChange v k z QuadraticAlgebra.omega=QuadraticAlgebra.omega :=
  quadraticChange_omega _ _ _

theorem universalSurplusChange_normal (P : Poly) (v k z : ℂ) :
    universalSurplusChange v k z (universalSurplusNormal P)=
      sourceSurplusNormal v k (kineticSourcePolynomial P v k) := by
  unfold kineticSourcePolynomial
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [universalSurplusNormal,universalSurplusChange_lift,sourceSurplusNormal,
      sourceSurplusScalar]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,universalSurplusNormal_X,MvPolynomial.eval₂Hom_X',hP]
    congr 1
    cases i <;> simp [universalSurplusCoord,kineticSourceCoord,universalSurplusChange_lift,
      universalSurplusChange_omega,sourceSurplusNormal,sourceSurplusScalar,basePoint]

theorem universalSurplusCoefficient_eval (P : Poly) (v k z : ℂ) (n : ℕ) :
    eval (basePoint v k z) (universalSurplusCoefficient P n)=
      ((sourceSurplusNormal v k (kineticSourcePolynomial P v k)).re+
        Polynomial.C z*(sourceSurplusNormal v k (kineticSourcePolynomial P v k)).im).coeff n := by
  have hr := congrArg QuadraticAlgebra.re (universalSurplusChange_normal P v k z)
  have hi := congrArg QuadraticAlgebra.im (universalSurplusChange_normal P v k z)
  change (universalSurplusNormal P).re.map (eval (basePoint v k z))=_ at hr
  change (universalSurplusNormal P).im.map (eval (basePoint v k z))=_ at hi
  have hrn := congrArg (fun Q : Polynomial ℂ => Q.coeff n) hr
  have hin := congrArg (fun Q : Polynomial ℂ => Q.coeff n) hi
  simp only [Polynomial.coeff_map] at hrn hin
  simp only [universalSurplusCoefficient,map_add,map_mul,eval_X,basePoint,
    Polynomial.coeff_add,Polynomial.coeff_C_mul,hrn,hin]

theorem universalSurplusCoefficient_flat (P : Poly) (k z : ℂ) (n : ℕ) :
    eval (basePoint 9 k z) (universalSurplusCoefficient P n)=
      (flatSurplus k z (kineticSourcePolynomial P 9 k)).coeff n := by
  have he := universalSurplusCoefficient_eval P 9 k z n
  have ha : boundaryA 9 k=(k-1)/9 := by simp [boundaryA,boundaryMass]
  unfold sourceSurplusNormal sourceSurplusScalar SourceSurplusAt at he
  rw [ha] at he
  exact he


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
