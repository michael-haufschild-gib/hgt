import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-! # Exact modular polynomials for the even rank-four theta seam -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
open GaloisForLFunctions.HTGeometry

/-- The seven normalized signed even reflection moments at the algebraic seam. -/
def modularThetaEvenSeamMomentPolynomial {K : Type*} [Field K] (n : Fin 7) (X : K) : K :=
  match n.val with
  | 0 => (9/64) + (-3/64)*X^1 + (1/256)*X^2
  | 1 => (45/64) + (-165/256)*X^1 + (21/256)*X^2 + (1/1024)*X^3
  | 2 => (765/64) + (-2505/128)*X^1 + (4461/1024)*X^2 + (77/1024)*X^3 + (27/4096)*X^4
  | 3 => (24345/64) + (-243615/256)*X^1 + (333759/1024)*X^2 + (31519/4096)*X^3 + (8199/4096)*X^4 + (-21/16384)*X^5
  | 4 => (1207665/64) + (-2122095/32)*X^1 + (16407993/512)*X^2 + (1024127/1024)*X^3 + (7963857/16384)*X^4 + (-30027/16384)*X^5 + (5133/65536)*X^6
  | 5 => (85066245/64) + (-1591823865/256)*X^1 + (2049802467/512)*X^2 + (327670217/2048)*X^3 + (1966854177/16384)*X^4 + (-62366877/65536)*X^5 + (3218985/65536)*X^6 + (-725859/262144)*X^7
  | _ => (8028542565/64) + (-96262740255/128)*X^1 + (634560122211/1024)*X^2 + (1975395347/64)*X^3 + (529421297031/16384)*X^4 + (-13501200603/32768)*X^5 + (6251467509/262144)*X^6 + (-888527835/262144)*X^7 + (-10466793/1048576)*X^8

/-- Normalized leading even rank-three determinant at the seam. -/
def modularThetaEvenSeamHeadPolynomial {K : Type*} [Field K] (X : K) : K :=
    (3444525/512) +
    (-80754975/2048)*X^1 +
    (4194195795/65536)*X^2 +
    (-2646917595/65536)*X^3 +
    (5201727255/524288)*X^4 +
    (-1723813569/1048576)*X^5 +
    (4581650223/16777216)*X^6 +
    (-612571059/16777216)*X^7 +
    (35927199/16777216)*X^8 +
    (1999197/268435456)*X^9 +
    (-117855/134217728)*X^10 +
    (-13245/536870912)*X^11 +
    (14025/8589934592)*X^12

/-- Normalized even rank-four determinant at the seam. -/
def modularThetaEvenSeamFourPolynomial {K : Type*} [Field K] (X : K) : K :=
    (6591529153125/64) +
    (-166253013084375/128)*X^1 +
    (5337820308200625/1024)*X^2 +
    (-37022043092855625/4096)*X^3 +
    (7787088853340790375/1048576)*X^4 +
    (-1646495212914961875/524288)*X^5 +
    (4126958864384131125/4194304)*X^6 +
    (-2873522866395593475/8388608)*X^7 +
    (9674455820287175685/134217728)*X^8 +
    (-1298405983277063295/134217728)*X^9 +
    (1072501486261175745/1073741824)*X^10 +
    (-228446494288779897/2147483648)*X^11 +
    (639767688325868871/68719476736)*X^12 +
    (-9963970860000735/17179869184)*X^13 +
    (3589481195177553/68719476736)*X^14 +
    (-340179430007961/137438953472)*X^15 +
    (-21683072191761/274877906944)*X^16 +
    (2370080393613/549755813888)*X^17 +
    (-57754209573/8796093022208)*X^18 +
    (-15503237325/17592186044416)*X^19 +
    (-14267390625/70368744177664)*X^20

/-- Exact leading determinant of the seven symbolic seam moments. -/
theorem modularThetaEvenSeamHeadPolynomial_eq {K : Type*} [Field K] [CharZero K] (X : K) :
    let m := fun n => modularThetaEvenSeamMomentPolynomial n X
    m 0*m 2*m 4-m 0*(m 3)^2-(m 1)^2*m 4+2*m 1*m 2*m 3-(m 2)^3 =
      modularThetaEvenSeamHeadPolynomial X := by
  norm_num [modularThetaEvenSeamMomentPolynomial, modularThetaEvenSeamHeadPolynomial]
  ring

/-- Exact next determinant of the same symbolic seam moments. -/
theorem modularThetaEvenSeamFourPolynomial_eq {K : Type*} [Field K] [CharZero K] (X : K) :
    hankelFourDet (modularThetaEvenSeamMomentPolynomial 0 X)
      (modularThetaEvenSeamMomentPolynomial 1 X) (modularThetaEvenSeamMomentPolynomial 2 X)
      (modularThetaEvenSeamMomentPolynomial 3 X) (modularThetaEvenSeamMomentPolynomial 4 X)
      (modularThetaEvenSeamMomentPolynomial 5 X) (modularThetaEvenSeamMomentPolynomial 6 X) =
      modularThetaEvenSeamFourPolynomial X := by
  norm_num [modularThetaEvenSeamMomentPolynomial, modularThetaEvenSeamFourPolynomial, hankelFourDet]
  ring

end
end HTGeometry
