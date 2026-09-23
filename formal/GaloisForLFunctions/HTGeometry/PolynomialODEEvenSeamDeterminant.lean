import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-! # Exact modular polynomials for the even rank-four theta seam -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
open GaloisForLFunctions.HTGeometry

/-- The seven normalized signed even reflection moments at the algebraic seam. -/
def modularThetaEvenSeamMomentPolynomial {K : Type*} [Field K] (n : Fin 7) (X : K) : K :=
  match n.val with
  | 0 => (9/64) + (-3/64)*X^(1 : ℕ) + (1/256)*X^(2 : ℕ)
  | 1 => (45/64) + (-165/256)*X^(1 : ℕ) + (21/256)*X^(2 : ℕ) + (1/1024)*X^(3 : ℕ)
  | 2 => (765/64) + (-2505/128)*X^(1 : ℕ) + (4461/1024)*X^(2 : ℕ) + (77/1024)*X^(3 : ℕ) + (27/4096)*X^(4 : ℕ)
  | 3 => (24345/64) + (-243615/256)*X^(1 : ℕ) + (333759/1024)*X^(2 : ℕ) + (31519/4096)*X^(3 : ℕ) + (8199/4096)*X^(4 : ℕ) + (-21/16384)*X^(5 : ℕ)
  | 4 => (1207665/64) + (-2122095/32)*X^(1 : ℕ) + (16407993/512)*X^(2 : ℕ) + (1024127/1024)*X^(3 : ℕ) + (7963857/16384)*X^(4 : ℕ) + (-30027/16384)*X^(5 : ℕ) + (5133/65536)*X^(6 : ℕ)
  | 5 => (85066245/64) + (-1591823865/256)*X^(1 : ℕ) + (2049802467/512)*X^(2 : ℕ) + (327670217/2048)*X^(3 : ℕ) + (1966854177/16384)*X^(4 : ℕ) + (-62366877/65536)*X^(5 : ℕ) + (3218985/65536)*X^(6 : ℕ) + (-725859/262144)*X^(7 : ℕ)
  | _ => (8028542565/64) + (-96262740255/128)*X^(1 : ℕ) + (634560122211/1024)*X^(2 : ℕ) + (1975395347/64)*X^(3 : ℕ) + (529421297031/16384)*X^(4 : ℕ) + (-13501200603/32768)*X^(5 : ℕ) + (6251467509/262144)*X^(6 : ℕ) + (-888527835/262144)*X^(7 : ℕ) + (-10466793/1048576)*X^(8 : ℕ)

/-- Normalized leading even rank-three determinant at the seam. -/
def modularThetaEvenSeamHeadPolynomial {K : Type*} [Field K] (X : K) : K :=
    (3444525/512) +
    (-80754975/2048)*X^(1 : ℕ) +
    (4194195795/65536)*X^(2 : ℕ) +
    (-2646917595/65536)*X^(3 : ℕ) +
    (5201727255/524288)*X^(4 : ℕ) +
    (-1723813569/1048576)*X^(5 : ℕ) +
    (4581650223/16777216)*X^(6 : ℕ) +
    (-612571059/16777216)*X^(7 : ℕ) +
    (35927199/16777216)*X^(8 : ℕ) +
    (1999197/268435456)*X^(9 : ℕ) +
    (-117855/134217728)*X^(10 : ℕ) +
    (-13245/536870912)*X^(11 : ℕ) +
    (14025/8589934592)*X^(12 : ℕ)

/-- Normalized even rank-four determinant at the seam. -/
def modularThetaEvenSeamFourPolynomial {K : Type*} [Field K] (X : K) : K :=
    (6591529153125/64) +
    (-166253013084375/128)*X^(1 : ℕ) +
    (5337820308200625/1024)*X^(2 : ℕ) +
    (-37022043092855625/4096)*X^(3 : ℕ) +
    (7787088853340790375/1048576)*X^(4 : ℕ) +
    (-1646495212914961875/524288)*X^(5 : ℕ) +
    (4126958864384131125/4194304)*X^(6 : ℕ) +
    (-2873522866395593475/8388608)*X^(7 : ℕ) +
    (9674455820287175685/134217728)*X^(8 : ℕ) +
    (-1298405983277063295/134217728)*X^(9 : ℕ) +
    (1072501486261175745/1073741824)*X^(10 : ℕ) +
    (-228446494288779897/2147483648)*X^(11 : ℕ) +
    (639767688325868871/68719476736)*X^(12 : ℕ) +
    (-9963970860000735/17179869184)*X^(13 : ℕ) +
    (3589481195177553/68719476736)*X^(14 : ℕ) +
    (-340179430007961/137438953472)*X^(15 : ℕ) +
    (-21683072191761/274877906944)*X^(16 : ℕ) +
    (2370080393613/549755813888)*X^(17 : ℕ) +
    (-57754209573/8796093022208)*X^(18 : ℕ) +
    (-15503237325/17592186044416)*X^(19 : ℕ) +
    (-14267390625/70368744177664)*X^(20 : ℕ)

/-- Exact leading determinant of the seven symbolic seam moments. -/
theorem modularThetaEvenSeamHeadPolynomial_eq {K : Type*} [Field K] [CharZero K] (X : K) :
    let m := fun n => modularThetaEvenSeamMomentPolynomial n X
    m 0*m 2*m 4-m 0*(m 3)^(2 : ℕ)-(m 1)^(2 : ℕ)*m 4+2*m 1*m 2*m 3-(m 2)^(3 : ℕ) =
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
