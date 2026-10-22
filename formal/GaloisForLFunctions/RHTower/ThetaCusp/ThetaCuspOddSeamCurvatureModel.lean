import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamSixteen
/-! # Exact homogeneous source-cofactor curvature and its positive seam determinant. -/

namespace HTGeometry.ThetaSeamOddCurvature
noncomputable section
private def Ph (n : Fin 7) (a b : ℝ) : ℝ :=
  match n.val with
  | 0 => (-3/8)*b^1 + (1/16)*a^(1 : ℕ)*b^(1-1)
  | 1 => (15/16)*b^2 + (-45/64)*a^(1 : ℕ)*b^(2-1) + (-1/128)*a^(2 : ℕ)*b^(2-2)
  | 2 => (-285/32)*b^3 + (225/16)*a^(1 : ℕ)*b^(3-1) + (191/512)*a^(2 : ℕ)*b^(3-2) + (51/1024)*a^(3 : ℕ)*b^(3-3)
  | 3 => (11085/64)*b^4 + (-118305/256)*a^(1 : ℕ)*b^(4-1) + (-21683/1024)*a^(2 : ℕ)*b^(4-2) + (-25755/4096)*a^(3 : ℕ)*b^(4-3) + (849/8192)*a^(4 : ℕ)*b^(4-4)
  | 4 => (-720915/128)*b^5 + (5801175/256)*a^(1 : ℕ)*b^(5-1) + (1600507/1024)*a^(2 : ℕ)*b^(5-2) + (782901/1024)*a^(3 : ℕ)*b^(5-3) + (-892299/32768)*a^(4 : ℕ)*b^(5-4) + (-26199/65536)*a^(5 : ℕ)*b^(5-5)
  | 5 => (70335015/256)*b^6 + (-1588796145/1024)*a^(1 : ℕ)*b^(6-1) + (-152504033/1024)*a^(2 : ℕ)*b^(6-2) + (-865949145/8192)*a^(3 : ℕ)*b^(6-3) + (397222479/65536)*a^(4 : ℕ)*b^(6-4) + (49594707/262144)*a^(5 : ℕ)*b^(6-5) + (1341999/524288)*a^(6 : ℕ)*b^(6-6)
  | _ => (-9603111885/512)*b^7 + (72410457375/512)*a^(1 : ℕ)*b^(7-1) + (146977580081/8192)*a^(2 : ℕ)*b^(7-2) + (281792785791/16384)*a^(3 : ℕ)*b^(7-3) + (-183992803467/131072)*a^(4 : ℕ)*b^(7-4) + (-2279863179/32768)*a^(5 : ℕ)*b^(7-5) + (-4153486905/2097152)*a^(6 : ℕ)*b^(7-6) + (82018251/4194304)*a^(7 : ℕ)*b^(7-7)
private def q00H {K : Type*} [Field K] (a b : K) : K :=
  (-9603111885 / 512 : K)*a^0*b^(7-0) +
  (72410457375 / 512 : K)*a^1*b^(7-1) +
  (146977580081 / 8192 : K)*a^2*b^(7-2) +
  (281792785791 / 16384 : K)*a^3*b^(7-3) +
  (-183992803467 / 131072 : K)*a^4*b^(7-4) +
  (-2279863179 / 32768 : K)*a^5*b^(7-5) +
  (-4153486905 / 2097152 : K)*a^6*b^(7-6) +
  (82018251 / 4194304 : K)*a^7*b^(7-7)

private def q00AH {K : Type*} [Field K] (a b : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1)*b^(6-(Nat.pred 1)) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2)*b^(6-(Nat.pred 2)) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3)*b^(6-(Nat.pred 3)) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4)*b^(6-(Nat.pred 4)) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5)*b^(6-(Nat.pred 5)) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6)*b^(6-(Nat.pred 6)) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)*b^(6-(Nat.pred 7))

private def q00AAH {K : Type*} [Field K] (a b : K) : K :=
  (146977580081 / 8192 : K)*(2 : K)*(2-1 : K)*a^(2-2)*b^(5-(2-2)) +
  (281792785791 / 16384 : K)*(3 : K)*(3-1 : K)*a^(3-2)*b^(5-(3-2)) +
  (-183992803467 / 131072 : K)*(4 : K)*(4-1 : K)*a^(4-2)*b^(5-(4-2)) +
  (-2279863179 / 32768 : K)*(5 : K)*(5-1 : K)*a^(5-2)*b^(5-(5-2)) +
  (-4153486905 / 2097152 : K)*(6 : K)*(6-1 : K)*a^(6-2)*b^(5-(6-2)) +
  (82018251 / 4194304 : K)*(7 : K)*(7-1 : K)*a^(7-2)*b^(5-(7-2))

private def q20H {K : Type*} [Field K] (a b : K) : K :=
  (24136819125 / 256 : K)*a^0*b^(6-0) +
  (-3674439502025 / 18432 : K)*a^1*b^(6-1) +
  (1331609046581 / 24576 : K)*a^2*b^(6-2) +
  (-1717482882775 / 49152 : K)*a^3*b^(6-3) +
  (18183821139 / 16384 : K)*a^4*b^(6-4) +
  (16860609835 / 524288 : K)*a^5*b^(6-5) +
  (3473399655 / 2097152 : K)*a^6*b^(6-6)

private def q20AH {K : Type*} [Field K] (a b : K) : K :=
  (-3674439502025 / 18432 : K)*(1 : K)*a^(Nat.pred 1)*b^(5-(Nat.pred 1)) +
  (1331609046581 / 24576 : K)*(2 : K)*a^(Nat.pred 2)*b^(5-(Nat.pred 2)) +
  (-1717482882775 / 49152 : K)*(3 : K)*a^(Nat.pred 3)*b^(5-(Nat.pred 3)) +
  (18183821139 / 16384 : K)*(4 : K)*a^(Nat.pred 4)*b^(5-(Nat.pred 4)) +
  (16860609835 / 524288 : K)*(5 : K)*a^(Nat.pred 5)*b^(5-(Nat.pred 5)) +
  (3473399655 / 2097152 : K)*(6 : K)*a^(Nat.pred 6)*b^(5-(Nat.pred 6))

private def q11H {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*a^1*b^(6-1) +
  (-71829533633 / 512 : K)*a^2*b^(6-2) +
  (-157119885175 / 2048 : K)*a^3*b^(6-3) +
  (2760219099 / 512 : K)*a^4*b^(6-4) +
  (14632222215 / 65536 : K)*a^5*b^(6-5) +
  (368880669 / 131072 : K)*a^6*b^(6-6)

private def q11AH {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1)*b^(5-(Nat.pred 1)) +
  (-71829533633 / 512 : K)*(2 : K)*a^(Nat.pred 2)*b^(5-(Nat.pred 2)) +
  (-157119885175 / 2048 : K)*(3 : K)*a^(Nat.pred 3)*b^(5-(Nat.pred 3)) +
  (2760219099 / 512 : K)*(4 : K)*a^(Nat.pred 4)*b^(5-(Nat.pred 4)) +
  (14632222215 / 65536 : K)*(5 : K)*a^(Nat.pred 5)*b^(5-(Nat.pred 5)) +
  (368880669 / 131072 : K)*(6 : K)*a^(Nat.pred 6)*b^(5-(Nat.pred 6))

private def q02H {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*a^1*b^(6-1) +
  (-82880231115 / 512 : K)*a^2*b^(6-2) +
  (-74767393635 / 2048 : K)*a^3*b^(6-3) +
  (2970635877 / 512 : K)*a^4*b^(6-4) +
  (13698002655 / 65536 : K)*a^5*b^(6-5) +
  (246236679 / 131072 : K)*a^6*b^(6-6)

private def q02AH {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1)*b^(5-(Nat.pred 1)) +
  (-82880231115 / 512 : K)*(2 : K)*a^(Nat.pred 2)*b^(5-(Nat.pred 2)) +
  (-74767393635 / 2048 : K)*(3 : K)*a^(Nat.pred 3)*b^(5-(Nat.pred 3)) +
  (2970635877 / 512 : K)*(4 : K)*a^(Nat.pred 4)*b^(5-(Nat.pred 4)) +
  (13698002655 / 65536 : K)*(5 : K)*a^(Nat.pred 5)*b^(5-(Nat.pred 5)) +
  (246236679 / 131072 : K)*(6 : K)*a^(Nat.pred 6)*b^(5-(Nat.pred 6))

private def q40H {K : Type*} [Field K] (a b : K) : K :=
  (-5144215302835 / 55296 : K)*a^0*b^(5-0) +
  (35577720543299 / 331776 : K)*a^1*b^(5-1) +
  (-25601872600205 / 442368 : K)*a^2*b^(5-2) +
  (38885059895 / 4096 : K)*a^3*b^(5-3) +
  (-1917405873275 / 14155776 : K)*a^4*b^(5-4) +
  (13260308795 / 3145728 : K)*a^5*b^(5-5)

private def q31H {K : Type*} [Field K] (a b : K) : K :=
  (1000088122121 / 6912 : K)*a^1*b^(5-1) +
  (-18420952055 / 512 : K)*a^2*b^(5-2) +
  (11621606205 / 256 : K)*a^3*b^(5-3) +
  (-64669006745 / 73728 : K)*a^4*b^(5-4) +
  (-1732754155 / 65536 : K)*a^5*b^(5-5)

private def q22H {K : Type*} [Field K] (a b : K) : K :=
  (524908130395 / 768 : K)*a^1*b^(5-1) +
  (111609297745 / 512 : K)*a^2*b^(5-2) +
  (19309524795 / 256 : K)*a^3*b^(5-3) +
  (-33218570005 / 8192 : K)*a^4*b^(5-4) +
  (-6389085105 / 65536 : K)*a^5*b^(5-5)

private def q13H {K : Type*} [Field K] (a b : K) : K :=
  (93930928597 / 96 : K)*a^1*b^(5-1) +
  (1083585415 / 4 : K)*a^2*b^(5-2) +
  (1456296435 / 32 : K)*a^3*b^(5-3) +
  (-2986894745 / 512 : K)*a^4*b^(5-4) +
  (-940378995 / 8192 : K)*a^5*b^(5-5)

private def q04H {K : Type*} [Field K] (a b : K) : K :=
  (5525348741 / 16 : K)*a^1*b^(5-1) +
  (9752268735 / 128 : K)*a^2*b^(5-2) +
  (275421465 / 32 : K)*a^3*b^(5-3) +
  (-5466943005 / 2048 : K)*a^4*b^(5-4) +
  (-102788325 / 2048 : K)*a^5*b^(5-5)


private def p14H (a b : ℝ) : ℝ :=
  let s := 3*b-3*a/4
  let w := 2*b+a/2
  2*s^2*q20H a b+2*s*w*q11H a b+2*w^2*q02H a b-2*a*w*q00AH a b-s/6*q00H a b
private def p16H (a b : ℝ) : ℝ :=
  let s := 3*b-3*a/4
  let w := 2*b+a/2
  let a2 := -2*a*w
  let s3 := -2*s^2/3+3*a*w/2
  let w3 := -a*w+4*s^2/9-4*s*w/3
  let a4 := 12*a*w^2-2*a*w3
  24*(s^4*q40H a b+s^3*w*q31H a b+s^2*w^2*q22H a b+s*w^3*q13H a b+w^4*q04H a b)+
  6*a2*(2*s^2*q20AH a b+2*s*w*q11AH a b+2*w^2*q02AH a b)+
  3*a2^2*q00AAH a b+4*(s3*(2*s*q20H a b+w*q11H a b)+w3*(s*q11H a b+2*w*q02H a b))+
  a4*q00AH a b-s*(2*s^2*q20H a b+2*s*w*q11H a b+2*w^2*q02H a b+a2*q00AH a b)+
  (-s3/6+s^2/12)*q00H a b


def pH (n : ℕ) (a b : ℝ) : ℝ :=
  if h : n<7 then Ph ⟨n,h⟩ a b else if n=7 then p14H a b else if n=8 then p16H a b else 0
def mH (r : ℕ) (a b : ℝ) : ℝ :=
  (-1:ℝ)^r*∑ j ∈ Finset.range (r+1), ((2*r).choose (2*j):ℝ)*pH j a b*pH (r-j) a b
def vH (r : ℕ) (a b : ℝ) : ℝ :=
  2*(-1:ℝ)^r*∑ j ∈ Finset.range (r+1),
    (((2*r).choose (2*j):ℝ)-((2*r).choose (2*j+1):ℝ))*pH (j+1) a b*pH (r-j) a b
def H (a b : ℝ) : ℝ := mH 1 a b*mH 3 a b-(mH 2 a b)^2
def H2 (a b : ℝ) : ℝ := vH 1 a b*mH 3 a b+mH 1 a b*vH 3 a b-2*mH 2 a b*vH 2 a b
def A (a b : ℝ) : ℝ :=
  mH 1 a b*mH 3 a b*mH 7 a b-mH 1 a b*(mH 5 a b)^2-(mH 2 a b)^2*mH 7 a b+
  2*mH 2 a b*mH 4 a b*mH 5 a b-mH 3 a b*(mH 4 a b)^2
def A2 (a b : ℝ) : ℝ :=
  vH 1 a b*mH 3 a b*mH 7 a b+mH 1 a b*vH 3 a b*mH 7 a b+mH 1 a b*mH 3 a b*vH 7 a b-
  vH 1 a b*(mH 5 a b)^2-2*mH 1 a b*mH 5 a b*vH 5 a b-
  2*mH 2 a b*vH 2 a b*mH 7 a b-(mH 2 a b)^2*vH 7 a b+
  2*(vH 2 a b*mH 4 a b*mH 5 a b+mH 2 a b*vH 4 a b*mH 5 a b+
    mH 2 a b*mH 4 a b*vH 5 a b)-vH 3 a b*(mH 4 a b)^2-2*mH 3 a b*mH 4 a b*vH 4 a b
def B (a b : ℝ) : ℝ :=
  -(mH 1 a b*mH 3 a b*mH 6 a b-mH 1 a b*mH 4 a b*mH 5 a b-(mH 2 a b)^2*mH 6 a b+
  mH 2 a b*mH 3 a b*mH 5 a b+mH 2 a b*(mH 4 a b)^2-(mH 3 a b)^2*mH 4 a b)
def B2 (a b : ℝ) : ℝ :=
  -(vH 1 a b*mH 3 a b*mH 6 a b+mH 1 a b*vH 3 a b*mH 6 a b+mH 1 a b*mH 3 a b*vH 6 a b-
  vH 1 a b*mH 4 a b*mH 5 a b-mH 1 a b*vH 4 a b*mH 5 a b-mH 1 a b*mH 4 a b*vH 5 a b-
  2*mH 2 a b*vH 2 a b*mH 6 a b-(mH 2 a b)^2*vH 6 a b+
  vH 2 a b*mH 3 a b*mH 5 a b+mH 2 a b*vH 3 a b*mH 5 a b+mH 2 a b*mH 3 a b*vH 5 a b+
  vH 2 a b*(mH 4 a b)^2+2*mH 2 a b*mH 4 a b*vH 4 a b-
  2*mH 3 a b*vH 3 a b*mH 4 a b-(mH 3 a b)^2*vH 4 a b)
def D (a b : ℝ) : ℝ :=
  mH 1 a b*mH 3 a b*mH 5 a b-mH 1 a b*(mH 4 a b)^2-(mH 2 a b)^2*mH 5 a b+
  2*mH 2 a b*mH 3 a b*mH 4 a b-(mH 3 a b)^3
def D2 (a b : ℝ) : ℝ :=
  vH 1 a b*(mH 3 a b*mH 5 a b-(mH 4 a b)^2)+
  vH 2 a b*(-2*mH 2 a b*mH 5 a b+2*mH 3 a b*mH 4 a b)+
  vH 3 a b*(mH 1 a b*mH 5 a b+2*mH 2 a b*mH 4 a b-3*(mH 3 a b)^2)+
  vH 4 a b*(-2*mH 1 a b*mH 4 a b+2*mH 2 a b*mH 3 a b)+
  vH 5 a b*(mH 1 a b*mH 3 a b-(mH 2 a b)^2)
def Na (a b : ℝ) : ℝ := pH 0 a b*A2 a b-6*pH 1 a b*A a b+
  10000000000000*b^7*(3*(pH 0 a b)^3*H2 a b-8*(pH 0 a b)^2*pH 1 a b*H a b)
def Nb (a b : ℝ) : ℝ := pH 0 a b*B2 a b-6*pH 1 a b*B a b
def Nd (a b : ℝ) : ℝ := pH 0 a b*D2 a b-6*pH 1 a b*D a b
def quadraticDet (a b : ℝ) : ℝ := Na a b*Nd a b-(Nb a b)^2

def sourceJet (n : ℕ) (a : ℝ) : ℝ :=
  if h : n<7 then modularThetaEvenSeamSourcePolynomial ⟨n,h⟩ a
  else if n=7 then ThetaSeamFourteen.sourceFourteen a
  else if n=8 then ThetaSeamSixteen.sourceSixteen a else 0

private def q00Model {K : Type*} [Field K] (a : K) : K :=
  (-9603111885 / 512 : K)*a^0 +
  (72410457375 / 512 : K)*a^1 +
  (146977580081 / 8192 : K)*a^2 +
  (281792785791 / 16384 : K)*a^3 +
  (-183992803467 / 131072 : K)*a^4 +
  (-2279863179 / 32768 : K)*a^5 +
  (-4153486905 / 2097152 : K)*a^6 +
  (82018251 / 4194304 : K)*a^7

private def q00AModel {K : Type*} [Field K] (a : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)

private def q00AAModel {K : Type*} [Field K] (a : K) : K :=
  (146977580081 / 8192 : K)*(2 : K)*(2-1 : K)*a^(2-2) +
  (281792785791 / 16384 : K)*(3 : K)*(3-1 : K)*a^(3-2) +
  (-183992803467 / 131072 : K)*(4 : K)*(4-1 : K)*a^(4-2) +
  (-2279863179 / 32768 : K)*(5 : K)*(5-1 : K)*a^(5-2) +
  (-4153486905 / 2097152 : K)*(6 : K)*(6-1 : K)*a^(6-2) +
  (82018251 / 4194304 : K)*(7 : K)*(7-1 : K)*a^(7-2)

private def q20Model {K : Type*} [Field K] (a : K) : K :=
  (24136819125 / 256 : K)*a^0 +
  (-3674439502025 / 18432 : K)*a^1 +
  (1331609046581 / 24576 : K)*a^2 +
  (-1717482882775 / 49152 : K)*a^3 +
  (18183821139 / 16384 : K)*a^4 +
  (16860609835 / 524288 : K)*a^5 +
  (3473399655 / 2097152 : K)*a^6

private def q20AModel {K : Type*} [Field K] (a : K) : K :=
  (-3674439502025 / 18432 : K)*(1 : K)*a^(Nat.pred 1) +
  (1331609046581 / 24576 : K)*(2 : K)*a^(Nat.pred 2) +
  (-1717482882775 / 49152 : K)*(3 : K)*a^(Nat.pred 3) +
  (18183821139 / 16384 : K)*(4 : K)*a^(Nat.pred 4) +
  (16860609835 / 524288 : K)*(5 : K)*a^(Nat.pred 5) +
  (3473399655 / 2097152 : K)*(6 : K)*a^(Nat.pred 6)

private def q11Model {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-71829533633 / 512 : K)*a^2 +
  (-157119885175 / 2048 : K)*a^3 +
  (2760219099 / 512 : K)*a^4 +
  (14632222215 / 65536 : K)*a^5 +
  (368880669 / 131072 : K)*a^6

private def q11AModel {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1) +
  (-71829533633 / 512 : K)*(2 : K)*a^(Nat.pred 2) +
  (-157119885175 / 2048 : K)*(3 : K)*a^(Nat.pred 3) +
  (2760219099 / 512 : K)*(4 : K)*a^(Nat.pred 4) +
  (14632222215 / 65536 : K)*(5 : K)*a^(Nat.pred 5) +
  (368880669 / 131072 : K)*(6 : K)*a^(Nat.pred 6)

private def q02Model {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-82880231115 / 512 : K)*a^2 +
  (-74767393635 / 2048 : K)*a^3 +
  (2970635877 / 512 : K)*a^4 +
  (13698002655 / 65536 : K)*a^5 +
  (246236679 / 131072 : K)*a^6

private def q02AModel {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1) +
  (-82880231115 / 512 : K)*(2 : K)*a^(Nat.pred 2) +
  (-74767393635 / 2048 : K)*(3 : K)*a^(Nat.pred 3) +
  (2970635877 / 512 : K)*(4 : K)*a^(Nat.pred 4) +
  (13698002655 / 65536 : K)*(5 : K)*a^(Nat.pred 5) +
  (246236679 / 131072 : K)*(6 : K)*a^(Nat.pred 6)

private def q40Model {K : Type*} [Field K] (a : K) : K :=
  (-5144215302835 / 55296 : K)*a^0 +
  (35577720543299 / 331776 : K)*a^1 +
  (-25601872600205 / 442368 : K)*a^2 +
  (38885059895 / 4096 : K)*a^3 +
  (-1917405873275 / 14155776 : K)*a^4 +
  (13260308795 / 3145728 : K)*a^5

private def q31Model {K : Type*} [Field K] (a : K) : K :=
  (1000088122121 / 6912 : K)*a^1 +
  (-18420952055 / 512 : K)*a^2 +
  (11621606205 / 256 : K)*a^3 +
  (-64669006745 / 73728 : K)*a^4 +
  (-1732754155 / 65536 : K)*a^5

private def q22Model {K : Type*} [Field K] (a : K) : K :=
  (524908130395 / 768 : K)*a^1 +
  (111609297745 / 512 : K)*a^2 +
  (19309524795 / 256 : K)*a^3 +
  (-33218570005 / 8192 : K)*a^4 +
  (-6389085105 / 65536 : K)*a^5

private def q13Model {K : Type*} [Field K] (a : K) : K :=
  (93930928597 / 96 : K)*a^1 +
  (1083585415 / 4 : K)*a^2 +
  (1456296435 / 32 : K)*a^3 +
  (-2986894745 / 512 : K)*a^4 +
  (-940378995 / 8192 : K)*a^5

private def q04Model {K : Type*} [Field K] (a : K) : K :=
  (5525348741 / 16 : K)*a^1 +
  (9752268735 / 128 : K)*a^2 +
  (275421465 / 32 : K)*a^3 +
  (-5466943005 / 2048 : K)*a^4 +
  (-102788325 / 2048 : K)*a^5

private def sourceSixteenModel {K : Type*} [Field K] (a : K) : K :=
  let s := 3-3*a/4
  let w := 2+a/2
  let a2 := -2*a*w
  let s3 := -2*s^2/3+3*a*w/2
  let w3 := -a*w+4*s^2/9-4*s*w/3
  let a4 := 12*a*w^2-2*a*w3
  24*(s^4*q40Model a+s^3*w*q31Model a+s^2*w^2*q22Model a+s*w^3*q13Model a+w^4*q04Model a)+
  6*a2*(2*s^2*q20AModel a+2*s*w*q11AModel a+2*w^2*q02AModel a)+
  3*a2^2*q00AAModel a+4*(s3*(2*s*q20Model a+w*q11Model a)+w3*(s*q11Model a+2*w*q02Model a))+
  a4*q00AModel a-s*(2*s^2*q20Model a+2*s*w*q11Model a+2*w^2*q02Model a+a2*q00AModel a)+
  (-s3/6+s^2/12)*q00Model a

private def sourceFourteenModel (a : ℝ) : ℝ :=
  let s := 3-3*a/4
  let w := 2+a/2
  2*s^2*q20Model a+2*s*w*q11Model a+2*w^2*q02Model a-2*a*w*q00AModel a-s/6*q00Model a

private theorem sourceFourteen_model_eq (a : ℝ) :
    ThetaSeamFourteen.sourceFourteen a=sourceFourteenModel a := rfl

private theorem sourceSixteen_model_eq (a : ℝ) :
    ThetaSeamSixteen.sourceSixteen a=sourceSixteenModel a := rfl

private theorem p14H_one (a : ℝ) : p14H a 1=ThetaSeamFourteen.sourceFourteen a := by
  rw [sourceFourteen_model_eq]
  norm_num [p14H,sourceFourteenModel,q00H,q00AH,q00AAH,q20H,q20AH,q11H,q11AH,q02H,q02AH,q40H,q31H,q22H,q13H,q04H,
    q00Model,q00AModel,q00AAModel,q20Model,q20AModel,q11Model,q11AModel,q02Model,q02AModel,q40Model,q31Model,q22Model,q13Model,q04Model]

private theorem p16H_one (a : ℝ) : p16H a 1=ThetaSeamSixteen.sourceSixteen a := by
  rw [sourceSixteen_model_eq]
  norm_num [p16H,sourceSixteenModel,q00H,q00AH,q00AAH,q20H,q20AH,q11H,q11AH,q02H,q02AH,q40H,q31H,q22H,q13H,q04H,
    q00Model,q00AModel,q00AAModel,q20Model,q20AModel,q11Model,q11AModel,q02Model,q02AModel,q40Model,q31Model,q22Model,q13Model,q04Model]

theorem pH_one (n : ℕ) (a : ℝ) : pH n a 1=sourceJet n a := by
  unfold pH sourceJet
  split_ifs with hn h7 h8
  · generalize hk : (⟨n,hn⟩ : Fin 7)=k
    fin_cases k <;> norm_num [Ph,modularThetaEvenSeamSourcePolynomial]
  · exact p14H_one a
  · exact p16H_one a
  · rfl

def seamMoment (r : ℕ) (a : ℝ) : ℝ :=
  (-1:ℝ)^r*∑ j ∈ Finset.range (r+1), ((2*r).choose (2*j):ℝ)*sourceJet j a*sourceJet (r-j) a

def seamVariation (r : ℕ) (a : ℝ) : ℝ :=
  2*(-1:ℝ)^r*∑ j ∈ Finset.range (r+1),
    (((2*r).choose (2*j):ℝ)-((2*r).choose (2*j+1):ℝ))*sourceJet (j+1) a*sourceJet (r-j) a

theorem mH_one (r : ℕ) (a : ℝ) : mH r a 1=seamMoment r a := by
  unfold mH seamMoment
  simp_rw [pH_one]

theorem vH_one (r : ℕ) (a : ℝ) : vH r a 1=seamVariation r a := by
  unfold vH seamVariation
  simp_rw [pH_one]

private def p14HNorm (a b : ℝ) : {r : ℝ // p14H a b=r} := by
  have h : p14H a b=p14H a b := rfl
  conv at h =>
    rhs
    norm_num [p14H,q00H,q00AH,q00AAH,q20H,q20AH,q11H,q11AH,q02H,q02AH,q40H,q31H,q22H,q13H,q04H]
    ring_nf
  exact ⟨_,h⟩

private def p16HNorm (a b : ℝ) : {r : ℝ // p16H a b=r} := by
  have h : p16H a b=p16H a b := rfl
  conv at h =>
    rhs
    norm_num [p16H,q00H,q00AH,q00AAH,q20H,q20AH,q11H,q11AH,q02H,q02AH,q40H,q31H,q22H,q13H,q04H]
    ring_nf
  exact ⟨_,h⟩

private def mH1Norm (a b : ℝ) : {r' : ℝ // mH 1 a b=r'} := by
  have h : mH 1 a b=mH 1 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH2Norm (a b : ℝ) : {r' : ℝ // mH 2 a b=r'} := by
  have h : mH 2 a b=mH 2 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH3Norm (a b : ℝ) : {r' : ℝ // mH 3 a b=r'} := by
  have h : mH 3 a b=mH 3 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH4Norm (a b : ℝ) : {r' : ℝ // mH 4 a b=r'} := by
  have h : mH 4 a b=mH 4 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH5Norm (a b : ℝ) : {r' : ℝ // mH 5 a b=r'} := by
  have h : mH 5 a b=mH 5 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH6Norm (a b : ℝ) : {r' : ℝ // mH 6 a b=r'} := by
  have h : mH 6 a b=mH 6 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def mH7Norm (a b : ℝ) : {r' : ℝ // mH 7 a b=r'} := by
  have h : mH 7 a b=mH 7 a b := rfl
  conv at h =>
    rhs
    norm_num [mH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH1Norm (a b : ℝ) : {r' : ℝ // vH 1 a b=r'} := by
  have h : vH 1 a b=vH 1 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH2Norm (a b : ℝ) : {r' : ℝ // vH 2 a b=r'} := by
  have h : vH 2 a b=vH 2 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH3Norm (a b : ℝ) : {r' : ℝ // vH 3 a b=r'} := by
  have h : vH 3 a b=vH 3 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH4Norm (a b : ℝ) : {r' : ℝ // vH 4 a b=r'} := by
  have h : vH 4 a b=vH 4 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH5Norm (a b : ℝ) : {r' : ℝ // vH 5 a b=r'} := by
  have h : vH 5 a b=vH 5 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH6Norm (a b : ℝ) : {r' : ℝ // vH 6 a b=r'} := by
  have h : vH 6 a b=vH 6 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def vH7Norm (a b : ℝ) : {r' : ℝ // vH 7 a b=r'} := by
  have h : vH 7 a b=vH 7 a b := rfl
  conv at h =>
    rhs
    norm_num [vH,Finset.sum_range_succ,Nat.choose,pH,Ph]
    simp only [(p14HNorm a b).property,(p16HNorm a b).property]
    dsimp only [p14HNorm,p16HNorm]
    ring_nf
  exact ⟨_,h⟩

private def HNorm (a b : ℝ) : {r : ℝ // H a b=r} := by
  have h : H a b=H a b := rfl
  conv at h =>
    rhs
    unfold H
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def H2Norm (a b : ℝ) : {r : ℝ // H2 a b=r} := by
  have h : H2 a b=H2 a b := rfl
  conv at h =>
    rhs
    unfold H2
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def ANorm (a b : ℝ) : {r : ℝ // A a b=r} := by
  have h : A a b=A a b := rfl
  conv at h =>
    rhs
    unfold A
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def A2Norm (a b : ℝ) : {r : ℝ // A2 a b=r} := by
  have h : A2 a b=A2 a b := rfl
  conv at h =>
    rhs
    unfold A2
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def BNorm (a b : ℝ) : {r : ℝ // B a b=r} := by
  have h : B a b=B a b := rfl
  conv at h =>
    rhs
    unfold B
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def B2Norm (a b : ℝ) : {r : ℝ // B2 a b=r} := by
  have h : B2 a b=B2 a b := rfl
  conv at h =>
    rhs
    unfold B2
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def DNorm (a b : ℝ) : {r : ℝ // D a b=r} := by
  have h : D a b=D a b := rfl
  conv at h =>
    rhs
    unfold D
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def D2Norm (a b : ℝ) : {r : ℝ // D2 a b=r} := by
  have h : D2 a b=D2 a b := rfl
  conv at h =>
    rhs
    unfold D2
    simp only [(mH1Norm a b).property,(mH2Norm a b).property,(mH3Norm a b).property,(mH4Norm a b).property,(mH5Norm a b).property,(mH6Norm a b).property,(mH7Norm a b).property,(vH1Norm a b).property,(vH2Norm a b).property,(vH3Norm a b).property,(vH4Norm a b).property,(vH5Norm a b).property,(vH6Norm a b).property,(vH7Norm a b).property]
    dsimp only [mH1Norm,mH2Norm,mH3Norm,mH4Norm,mH5Norm,mH6Norm,mH7Norm,vH1Norm,vH2Norm,vH3Norm,vH4Norm,vH5Norm,vH6Norm,vH7Norm]
    ring_nf
  exact ⟨_,h⟩

private def NaNorm (a b : ℝ) : {r : ℝ // Na a b=r} := by
  have h : Na a b=Na a b := rfl
  conv at h =>
    rhs
    unfold Na
    simp only [(HNorm a b).property,(H2Norm a b).property,(ANorm a b).property,
      (A2Norm a b).property,(BNorm a b).property,(B2Norm a b).property,
      (DNorm a b).property,(D2Norm a b).property]
    dsimp only [HNorm,H2Norm,ANorm,A2Norm,BNorm,B2Norm,DNorm,D2Norm]
    norm_num [pH,Ph]
    ring_nf
  exact ⟨_,h⟩

private def NbNorm (a b : ℝ) : {r : ℝ // Nb a b=r} := by
  have h : Nb a b=Nb a b := rfl
  conv at h =>
    rhs
    unfold Nb
    simp only [(HNorm a b).property,(H2Norm a b).property,(ANorm a b).property,
      (A2Norm a b).property,(BNorm a b).property,(B2Norm a b).property,
      (DNorm a b).property,(D2Norm a b).property]
    dsimp only [HNorm,H2Norm,ANorm,A2Norm,BNorm,B2Norm,DNorm,D2Norm]
    norm_num [pH,Ph]
    ring_nf
  exact ⟨_,h⟩

private def NdNorm (a b : ℝ) : {r : ℝ // Nd a b=r} := by
  have h : Nd a b=Nd a b := rfl
  conv at h =>
    rhs
    unfold Nd
    simp only [(HNorm a b).property,(H2Norm a b).property,(ANorm a b).property,
      (A2Norm a b).property,(BNorm a b).property,(B2Norm a b).property,
      (DNorm a b).property,(D2Norm a b).property]
    dsimp only [HNorm,H2Norm,ANorm,A2Norm,BNorm,B2Norm,DNorm,D2Norm]
    norm_num [pH,Ph]
    ring_nf
  exact ⟨_,h⟩

private def quadraticDetNorm (a b : ℝ) : {r : ℝ // quadraticDet a b=r} := by
  have h : quadraticDet a b=quadraticDet a b := rfl
  conv at h =>
    rhs
    unfold quadraticDet
    rw [(NaNorm a b).property,(NbNorm a b).property,(NdNorm a b).property]
    dsimp only [NaNorm,NbNorm,NdNorm]
    ring_nf
  exact ⟨_,h⟩

-- Source incidence remains separate from the algebraic sign certificate.
theorem Na_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 < u+v) :
    0 < Na ((191*u+192*v)/10) (u+v) := by
  rw [(NaNorm _ _).property]
  dsimp only [NaNorm]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have hvp : 0 < v := by linarith
    subst u
    ring_nf
    positivity
theorem quadraticDet_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 < u+v) :
    0 < quadraticDet ((191*u+192*v)/10) (u+v) := by
  rw [(quadraticDetNorm _ _).property]
  dsimp only [quadraticDetNorm]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have hvp : 0 < v := by linarith
    subst u
    ring_nf
    positivity
end
end HTGeometry.ThetaSeamOddCurvature
