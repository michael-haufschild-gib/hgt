import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamFourteen
/-!
# Canonical coupled odd-four seam polynomial

Exact homogeneous cofactor model for the source-selected C3 correction and
C4=10^13. The b=1 identity identifies the canonical cleared determinant.
Its quadratic Bernstein controls retain the entire proved pi enclosure.
-/
namespace HTGeometry.ThetaSeamCoupled
noncomputable section
open GaloisForLFunctions.HTGeometry
private def seam12Zero {K : Type*} [Field K] (a : K) : K :=
  (-9603111885 / 512 : K)*a^0 +
  (72410457375 / 512 : K)*a^1 +
  (146977580081 / 8192 : K)*a^2 +
  (281792785791 / 16384 : K)*a^3 +
  (-183992803467 / 131072 : K)*a^4 +
  (-2279863179 / 32768 : K)*a^5 +
  (-4153486905 / 2097152 : K)*a^6 +
  (82018251 / 4194304 : K)*a^7

private def seam12SSHalf {K : Type*} [Field K] (a : K) : K :=
  (24136819125 / 256 : K)*a^0 +
  (-3674439502025 / 18432 : K)*a^1 +
  (1331609046581 / 24576 : K)*a^2 +
  (-1717482882775 / 49152 : K)*a^3 +
  (18183821139 / 16384 : K)*a^4 +
  (16860609835 / 524288 : K)*a^5 +
  (3473399655 / 2097152 : K)*a^6

private def seam12SW {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-71829533633 / 512 : K)*a^2 +
  (-157119885175 / 2048 : K)*a^3 +
  (2760219099 / 512 : K)*a^4 +
  (14632222215 / 65536 : K)*a^5 +
  (368880669 / 131072 : K)*a^6

private def seam12WWHalf {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-82880231115 / 512 : K)*a^2 +
  (-74767393635 / 2048 : K)*a^3 +
  (2970635877 / 512 : K)*a^4 +
  (13698002655 / 65536 : K)*a^5 +
  (246236679 / 131072 : K)*a^6

private def seam12A {K : Type*} [Field K] (a : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)

def sourceFourteen {K : Type*} [Field K] (a : K) : K :=
  let s := 3-3*a/4
  let w := 2+a/2
  2*s^2*seam12SSHalf a+2*s*w*seam12SW a+2*w^2*seam12WWHalf a-
    2*a*w*seam12A a-s/6*seam12Zero a


theorem source_fourteen_model_eq (a : ℝ) :
    HTGeometry.ThetaSeamFourteen.sourceFourteen a = sourceFourteen a := rfl

def momentSeven (a : ℝ) : ℝ :=
  let f := fun k : Fin 7 => modularThetaEvenSeamSourcePolynomial k a;
  -(2*f 0*sourceFourteen a+182*f 1*f 6+2002*f 2*f 5+6006*f 3*f 4)

def sourceSquare (a : ℝ) : ℝ := ((a-6)/16)^2

def moment (k : Fin 7) (a : ℝ) : ℝ :=
  if h : k.val<6 then modularThetaEvenSeamMomentPolynomial ⟨k.val+1,by omega⟩ a
  else momentSeven a

def detThree (a : ℝ) : ℝ :=
  let m := fun k : Fin 7 => moment k a;
  m 0*m 2*m 4-m 0*(m 3)^2-(m 1)^2*m 4+2*m 1*m 2*m 3-(m 2)^3

def headTwo (a : ℝ) : ℝ := moment 0 a*moment 2 a-(moment 1 a)^2

private def seam12ZeroHom {K : Type*} [Field K] (a b : K) : K :=
  (-9603111885 / 512 : K)*a^0*b^(7-0) +
  (72410457375 / 512 : K)*a^1*b^(7-1) +
  (146977580081 / 8192 : K)*a^2*b^(7-2) +
  (281792785791 / 16384 : K)*a^3*b^(7-3) +
  (-183992803467 / 131072 : K)*a^4*b^(7-4) +
  (-2279863179 / 32768 : K)*a^5*b^(7-5) +
  (-4153486905 / 2097152 : K)*a^6*b^(7-6) +
  (82018251 / 4194304 : K)*a^7*b^(7-7)

private def seam12SSHalfHom {K : Type*} [Field K] (a b : K) : K :=
  (24136819125 / 256 : K)*a^0*b^(6-0) +
  (-3674439502025 / 18432 : K)*a^1*b^(6-1) +
  (1331609046581 / 24576 : K)*a^2*b^(6-2) +
  (-1717482882775 / 49152 : K)*a^3*b^(6-3) +
  (18183821139 / 16384 : K)*a^4*b^(6-4) +
  (16860609835 / 524288 : K)*a^5*b^(6-5) +
  (3473399655 / 2097152 : K)*a^6*b^(6-6)

private def seam12SWHom {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*a^1*b^(6-1) +
  (-71829533633 / 512 : K)*a^2*b^(6-2) +
  (-157119885175 / 2048 : K)*a^3*b^(6-3) +
  (2760219099 / 512 : K)*a^4*b^(6-4) +
  (14632222215 / 65536 : K)*a^5*b^(6-5) +
  (368880669 / 131072 : K)*a^6*b^(6-6)

private def seam12WWHalfHom {K : Type*} [Field K] (a b : K) : K :=
  (-146977580081 / 256 : K)*a^1*b^(6-1) +
  (-82880231115 / 512 : K)*a^2*b^(6-2) +
  (-74767393635 / 2048 : K)*a^3*b^(6-3) +
  (2970635877 / 512 : K)*a^4*b^(6-4) +
  (13698002655 / 65536 : K)*a^5*b^(6-5) +
  (246236679 / 131072 : K)*a^6*b^(6-6)

private def seam12AHom {K : Type*} [Field K] (a b : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1)*b^(6-(Nat.pred 1)) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2)*b^(6-(Nat.pred 2)) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3)*b^(6-(Nat.pred 3)) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4)*b^(6-(Nat.pred 4)) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5)*b^(6-(Nat.pred 5)) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6)*b^(6-(Nat.pred 6)) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)*b^(6-(Nat.pred 7))

private def sourceFourteenHom (a b : ℝ) : ℝ :=
  let s := 3*b-3*a/4
  let w := 2*b+a/2
  2*s^2*seam12SSHalfHom a b+2*s*w*seam12SWHom a b+2*w^2*seam12WWHalfHom a b-
    2*a*w*seam12AHom a b-s/6*seam12ZeroHom a b

private def sourceHom (k : Fin 7) (a b : ℝ) : ℝ :=
  match k.val with
  | 0 => (-3/8)*a^0*b^(1-0) + (1/16)*a^1*b^(1-1)
  | 1 => (15/16)*a^0*b^(2-0) + (-45/64)*a^1*b^(2-1) + (-1/128)*a^2*b^(2-2)
  | 2 => (-285/32)*a^0*b^(3-0) + (225/16)*a^1*b^(3-1) + (191/512)*a^2*b^(3-2) + (51/1024)*a^3*b^(3-3)
  | 3 => (11085/64)*a^0*b^(4-0) + (-118305/256)*a^1*b^(4-1) + (-21683/1024)*a^2*b^(4-2) + (-25755/4096)*a^3*b^(4-3) + (849/8192)*a^4*b^(4-4)
  | 4 => (-720915/128)*a^0*b^(5-0) + (5801175/256)*a^1*b^(5-1) + (1600507/1024)*a^2*b^(5-2) + (782901/1024)*a^3*b^(5-3) + (-892299/32768)*a^4*b^(5-4) + (-26199/65536)*a^5*b^(5-5)
  | 5 => (70335015/256)*a^0*b^(6-0) + (-1588796145/1024)*a^1*b^(6-1) + (-152504033/1024)*a^2*b^(6-2) + (-865949145/8192)*a^3*b^(6-3) + (397222479/65536)*a^4*b^(6-4) + (49594707/262144)*a^5*b^(6-5) + (1341999/524288)*a^6*b^(6-6)
  | _ => (-9603111885/512)*a^0*b^(7-0) + (72410457375/512)*a^1*b^(7-1) + (146977580081/8192)*a^2*b^(7-2) + (281792785791/16384)*a^3*b^(7-3) + (-183992803467/131072)*a^4*b^(7-4) + (-2279863179/32768)*a^5*b^(7-5) + (-4153486905/2097152)*a^6*b^(7-6) + (82018251/4194304)*a^7*b^(7-7)

private def momentSevenHom (a b : ℝ) : ℝ :=
  let f := fun k : Fin 7 => sourceHom k a b;
  -(2*f 0*sourceFourteenHom a b+182*f 1*f 6+2002*f 2*f 5+6006*f 3*f 4)

private def momentHom (k : Fin 7) (a b : ℝ) : ℝ :=
  match k.val with
  | 0 => (45/64)*a^0*b^(3-0) + (-165/256)*a^1*b^(3-1) + (21/256)*a^2*b^(3-2) + (1/1024)*a^3*b^(3-3)
  | 1 => (765/64)*a^0*b^(4-0) + (-2505/128)*a^1*b^(4-1) + (4461/1024)*a^2*b^(4-2) + (77/1024)*a^3*b^(4-3) + (27/4096)*a^4*b^(4-4)
  | 2 => (24345/64)*a^0*b^(5-0) + (-243615/256)*a^1*b^(5-1) + (333759/1024)*a^2*b^(5-2) + (31519/4096)*a^3*b^(5-3) + (8199/4096)*a^4*b^(5-4) + (-21/16384)*a^5*b^(5-5)
  | 3 => (1207665/64)*a^0*b^(6-0) + (-2122095/32)*a^1*b^(6-1) + (16407993/512)*a^2*b^(6-2) + (1024127/1024)*a^3*b^(6-3) + (7963857/16384)*a^4*b^(6-4) + (-30027/16384)*a^5*b^(6-5) + (5133/65536)*a^6*b^(6-6)
  | 4 => (85066245/64)*a^0*b^(7-0) + (-1591823865/256)*a^1*b^(7-1) + (2049802467/512)*a^2*b^(7-2) + (327670217/2048)*a^3*b^(7-3) + (1966854177/16384)*a^4*b^(7-4) + (-62366877/65536)*a^5*b^(7-5) + (3218985/65536)*a^6*b^(7-6) + (-725859/262144)*a^7*b^(7-7)
  | 5 => (8028542565/64)*a^0*b^(8-0) + (-96262740255/128)*a^1*b^(8-1) + (634560122211/1024)*a^2*b^(8-2) + (1975395347/64)*a^3*b^(8-3) + (529421297031/16384)*a^4*b^(8-4) + (-13501200603/32768)*a^5*b^(8-5) + (6251467509/262144)*a^6*b^(8-6) + (-888527835/262144)*a^7*b^(8-7) + (-10466793/1048576)*a^8*b^(8-8)
  | _ => momentSevenHom a b

private def momentSevenHomNorm (a b : ℝ) : {r : ℝ // momentSevenHom a b=r} := by
  have h : momentSevenHom a b=momentSevenHom a b := rfl
  conv at h =>
    rhs
    norm_num [momentSevenHom,sourceHom,sourceFourteenHom,seam12SSHalfHom,
      seam12SWHom,seam12WWHalfHom,seam12AHom,seam12ZeroHom]
    ring_nf
  exact ⟨_,h⟩


private def c5 (a b : ℝ) : ℝ :=
  let m := fun k : Fin 7 => momentHom k a b;
  m 0*m 2-(m 1)^2

private def c5Norm (a b : ℝ) : {r : ℝ // c5 a b=r} := by
  have h : c5 a b=c5 a b := rfl
  conv at h =>
    rhs
    unfold c5
    norm_num [momentHom]
    ring_nf
  exact ⟨_,h⟩

private def h3 (a b : ℝ) : ℝ :=
  let m := fun k : Fin 7 => momentHom k a b;
  c5 a b*m 4-m 0*(m 3)^2+2*m 1*m 2*m 3-(m 2)^3

private def h3Norm (a b : ℝ) : {r : ℝ // h3 a b=r} := by
  have h : h3 a b=h3 a b := rfl
  conv at h =>
    rhs
    unfold h3
    rw [(c5Norm a b).property]
    dsimp only [c5Norm]
    norm_num [momentHom]
    ring_nf
  exact ⟨_,h⟩

private def cof22 (a b : ℝ) : ℝ :=
  let m := fun k : Fin 7 => momentHom k a b;
  c5 a b*m 6-m 0*(m 4)^2+2*m 1*m 3*m 4-m 2*(m 3)^2

private def cof22Norm (a b : ℝ) : {r : ℝ // cof22 a b=r} := by
  have h : cof22 a b=cof22 a b := rfl
  conv at h =>
    rhs
    unfold cof22
    rw [(c5Norm a b).property]
    dsimp only [c5Norm]
    norm_num [momentHom]
    rw [(momentSevenHomNorm a b).property]
    dsimp only [momentSevenHomNorm]
    ring_nf
  exact ⟨_,h⟩

private def cof23 (a b : ℝ) : ℝ :=
  let m := fun k : Fin 7 => momentHom k a b;
  -(c5 a b*m 5-m 0*m 3*m 4+m 1*m 2*m 4+m 1*(m 3)^2-(m 2)^2*m 3)

private def cof23Norm (a b : ℝ) : {r : ℝ // cof23 a b=r} := by
  have h : cof23 a b=cof23 a b := rfl
  conv at h =>
    rhs
    unfold cof23
    rw [(c5Norm a b).property]
    dsimp only [c5Norm]
    norm_num [momentHom]
    ring_nf
  exact ⟨_,h⟩

private theorem momentHom_one (k : Fin 7) (a : ℝ) : momentHom k a 1=moment k a := by
  fin_cases k
  all_goals norm_num [momentHom,moment,momentSevenHom,momentSeven,sourceHom,
    modularThetaEvenSeamSourcePolynomial,modularThetaEvenSeamMomentPolynomial,
    sourceFourteenHom,sourceFourteen,seam12SSHalfHom,seam12SWHom,seam12WWHalfHom,
    seam12AHom,seam12ZeroHom,seam12SSHalf,seam12SW,seam12WWHalf,seam12A,seam12Zero]

def canonicalCleared (a q : ℝ) : ℝ :=
  let m := fun k : Fin 7 => moment k a;
  let t := 168*q-56
  let A := m 0*m 2*m 6-m 0*(m 4)^2-(m 1)^2*m 6+2*m 1*m 3*m 4-m 2*(m 3)^2
  let B := -(m 0*m 2*m 5-m 0*m 3*m 4-(m 1)^2*m 5+
    m 1*m 2*m 4+m 1*(m 3)^2-(m 2)^2*m 3);
  -2*detThree a*A-B^2-6*t*detThree a*B-3*t^2*(detThree a)^2-
    2*10000000000000*(3*sourceSquare a)*detThree a*headTwo a

private def kc0 (a b : ℝ) : ℝ := -2*h3 a b*cof22 a b

private def kc0Norm (a b : ℝ) : {r : ℝ // kc0 a b=r} := by
  have h : kc0 a b=kc0 a b := rfl
  conv at h =>
    rhs
    unfold kc0
    rw [(h3Norm a b).property,(cof22Norm a b).property]
    dsimp only [h3Norm,cof22Norm]
    ring_nf
  exact ⟨_,h⟩

private def kc1 (a b : ℝ) : ℝ := -(cof23 a b)^2

private def kc1Norm (a b : ℝ) : {r : ℝ // kc1 a b=r} := by
  have h : kc1 a b=kc1 a b := rfl
  conv at h =>
    rhs
    unfold kc1
    rw [(cof23Norm a b).property]
    dsimp only [cof23Norm]
    ring_nf
  exact ⟨_,h⟩

private def kc2 (a b : ℝ) : ℝ := -6*b*h3 a b*cof23 a b

private def kc2Norm (a b : ℝ) : {r : ℝ // kc2 a b=r} := by
  have h : kc2 a b=kc2 a b := rfl
  conv at h =>
    rhs
    unfold kc2
    rw [(h3Norm a b).property,(cof23Norm a b).property]
    dsimp only [h3Norm,cof23Norm]
    ring_nf
  exact ⟨_,h⟩

private def kc3 (a b : ℝ) : ℝ := -3*b^2*(h3 a b)^2

private def kc3Norm (a b : ℝ) : {r : ℝ // kc3 a b=r} := by
  have h : kc3 a b=kc3 a b := rfl
  conv at h =>
    rhs
    unfold kc3
    rw [(h3Norm a b).property]
    dsimp only [h3Norm]
    ring_nf
  exact ⟨_,h⟩

private def kc4 (a b : ℝ) : ℝ := -2*10000000000000*(3*((a-6*b)/16)^2)*b^7*h3 a b*c5 a b

private def kc4Norm (a b : ℝ) : {r : ℝ // kc4 a b=r} := by
  have h : kc4 a b=kc4 a b := rfl
  conv at h =>
    rhs
    unfold kc4
    rw [(h3Norm a b).property,(c5Norm a b).property]
    dsimp only [h3Norm,c5Norm]
    ring_nf
  exact ⟨_,h⟩

def canonicalHom (a b q : ℝ) : ℝ :=
  kc0 a b+kc1 a b+(168*q-56)*kc2 a b+(168*q-56)^2*kc3 a b+kc4 a b

def canonicalLoNorm (a b : ℝ) : {r : ℝ // canonicalHom a b (157/50)=r} := by
  have h : canonicalHom a b (157/50)=canonicalHom a b (157/50) := rfl
  conv at h =>
    rhs
    unfold canonicalHom
    rw [(kc0Norm a b).property,(kc1Norm a b).property,(kc2Norm a b).property,(kc3Norm a b).property,(kc4Norm a b).property]
    dsimp only [kc0Norm,kc1Norm,kc2Norm,kc3Norm,kc4Norm]
    ring_nf
  exact ⟨_,h⟩

def canonicalHiNorm (a b : ℝ) : {r : ℝ // canonicalHom a b (63/20)=r} := by
  have h : canonicalHom a b (63/20)=canonicalHom a b (63/20) := rfl
  conv at h =>
    rhs
    unfold canonicalHom
    rw [(kc0Norm a b).property,(kc1Norm a b).property,(kc2Norm a b).property,(kc3Norm a b).property,(kc4Norm a b).property]
    dsimp only [kc0Norm,kc1Norm,kc2Norm,kc3Norm,kc4Norm]
    ring_nf
  exact ⟨_,h⟩

theorem canonicalHom_one (a q : ℝ) : canonicalHom a 1 q=canonicalCleared a q := by
  dsimp only [canonicalHom,kc0,kc1,kc2,kc3,kc4,h3,cof22,cof23,c5]
  simp only [momentHom_one,one_pow,mul_one]
  unfold canonicalCleared detThree headTwo sourceSquare
  ring

def canonicalMidControlHom (a b : ℝ) : ℝ := kc0 a b+kc1 a b+((168*(157/50)-56)+(168*(63/20)-56))/2*kc2 a b+(168*(157/50)-56)*(168*(63/20)-56)*kc3 a b+kc4 a b

def canonicalMidControlHomNorm (a b : ℝ) : {r : ℝ // canonicalMidControlHom a b=r} := by
  have h : canonicalMidControlHom a b=canonicalMidControlHom a b := rfl
  conv at h =>
    rhs
    unfold canonicalMidControlHom
    rw [(kc0Norm a b).property,(kc1Norm a b).property,(kc2Norm a b).property,(kc3Norm a b).property,(kc4Norm a b).property]
    dsimp only [kc0Norm,kc1Norm,kc2Norm,kc3Norm,kc4Norm]
    ring_nf
  exact ⟨_,h⟩

def optimalHom (a b : ℝ) : ℝ := kc0 a b-2*kc1 a b+kc4 a b

def optimalHomNorm (a b : ℝ) : {r : ℝ // optimalHom a b=r} := by
  have h : optimalHom a b=optimalHom a b := rfl
  conv at h =>
    rhs
    unfold optimalHom
    rw [(kc0Norm a b).property,(kc1Norm a b).property,(kc4Norm a b).property]
    dsimp only [kc0Norm,kc1Norm,kc4Norm]
    ring_nf
  exact ⟨_,h⟩

theorem canonicalHom_bernstein (a b q : ℝ) :
    canonicalHom a b q =
      (1-(100*q-314))^2*canonicalHom a b (157/50)+
      2*(100*q-314)*(1-(100*q-314))*canonicalMidControlHom a b+
      (100*q-314)^2*canonicalHom a b (63/20) := by
  unfold canonicalHom canonicalMidControlHom
  ring

/-- At the optimal direction only the native diagonal-load threshold remains. -/
theorem optimalHom_one (a : ℝ) : optimalHom a 1 =
    -2*headTwo a*(hankelFourDet (moment 0 a) (moment 1 a) (moment 2 a) (moment 3 a)
      (moment 4 a) (moment 5 a) (moment 6 a)+
      10000000000000*(3*sourceSquare a)*detThree a) := by
  dsimp only [optimalHom,kc0,kc1,kc4,h3,cof22,cof23,c5]
  simp only [momentHom_one,one_pow,mul_one]
  unfold headTwo detThree sourceSquare hankelFourDet
  ring

end
end HTGeometry.ThetaSeamCoupled
