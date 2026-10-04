import GaloisForLFunctions.RHTower.ThetaCuspOddSeamFourteen
/-!
# Literal complete theta-source derivative sixteen at the seam

The fourth covariant variation of the existing order-twelve source
polynomial retains the transverse fourth jet. Its specialization gives
an unconditional identity for the complete source derivative sixteen,
needed for the fourth Schur-gap cofactor curvature.
-/

namespace HTGeometry.ThetaSeamSixteen
noncomputable section
open MvPolynomial ModularThetaLyapunovState
open ThetaSeamFourteen

private theorem states_univ : (Finset.univ : Finset ModularThetaLyapunovState) = {.S,.A,.W} := by
  ext i
  cases i <;> simp

private theorem pd_comm {R σ : Type*} [CommSemiring R] (i j : σ) (Q : MvPolynomial σ R) :
    pderiv i (pderiv j Q)=pderiv j (pderiv i Q) := by
  classical
  ext d
  by_cases h : i=j
  · subst j
    rfl
  · simp [coeff_pderiv,Finsupp.add_apply,h,Ne.symm h,
      add_comm,add_left_comm,mul_comm,mul_left_comm,mul_assoc]

/-- Exact fourth covariant seam variation, retaining the fourth transverse source jet. -/
theorem seam_fourth_lie (Q : ModularThetaLyapunovPolynomial) (a : ℂ) :
    let e := eval (seamState a)
    let s := 3-3*a/4
    let w := 2+a/2
    let a2 := -2*a*w
    let s3 := -2*s^2/3+3*a*w/2
    let w3 := -a*w+4*s^2/9-4*s*w/3
    let a4 := 12*a*w^2-2*a*w3
    e (modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedLie
      (modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedLie Q)))) =
    s^4*e (pderiv .S (pderiv .S (pderiv .S (pderiv .S Q))))+
    4*s^3*w*e (pderiv .S (pderiv .S (pderiv .S (pderiv .W Q))))+
    6*s^2*w^2*e (pderiv .S (pderiv .S (pderiv .W (pderiv .W Q))))+
    4*s*w^3*e (pderiv .S (pderiv .W (pderiv .W (pderiv .W Q))))+
    w^4*e (pderiv .W (pderiv .W (pderiv .W (pderiv .W Q))))+
    6*a2*(s^2*e (pderiv .S (pderiv .S (pderiv .A Q)))+
      2*s*w*e (pderiv .S (pderiv .W (pderiv .A Q)))+
      w^2*e (pderiv .W (pderiv .W (pderiv .A Q))))+
    3*a2^2*e (pderiv .A (pderiv .A Q))+
    4*(s3*(s*e (pderiv .S (pderiv .S Q))+w*e (pderiv .S (pderiv .W Q)))+
      w3*(s*e (pderiv .S (pderiv .W Q))+w*e (pderiv .W (pderiv .W Q))))+
    a4*e (pderiv .A Q)-
    s*(s^2*e (pderiv .S (pderiv .S Q))+2*s*w*e (pderiv .S (pderiv .W Q))+
      w^2*e (pderiv .W (pderiv .W Q))+a2*e (pderiv .A Q))+
    (-s3/6+s^2/12)*e Q := by
  have htwo (i : ModularThetaLyapunovState) :
      pderiv i (2 : ModularThetaLyapunovPolynomial)=0 := by
    rw [show (2 : ModularThetaLyapunovPolynomial)=1+1 by ring,map_add]
    simp only [pderiv_one,add_zero]
  dsimp only
  rw [seam_double_lie]
  simp [modularThetaLyapunovNormalizedLie,modularThetaLyapunovLie,
    modularThetaLyapunovVectorField,states_univ,pderiv_X,Pi.single_apply,seamState,pd_comm,htwo]
  ring


private def q00 {K : Type*} [Field K] (a : K) : K :=
  (-9603111885 / 512 : K)*a^0 +
  (72410457375 / 512 : K)*a^1 +
  (146977580081 / 8192 : K)*a^2 +
  (281792785791 / 16384 : K)*a^3 +
  (-183992803467 / 131072 : K)*a^4 +
  (-2279863179 / 32768 : K)*a^5 +
  (-4153486905 / 2097152 : K)*a^6 +
  (82018251 / 4194304 : K)*a^7

private def q00A {K : Type*} [Field K] (a : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)

private def q00AA {K : Type*} [Field K] (a : K) : K :=
  (146977580081 / 8192 : K)*(2 : K)*(2-1 : K)*a^(2-2) +
  (281792785791 / 16384 : K)*(3 : K)*(3-1 : K)*a^(3-2) +
  (-183992803467 / 131072 : K)*(4 : K)*(4-1 : K)*a^(4-2) +
  (-2279863179 / 32768 : K)*(5 : K)*(5-1 : K)*a^(5-2) +
  (-4153486905 / 2097152 : K)*(6 : K)*(6-1 : K)*a^(6-2) +
  (82018251 / 4194304 : K)*(7 : K)*(7-1 : K)*a^(7-2)

private def q20 {K : Type*} [Field K] (a : K) : K :=
  (24136819125 / 256 : K)*a^0 +
  (-3674439502025 / 18432 : K)*a^1 +
  (1331609046581 / 24576 : K)*a^2 +
  (-1717482882775 / 49152 : K)*a^3 +
  (18183821139 / 16384 : K)*a^4 +
  (16860609835 / 524288 : K)*a^5 +
  (3473399655 / 2097152 : K)*a^6

private def q20A {K : Type*} [Field K] (a : K) : K :=
  (-3674439502025 / 18432 : K)*(1 : K)*a^(Nat.pred 1) +
  (1331609046581 / 24576 : K)*(2 : K)*a^(Nat.pred 2) +
  (-1717482882775 / 49152 : K)*(3 : K)*a^(Nat.pred 3) +
  (18183821139 / 16384 : K)*(4 : K)*a^(Nat.pred 4) +
  (16860609835 / 524288 : K)*(5 : K)*a^(Nat.pred 5) +
  (3473399655 / 2097152 : K)*(6 : K)*a^(Nat.pred 6)

private def q11 {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-71829533633 / 512 : K)*a^2 +
  (-157119885175 / 2048 : K)*a^3 +
  (2760219099 / 512 : K)*a^4 +
  (14632222215 / 65536 : K)*a^5 +
  (368880669 / 131072 : K)*a^6

private def q11A {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1) +
  (-71829533633 / 512 : K)*(2 : K)*a^(Nat.pred 2) +
  (-157119885175 / 2048 : K)*(3 : K)*a^(Nat.pred 3) +
  (2760219099 / 512 : K)*(4 : K)*a^(Nat.pred 4) +
  (14632222215 / 65536 : K)*(5 : K)*a^(Nat.pred 5) +
  (368880669 / 131072 : K)*(6 : K)*a^(Nat.pred 6)

private def q02 {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-82880231115 / 512 : K)*a^2 +
  (-74767393635 / 2048 : K)*a^3 +
  (2970635877 / 512 : K)*a^4 +
  (13698002655 / 65536 : K)*a^5 +
  (246236679 / 131072 : K)*a^6

private def q02A {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*(1 : K)*a^(Nat.pred 1) +
  (-82880231115 / 512 : K)*(2 : K)*a^(Nat.pred 2) +
  (-74767393635 / 2048 : K)*(3 : K)*a^(Nat.pred 3) +
  (2970635877 / 512 : K)*(4 : K)*a^(Nat.pred 4) +
  (13698002655 / 65536 : K)*(5 : K)*a^(Nat.pred 5) +
  (246236679 / 131072 : K)*(6 : K)*a^(Nat.pred 6)

private def q40 {K : Type*} [Field K] (a : K) : K :=
  (-5144215302835 / 55296 : K)*a^0 +
  (35577720543299 / 331776 : K)*a^1 +
  (-25601872600205 / 442368 : K)*a^2 +
  (38885059895 / 4096 : K)*a^3 +
  (-1917405873275 / 14155776 : K)*a^4 +
  (13260308795 / 3145728 : K)*a^5

private def q31 {K : Type*} [Field K] (a : K) : K :=
  (1000088122121 / 6912 : K)*a^1 +
  (-18420952055 / 512 : K)*a^2 +
  (11621606205 / 256 : K)*a^3 +
  (-64669006745 / 73728 : K)*a^4 +
  (-1732754155 / 65536 : K)*a^5

private def q22 {K : Type*} [Field K] (a : K) : K :=
  (524908130395 / 768 : K)*a^1 +
  (111609297745 / 512 : K)*a^2 +
  (19309524795 / 256 : K)*a^3 +
  (-33218570005 / 8192 : K)*a^4 +
  (-6389085105 / 65536 : K)*a^5

private def q13 {K : Type*} [Field K] (a : K) : K :=
  (93930928597 / 96 : K)*a^1 +
  (1083585415 / 4 : K)*a^2 +
  (1456296435 / 32 : K)*a^3 +
  (-2986894745 / 512 : K)*a^4 +
  (-940378995 / 8192 : K)*a^5

private def q04 {K : Type*} [Field K] (a : K) : K :=
  (5525348741 / 16 : K)*a^1 +
  (9752268735 / 128 : K)*a^2 +
  (275421465 / 32 : K)*a^3 +
  (-5466943005 / 2048 : K)*a^4 +
  (-102788325 / 2048 : K)*a^5

private theorem pd_num2 (i : ModularThetaLyapunovState) :
    pderiv i (2 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 2

private theorem pd_num3 (i : ModularThetaLyapunovState) :
    pderiv i (3 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 3

private theorem pd_num4 (i : ModularThetaLyapunovState) :
    pderiv i (4 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 4

private theorem pd_num5 (i : ModularThetaLyapunovState) :
    pderiv i (5 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 5

private theorem pd_num6 (i : ModularThetaLyapunovState) :
    pderiv i (6 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 6

private theorem pd_num7 (i : ModularThetaLyapunovState) :
    pderiv i (7 : ModularThetaLyapunovPolynomial)=0 := (pderiv i).map_natCast 7

attribute [local simp] pd_num2 pd_num3 pd_num4 pd_num5 pd_num6 pd_num7

private theorem eval_q00 (a : ℂ) : eval (seamState a) evenCompactSourceJet12 = 1*q00 a := by
  simp [evenCompactSourceJet12,seamState,q00]
  ring

private theorem eval_q20 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S evenCompactSourceJet12)) = 2*q20 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q20]
  ring

private theorem eval_q11 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .W evenCompactSourceJet12)) = 1*q11 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q11]
  ring

private theorem eval_q02 (a : ℂ) : eval (seamState a) (pderiv .W (pderiv .W evenCompactSourceJet12)) = 2*q02 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q02]
  ring

private theorem eval_q40 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S (pderiv .S (pderiv .S evenCompactSourceJet12)))) = 24*q40 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q40]
  ring

private theorem eval_q31 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S (pderiv .S (pderiv .W evenCompactSourceJet12)))) = 6*q31 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q31]
  ring

private theorem eval_q22 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S (pderiv .W (pderiv .W evenCompactSourceJet12)))) = 4*q22 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q22]
  ring

private theorem eval_q13 (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .W (pderiv .W (pderiv .W evenCompactSourceJet12)))) = 6*q13 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q13]
  ring

private theorem eval_q04 (a : ℂ) : eval (seamState a) (pderiv .W (pderiv .W (pderiv .W (pderiv .W evenCompactSourceJet12)))) = 24*q04 a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q04]
  ring

private theorem eval_q20A (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S (pderiv .A evenCompactSourceJet12))) = 2*q20A a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q20A]
  ring

private theorem eval_q11A (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .W (pderiv .A evenCompactSourceJet12))) = 1*q11A a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q11A]
  ring

private theorem eval_q02A (a : ℂ) : eval (seamState a) (pderiv .W (pderiv .W (pderiv .A evenCompactSourceJet12))) = 2*q02A a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q02A]
  ring

private theorem eval_q00A (a : ℂ) : eval (seamState a) (pderiv .A evenCompactSourceJet12) = 1*q00A a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q00A]
  ring

private theorem eval_q00AA (a : ℂ) : eval (seamState a) (pderiv .A (pderiv .A evenCompactSourceJet12)) = 1*q00AA a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,q00AA]
  ring

def sourceSixteen {K : Type*} [Field K] (a : K) : K :=
  let s := 3-3*a/4
  let w := 2+a/2
  let a2 := -2*a*w
  let s3 := -2*s^2/3+3*a*w/2
  let w3 := -a*w+4*s^2/9-4*s*w/3
  let a4 := 12*a*w^2-2*a*w3
  24*(s^4*q40 a+s^3*w*q31 a+s^2*w^2*q22 a+s*w^3*q13 a+w^4*q04 a)+
  6*a2*(2*s^2*q20A a+2*s*w*q11A a+2*w^2*q02A a)+
  3*a2^2*q00AA a+4*(s3*(2*s*q20 a+w*q11 a)+w3*(s*q11 a+2*w*q02 a))+
  a4*q00A a-s*(2*s^2*q20 a+2*s*w*q11 a+2*w^2*q02 a+a2*q00A a)+
  (-s3/6+s^2/12)*q00 a

theorem eval_source_sixteen (a : ℂ) :
    eval (seamState a) (modularThetaLyapunovNormalizedSourceJet 16)=sourceSixteen a := by
  rw [show 16=15+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    show 15=14+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    show 14=13+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    show 13=12+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    evenCompactSourceJet12_eq,seam_fourth_lie]
  rw [eval_q00,eval_q20,eval_q11,eval_q02,eval_q40,eval_q31,eval_q22,eval_q13,eval_q04,eval_q20A,eval_q11A,eval_q02A,eval_q00A,eval_q00AA]
  unfold sourceSixteen
  ring

open RHTower
/-- Literal complete-source derivative sixteen, with no source hypothesis. -/
theorem source_sixteen : iteratedDeriv 16 thetaCuspFullSource 0 =
    thetaCuspSelfDualThetaMass*sourceSixteen (thetaCuspSelfDualModularScale^2) := by
  have h := thetaCuspFullSource_seamJet_eq_formalJet 16
  rw [modularThetaODESourceJet_eq_X_H_mul_normalized,map_mul,MvPolynomial.eval_X] at h
  simp only [modularThetaODESeamState,one_mul] at h
  rw [← modularThetaGeneralLyapunov_normalizedSourceJet,
    eval_modularThetaGeneralLyapunovPullback_seam] at h
  change ((iteratedDeriv 16 thetaCuspFullSource 0 : ℝ) : ℂ) =
    (thetaCuspSelfDualThetaMass : ℂ)*eval (seamState ((thetaCuspSelfDualModularScale:ℂ)^2))
      (modularThetaLyapunovNormalizedSourceJet 16) at h
  rw [eval_source_sixteen] at h
  apply Complex.ofReal_injective
  rw [h]
  norm_num [sourceSixteen,q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]

end
end HTGeometry.ThetaSeamSixteen
