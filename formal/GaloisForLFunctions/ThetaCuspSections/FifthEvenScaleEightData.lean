import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadContinuation

/-!
# Exact comparison matrices at theta scale eight

Rational bounds enclose the leading unequal-pair weight. A half-sized cross
load has a positive lower comparison matrix; the full cross load has an upper
comparison matrix with a negative direction. The displayed moments and load
rows are identified with the radial source and its Gaussian congruence.
-/
open Matrix
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.EightCrossData
open FifthLeadingPair FifthNativeRay FifthRemainder EvenFiveEndpoint
open _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit
private def r0 (q : ℝ) : ℝ := 9 - q * 12 + q ^ 2 * 4
private def r1 (q : ℝ) : ℝ := q * 120 - q ^ 2 * 96 + q ^ 3 * 32
private def r2 (q : ℝ) : ℝ := -(q * 480) + q ^ 2 * 4416 - q ^ 3 * 2432 + q ^ 4 * 768
private def r3 (q : ℝ) : ℝ := q * 1920 - q ^ 2 * 82176 + q ^ 3 * 253952 - q ^ 4 * 107520 + q ^ 5 * 30720
private def r4 (q : ℝ) : ℝ := -(q * 7680) + q ^ 2 * 1360896 - q ^ 3 * 12388352 + q ^ 4 * 19611648 - q ^ 5 * 6881280 + q ^ 6 * 1720320
private def r5 (q : ℝ) : ℝ := q * 30720 - q ^ 2 * 21958656 + q ^ 3 * 500252672 - q ^ 4 * 1924055040 + q ^ 5 * 1899233280 - q ^ 6 * 578027520 +
      q ^ 7 * 123863040
private def r6 (q : ℝ) : ℝ := -(q * 122880) + q ^ 2 * 352075776 - q ^ 3 * 18886787072 + q ^ 4 * 150752329728 - q ^ 5 * 320229212160 +
          q ^ 6 * 221632266240 -
        q ^ 7 * 59949711360 +
      q ^ 8 * 10899947520
private def r7 (q : ℝ) : ℝ := q * 491520 - q ^ 2 * 5636161536 + q ^ 3 * 694004744192 - q ^ 4 * 10699371970560 + q ^ 5 * 42564900618240 -
            q ^ 6 * 57797577277440 +
          q ^ 7 * 30323654000640 -
        q ^ 8 * 7368364523520 +
      q ^ 9 * 1133594542080
private def r8 (q : ℝ) : ℝ := -(q * 1966080) + q ^ 2 * 90190381056 - q ^ 3 * 25209606766592 + q ^ 4 * 723521013547008 - q ^ 5 * 5015348591984640 +
              q ^ 6 * 11904065218805760 -
            q ^ 7 * 11342746988052480 +
          q ^ 8 * 4763364265820160 -
        q ^ 9 * 1042906978713600 +
      q ^ 10 * 136031345049600
private def b0 (q : ℝ) : ℝ := 9 - q * 30 + q ^ 2 * 16
private def b1 (q : ℝ) : ℝ := q * 300 - q ^ 2 * 1356 + q ^ 3 * 1400 - q ^ 4 * 576
private def b2 (q : ℝ) : ℝ := -(q * 1200) + q ^ 2 * 39696 - q ^ 3 * 171200 + q ^ 4 * 200784 - q ^ 5 * 108000 + q ^ 6 * 20736
private def b3 (q : ℝ) : ℝ := q * 4800 - q ^ 2 * 707136 + q ^ 3 * 10073600 - q ^ 4 * 35416896 + q ^ 5 * 43089600 - q ^ 6 * 25790400 +
        q ^ 7 * 7620480 -
      q ^ 8 * 746496
private def b4 (q : ℝ) : ℝ := -(q * 19200) + q ^ 2 * 11602176 - q ^ 3 * 433126400 + q ^ 4 * 3651012864 - q ^ 5 * 10402022400 + q ^ 6 * 12499017216 -
            q ^ 7 * 7892398080 +
          q ^ 8 * 2788598016 -
        q ^ 9 * 468426240 +
      q ^ 10 * 26873856
private def b5 (q : ℝ) : ℝ := q * 76800 - q ^ 2 * 186786816 + q ^ 3 * 16751820800 - q ^ 4 * 293872751616 + q ^ 5 * 1684623283200 -
                  q ^ 6 * 4002679526400 +
                q ^ 7 * 4618622453760 -
              q ^ 8 * 2987682527232 +
            q ^ 9 * 1157721984000 -
          q ^ 10 * 250538241024 +
        q ^ 11 * 26000455680 -
      q ^ 12 * 967458816
private def b6 (q : ℝ) : ℝ := -(q * 307200) + q ^ 2 * 2993197056 - q ^ 3 * 621740441600 + q ^ 4 * 21146177900544 - q ^ 5 * 220856989900800 +
                      q ^ 6 * 939708531818496 -
                    q ^ 7 * 1911756612648960 +
                  q ^ 8 * 2090002567606272 -
                q ^ 9 * 1357634344366080 +
              q ^ 10 * 554264510164992 -
            q ^ 11 * 138376171929600 +
          q ^ 12 * 19385214160896 -
        q ^ 13 * 1342349107200 +
      q ^ 14 * 34828517376
private def b7 (q : ℝ) : ℝ := q * 1228800 - q ^ 2 * 47909584896 + q ^ 3 * 22681960448000 - q ^ 4 * 1440287890292736 + q ^ 5 * 25873229882572800 -
                          q ^ 6 * 183368931293184000 +
                        q ^ 7 * 614258629468323840 -
                      q ^ 8 * 1091711196399403008 +
                    q ^ 9 * 1124791456149504000 -
                  q ^ 10 * 723717393839751168 +
                q ^ 11 * 304249765406146560 -
              q ^ 12 * 82936975037349888 +
            q ^ 13 * 13929931575705600 -
          q ^ 14 * 1338962033885184 +
        q ^ 15 * 65738826547200 -
      q ^ 16 * 1253826625536
private def b8 (q : ℝ) : ℝ := -(q * 4915200) + q ^ 2 * 766627086336 - q ^ 3 * 821341473996800 + q ^ 4 * 95352120017485824 -
                                q ^ 5 * 2845887571309363200 +
                              q ^ 6 * 32060191465030680576 -
                            q ^ 7 * 167495442068487536640 +
                          q ^ 8 * 460233151236709613568 -
                        q ^ 9 * 725737675056009707520 +
                      q ^ 10 * 703779563626546987008 -
                    q ^ 11 * 444465339058343116800 +
                  q ^ 12 * 189568590591937609728 -
                q ^ 13 * 54676337965085491200 +
              q ^ 14 * 10342260481727397888 -
            q ^ 15 * 1222973202943180800 +
          q ^ 16 * 84812489945579520 -
        q ^ 17 * 3093817198510080 +
      q ^ 18 * 45137758519296
private def v00 : ℝ := (77823589288666326500231483525535147042963486152333881423850577248705827605229713493546434462554055194962335967989336172661693329287113591496067967465209:ℝ)/
      1755127208175132818879075093054200815146392631621110036464129779666968099532774608328840277670502015842846312782112419312505038149413190000000000
private def v01 : ℝ := (213634858032934921254755799410551877313697330561115055300195851565570358045178979771160212930399966024545162329858804781715588254934373409344237054121171677:ℝ)/
      14041017665401062551032600744433606521171141052968880291713038237335744796262196866630722221364016126742770502256899354500040305195305520000000000
private def v11 : ℝ := (6252277575739794174596338789602460218609276873477589919459839916656154203221402741336384649789533473691285534227998318787688891731167030613030733844902491683:ℝ)/
      864062625563142310832775430426683478225916372490392633336186968451430449000750576408044444391631761645708953985039960276925557242788032000000000
/-- Quartic lower compensation bound obtained from the scale-eight tangent. -/
def g (q : ℝ) : ℝ :=
  3*(2*q-3)^2-(1000001/1000000)*(q/8-13/200)*
    ((2*q-3)*(8*q^2-30*q+15)/2+(2*q-3)^2/100000)
/-- Explicit diagonal-pair radial moments through order eight. -/
def rMoment (q : ℝ) : ℕ → ℝ
  | 0 => r0 q
  | 1 => r1 q
  | 2 => r2 q
  | 3 => r3 q
  | 4 => r4 q
  | 5 => r5 q
  | 6 => r6 q
  | 7 => r7 q
  | 8 => r8 q
  | _ => 0
/-- Explicit unequal-pair radial moments through order eight. -/
def bMoment (q : ℝ) : ℕ → ℝ
  | 0 => b0 q
  | 1 => b1 q
  | 2 => b2 q
  | 3 => b3 q
  | 4 => b4 q
  | 5 => b5 q
  | 6 => b6 q
  | 7 => b7 q
  | 8 => b8 q
  | _ => 0
/-- First cross-load row in Gaussian coordinates. -/
def u0 (q : ℝ) : Fin 5 → ℝ :=
  ![0,0,1/(256*q^2),(35-10*q)/(1024*q^3),35*(q-7)/(2048*q^3)]
/-- Second cross-load row in Gaussian coordinates. -/
def u1 (q : ℝ) : Fin 5 → ℝ :=
  ![0,0,0,1/(12288*q^3),-7*(q-7)/(24576*q^4)]
private def e00 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000)
private def e01 (m : ℕ → ℝ) : ℝ := -m 0 + m 1 * (1 / 8)
private def e02 (m : ℕ → ℝ) : ℝ := (m 0 * (3 / 4) + m 1 * (-3 / 16) + m 2 * (1 / 256) - 0)
private def e03 (m : ℕ → ℝ) : ℝ := (m 0 * (-5 / 8) + m 1 * (15 / 64) + m 2 * (-5 / 512) + m 3 * (1 / 12288) - 0)
private def e04 (m : ℕ → ℝ) : ℝ := (m 0 * (35 / 64) + m 1 * (-35 / 128) + m 2 * (35 / 2048) + m 3 * (-7 / 24576) + m 4 * (1 / 786432) -
      0)
private def e11 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000) + m 1 * (-1 / 4) + m 2 * (1 / 64)
private def e12 (m : ℕ → ℝ) : ℝ := (m 0 * (-3 / 4) + m 1 * (9 / 32) + m 2 * (-7 / 256) + m 3 * (1 / 2048) - 0)
private def e13 (m : ℕ → ℝ) : ℝ := (m 0 * (5 / 8) + m 1 * (-5 / 16) + m 2 * (5 / 128) + m 3 * (-1 / 768) + m 4 * (1 / 98304) -
      0)
private def e14 (m : ℕ → ℝ) : ℝ := (m 0 * (-35 / 64) + m 1 * (175 / 512) + m 2 * (-105 / 2048) + m 3 * (119 / 49152) + m 4 * (-29 / 786432) +
        m 5 * (1 / 6291456) -
      0)
private def e22 (m : ℕ → ℝ) : ℝ := m 0 * (1123 / 2000) + m 1 * (-9 / 32) + m 2 * (21 / 512) + m 3 * (-3 / 2048) + m 4 * (1 / 65536)
private def e23 (m : ℕ → ℝ) : ℝ := (m 0 * (-15 / 32) + m 1 * (75 / 256) + m 2 * (-55 / 1024) + m 3 * (23 / 8192) + m 4 * (-7 / 131072) +
        m 5 * (1 / 3145728) -
      0)
private def e24 (m : ℕ → ℝ) : ℝ := (m 0 * (105 / 256) + m 1 * (-315 / 1024) + m 2 * (1085 / 16384) + m 3 * (-147 / 32768) + m 4 * (127 / 1048576) +
          m 5 * (-17 / 12582912) +
        m 6 * (1 / 201326592) -
      0)
private def e33 (m : ℕ → ℝ) : ℝ := m 0 * (3117 / 8000) + m 1 * (-75 / 256) + m 2 * (275 / 4096) + m 3 * (-115 / 24576) + m 4 * (35 / 262144) +
        m 5 * (-5 / 3145728) +
      m 6 * (1 / 150994944)
private def e34 (m : ℕ → ℝ) : ℝ := (m 0 * (-175 / 512) + m 1 * (1225 / 4096) + m 2 * (-2625 / 32768) + m 3 * (5425 / 786432) + m 4 * (-1615 / 6291456) +
            m 5 * (75 / 16777216) +
          m 6 * (-43 / 1207959552) +
        m 7 * (1 / 9663676416) -
      0)
private def e44 (m : ℕ → ℝ) : ℝ := m 0 * (152613 / 512000) + m 1 * (-1225 / 4096) + m 2 * (6125 / 65536) + m 3 * (-7595 / 786432) +
              m 4 * (11305 / 25165824) +
            m 5 * (-175 / 16777216) +
          m 6 * (301 / 2415919104) +
        m 7 * (-7 / 9663676416) +
      m 8 * (1 / 618475290624)
private def entryPoly (m : ℕ → ℝ) (i j : Fin 5) : ℝ :=
  match i.val,j.val with
  | 0,0 => e00 m
  | 0,1 | 1,0 => e01 m
  | 0,2 | 2,0 => e02 m
  | 0,3 | 3,0 => e03 m
  | 0,4 | 4,0 => e04 m
  | 1,1 => e11 m
  | 1,2 | 2,1 => e12 m
  | 1,3 | 3,1 => e13 m
  | 1,4 | 4,1 => e14 m
  | 2,2 => e22 m
  | 2,3 | 3,2 => e23 m
  | 2,4 | 4,2 => e24 m
  | 3,3 => e33 m
  | 3,4 | 4,3 => e34 m
  | 4,4 => e44 m
  | _,_ => 0

/-- Leading Gaussian form with a scalar cross-load and a diagonal error allowance. -/
def polyModel (q z c e : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  entryPoly (fun k => (rMoment q k+8*z*bMoment q k)/q^k) i j+
  c*(v00*u0 q i*u0 q j+v01*(u0 q i*u1 q j+u1 q i*u0 q j)+v11*u1 q i*u1 q j)+
  (if i=j then (rMoment q 0+8*z*bMoment q 0)/1000+e else 0)

/-- Normalize exact rational entries and Schur signs of the radial cross-load model. -/
scoped macro "norm_cross_model" : tactic =>
  `(tactic| norm_num [delta,schur,minor,determinant,tailIndex,polyModel,
    v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44])


theorem center_tangent_eight {x : ℝ} (hx : 0 ≤ x) :
    2*x ≤ Real.pi*Real.exp (2*x)/8-13/200 := by
  have h := Real.sum_le_exp_of_nonneg (x := (187/200 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have he : (2547/1000 : ℝ) ≤ Real.exp (187/200) := by linarith only [h]
  have hpi : (31415/10000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hp := mul_le_mul hpi he (by norm_num : (0 : ℝ) ≤ 2547/1000) Real.pi_pos.le
  have hbase : (8 : ℝ) ≤ Real.pi*Real.exp (187/200) := by nlinarith only [hp]
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*x-187/200))
    (show 0 ≤ Real.pi*Real.exp (187/200) by positivity)
  have hs := mul_le_mul_of_nonneg_right hbase
    (show 0 ≤ 1+(2*x-187/200) by linarith only [hx])
  simp only [mul_assoc] at ht
  rw [← Real.exp_add,show (187/200 : ℝ)+(2*x-187/200)=2*x by ring] at ht
  nlinarith only [ht,hs]


/-- Rational upper bound for the unequal-pair weight at scale eight. -/
def weight : ℝ := 37751346/1000000000000000000
/-- Rational upper bound for the normalized complete compensation at scale eight. -/
def upperCompensation : ℝ :=
  (3*(1000001/1000000)^2-(14/15)*((8*8^2-30*8+15)/(2*(2*8-3))-1/100000))*(2*8-3)^2
/-- Half-load lower comparison, including a one-tenth diagonal reserve. -/
def lowerEight : Matrix (Fin 5) (Fin 5) ℝ := polyModel 8 weight (g 8/2) (-1/10)
/-- Full-load upper comparison, including a one-tenth diagonal allowance. -/
def upperEight : Matrix (Fin 5) (Fin 5) ℝ := polyModel 8 weight upperCompensation (1/10)
theorem decay_bounds :
    (37751345/1000000000000000000 : ℝ) ≤ Real.exp (-24) ∧
    Real.exp (-24) ≤ weight := by
  have hlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 24
  have hhi := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 24
  rw [← Real.exp_nat_mul] at hlo hhi
  simp only [Nat.cast_ofNat,mul_one] at hlo hhi
  have hl : (1000000000000000000/37751346 : ℝ) ≤ Real.exp 24 :=
    (by norm_num : (1000000000000000000/37751346 : ℝ) ≤ (2.7182818283 : ℝ)^24).trans hlo
  have hu : Real.exp 24 ≤ (1000000000000000000/37751345 : ℝ) :=
    hhi.trans (by norm_num : (2.7182818286 : ℝ)^24 ≤ 1000000000000000000/37751345)
  rw [Real.exp_neg,inv_eq_one_div]
  constructor
  · norm_num only [one_div]
    have h := one_div_le_one_div_of_le (Real.exp_pos 24) hu
    norm_num at h
    exact h
  · norm_num only [one_div,weight]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000000000000000/37751346) hl
    norm_num at h
    exact h
theorem center_lower_base : Real.pi*Real.exp (14/15) ≤ (8 : ℝ) := by
  have h1 : Real.exp 1 ≤ (2719/1000 : ℝ) := by linarith only [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h1 14
  rw [← Real.exp_nat_mul] at hp
  simp only [Nat.cast_ofNat,mul_one] at hp
  have hpow : Real.exp (14/15 : ℝ)^15 ≤ (28/11 : ℝ)^15 := by
    rw [← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    rw [show (15 : ℝ)*(14/15)=14 by ring]
    exact hp.trans (by norm_num : (2719/1000 : ℝ)^14 ≤ (28/11 : ℝ)^15)
  have he : Real.exp (14/15 : ℝ) ≤ 28/11 := by
    by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) (by norm_num : (0 : ℝ) ≤ 28/11)
      (by norm_num : (15 : ℕ) ≠ 0)
    linarith only [hh,hpow]
  have hpi : Real.pi ≤ (22/7 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hh := mul_le_mul hpi he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 22/7)
  norm_num at hh
  exact hh

private theorem lower_sign_0 : 0 < lowerEight 0 0 := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem lower_sign_1 : 0 < delta lowerEight := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem lower_sign_2 : 0 < schur lowerEight 0 0 := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem lower_sign_3 : 0 < minor lowerEight := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem lower_sign_4 : 0 < determinant lowerEight := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem upper_sign_0 : 0 < upperEight 0 0 := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem upper_sign_1 : 0 < delta upperEight := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem upper_sign_2 : 0 < schur upperEight 0 0 := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem upper_minor_neg : minor upperEight < 0 := by
  norm_num [delta,schur,minor,determinant,tailIndex,lowerEight,upperEight,polyModel,g,
    weight,upperCompensation,v00,v01,v11,u0,u1,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

/-- Explicit Gaussian congruence entries for a Hankel moment sequence. -/
def gaussianEntry (m : ℕ → ℝ) (i j : Fin 5) : ℝ :=
  entryPoly m i j+if i.val=j.val then m 0/1000 else 0
/-- The unequal-pair Gaussian form normalized at scale eight. -/
def mixedGram : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianEntry (fun k => 8*bMoment 8 k/8^k)
/-- A pure radial Gaussian form normalized by powers of eight. -/
def pureGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianEntry (fun k => rMoment q k/8^k)

private theorem mixed_bound_0 (j : Fin 5) : |mixedGram 0 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem mixed_bound_1 (j : Fin 5) : |mixedGram 1 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem mixed_bound_2 (j : Fin 5) : |mixedGram 2 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem mixed_bound_3 (j : Fin 5) : |mixedGram 3 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem mixed_bound_4 (j : Fin 5) : |mixedGram 4 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_two_bound_0 (j : Fin 5) : |(pureGram 32) 0 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_two_bound_1 (j : Fin 5) : |(pureGram 32) 1 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_two_bound_2 (j : Fin 5) : |(pureGram 32) 2 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_two_bound_3 (j : Fin 5) : |(pureGram 32) 3 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_two_bound_4 (j : Fin 5) : |(pureGram 32) 4 j| ≤ 10000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_three_bound_0 (j : Fin 5) : |(pureGram 72) 0 j| ≤ 1000000000000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_three_bound_1 (j : Fin 5) : |(pureGram 72) 1 j| ≤ 1000000000000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_three_bound_2 (j : Fin 5) : |(pureGram 72) 2 j| ≤ 1000000000000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_three_bound_3 (j : Fin 5) : |(pureGram 72) 3 j| ≤ 1000000000000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]

private theorem pure_three_bound_4 (j : Fin 5) : |(pureGram 72) 4 j| ≤ 1000000000000000000000000 := by
  fin_cases j <;> norm_num [Fin.ext_iff,mixedGram,pureGram,gaussianEntry,rMoment,bMoment,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,b0,b1,b2,b3,b4,b5,b6,b7,b8,
    entryPoly,e00,e01,e02,e03,e04,e11,e12,e13,e14,e22,e23,e24,e33,e34,e44]


theorem radial_eq (q : ℝ) (k : ℕ) (hk : k ≤ 8) :
    (thetaPairRadialEvenPolynomial (q^2) k).eval (2*q) = rMoment q k := by
  interval_cases k
  · exact radial_0 q
  · exact radial_1 q
  · exact radial_2 q
  · exact radial_3 q
  · exact radial_4 q
  · exact radial_5 q
  · exact radial_6 q
  · exact radial_7 q
  · exact radial_8 q

theorem mixed_eq (q : ℝ) (k : ℕ) (hk : k ≤ 8) :
    (thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q) = bMoment q k := by
  interval_cases k
  · exact mixed_0 q
  · exact mixed_1 q
  · exact mixed_2 q
  · exact mixed_3 q
  · exact mixed_4 q
  · exact mixed_5 q
  · exact mixed_6 q
  · exact mixed_7 q
  · exact mixed_8 q

/-- The explicit entries are the Gaussian congruence of the Hankel moments. -/
theorem gaussian_eq (m : ℕ → ℝ) :
    gaussianGram (fun a b : Fin 5 => m (a.val+b.val)) = gaussianEntry m := by
  ext i j
  have h := FifthLeadingPair.entry_eq_entryPoly m i j
  change gaussianGram (fun a b : Fin 5 => m (a.val+b.val)) i j-
    (if i.val=j.val then m 0/1000 else 0)=entryPoly m i j at h
  simp only [gaussianEntry]
  linarith only [h]

private theorem entryPoly_symmetric (m : ℕ → ℝ) (i j : Fin 5) :
    entryPoly m i j = entryPoly m j i :=
  FifthLeadingPair.entryPoly_symmetric m i j

private theorem polyModel_symmetric (q z c e : ℝ) (i j : Fin 5) :
    polyModel q z c e i j = polyModel q z c e j i := by
  simp only [polyModel,entryPoly_symmetric _ i j,eq_comm (a := i) (b := j)]
  ring

/-- The rational half-load lower comparison is strictly positive. -/
theorem lowerEight_posDef : lowerEight.PosDef :=
  posDef_of_schur_signs (polyModel_symmetric _ _ _ _)
    lower_sign_0 lower_sign_1 lower_sign_2 lower_sign_3 lower_sign_4

-- Lifting a negative Schur direction through the positive two-coordinate head.
private theorem negative_of_schur_minor {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : ∀ i j, A i j = A j i) (hr : 0 < A 0 0) (hd : 0 < delta A)
    (hs : 0 < schur A 0 0) (hm : minor A < 0) :
    ∃ v : Fin 5 → ℝ, v ⬝ᵥ (A *ᵥ v) < 0 := by
  let u := -schur A 0 1
  let v := schur A 0 0
  let p := A 0 2*u+A 0 3*v
  let r := A 1 2*u+A 1 3*v
  let x0 := A 0 1*r-A 1 1*p
  let x1 := A 0 1*p-A 0 0*r
  have hfirst : firstCoordinate A x0 x1 (delta A*u) (delta A*v) 0 = 0 := by
    dsimp only [firstCoordinate,x0,x1,p,r,delta]
    ring
  have hsecond : secondCoordinate A x1 (delta A*u) (delta A*v) 0 = 0 := by
    dsimp only [secondCoordinate,x1,p,r]
    ring
  have htail : tailQuadratic A (delta A*u) (delta A*v) 0 =
      (delta A)^2*schur A 0 0*minor A := by
    dsimp only [tailQuadratic,u,v,minor]
    ring
  have he := quadratic_square_completion A x0 x1 (delta A*u) (delta A*v) 0
  rw [hfirst,hsecond,htail] at he
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_add] at he
  have hn : quadratic A x0 x1 (delta A*u) (delta A*v) 0 < 0 := by
    apply neg_of_mul_neg_left _ (mul_pos hr hd).le
    rw [mul_comm,he]
    exact mul_neg_of_pos_of_neg hr
      (mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos hd) hs) hm)
  refine ⟨![x0,x1,delta A*u,delta A*v,0], ?_⟩
  rw [matrix_energy hA]
  change quadratic A x0 x1 (delta A*u) (delta A*v) 0 < 0
  exact hn

/-- The rational full-load upper comparison has a strictly negative direction. -/
theorem upperEight_negative : ∃ v : Fin 5 → ℝ, v ⬝ᵥ (upperEight *ᵥ v) < 0 :=
  negative_of_schur_minor (polyModel_symmetric _ _ _ _)
    upper_sign_0 upper_sign_1 upper_sign_2 upper_minor_neg

theorem mixed_bound (i j : Fin 5) : |(mixedGram) i j| ≤ 10000000000000000 := by
  fin_cases i
  · exact mixed_bound_0 j
  · exact mixed_bound_1 j
  · exact mixed_bound_2 j
  · exact mixed_bound_3 j
  · exact mixed_bound_4 j

theorem pure_two_bound (i j : Fin 5) : |(pureGram 32) i j| ≤ 10000000000000000 := by
  fin_cases i
  · exact pure_two_bound_0 j
  · exact pure_two_bound_1 j
  · exact pure_two_bound_2 j
  · exact pure_two_bound_3 j
  · exact pure_two_bound_4 j

theorem pure_three_bound (i j : Fin 5) : |(pureGram 72) i j| ≤ 1000000000000000000000000 := by
  fin_cases i
  · exact pure_three_bound_0 j
  · exact pure_three_bound_1 j
  · exact pure_three_bound_2 j
  · exact pure_three_bound_3 j
  · exact pure_three_bound_4 j

private theorem paid00 : paidSevenSchur 0 0 = v00 :=
  paidSevenSchur_00
private theorem paid01 : paidSevenSchur 0 1 = v01 :=
  paidSevenSchur_01
private theorem paid11 : paidSevenSchur 1 1 = v11 :=
  paidSevenSchur_11
private theorem paid10 : paidSevenSchur 1 0 = v01 := by
  have h := congrFun (congrFun crossCoefficient_posDef.isHermitian 0) 1
  simp only [Matrix.conjTranspose_apply,star_trivial,paid01] at h
  exact h

/-- The fixed cross-load in the normalized Gaussian basis. -/
def loadGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (loadMap*nativeBasis q)ᴴ*paidSevenSchur*(loadMap*nativeBasis q)

private theorem load_row_zero {q : ℝ} (hq : q ≠ 0) (j : Fin 5) :
    (loadMap*nativeBasis q) 0 j = u0 q j := by
  fin_cases j <;> norm_num [loadMap,nativeBasis,gaussianBasis,u0,Matrix.mul_apply,
    Fin.sum_univ_succ]
  all_goals field_simp [hq] <;> ring

private theorem load_row_one {q : ℝ} (hq : q ≠ 0) (j : Fin 5) :
    (loadMap*nativeBasis q) 1 j = u1 q j := by
  fin_cases j <;> norm_num [loadMap,nativeBasis,gaussianBasis,u1,Matrix.mul_apply,
    Fin.sum_univ_succ]
  all_goals field_simp [hq] <;> ring

private theorem loadGram_entry {q : ℝ} (hq : q ≠ 0) (i j : Fin 5) :
    loadGram q i j = v00*u0 q i*u0 q j+
      v01*(u0 q i*u1 q j+u1 q i*u0 q j)+v11*u1 q i*u1 q j := by
  change (∑ a : Fin 2, (∑ b : Fin 2,
    star ((loadMap*nativeBasis q) b i)*paidSevenSchur b a)*(loadMap*nativeBasis q) a j) = _
  simp only [Fin.sum_univ_two,star_trivial,load_row_zero hq,load_row_one hq,
    paid00,paid01,paid10,paid11]
  ring

/-- The load form is nonnegative at every scale. -/
theorem loadGram_posSemidef (q : ℝ) : (loadGram q).PosSemidef :=
  crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same _

private theorem leadingMatrix_eq (q z : ℝ) : leadingMatrix q z =
    (fun i j : Fin 5 => (rMoment q (i.val+j.val)+8*z*bMoment q (i.val+j.val))/q^(i.val+j.val) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  simp only [leadingMatrix,leadingMoment]
  rw [radial_eq q (i.val+j.val) (by omega),mixed_eq q (i.val+j.val) (by omega)]

/-- Exact identification of the displayed rational model with the radial source. -/
theorem polyModel_eq {q : ℝ} (hq : q ≠ 0) (z c e : ℝ) :
    polyModel q z c e = gaussianGram (leadingMatrix q z)+c • loadGram q+e • 1 := by
  rw [leadingMatrix_eq,gaussian_eq (fun k => (rMoment q k+8*z*bMoment q k)/q^k)]
  ext i j
  simp only [polyModel,gaussianEntry,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,loadGram_entry hq,pow_zero,div_one,← Fin.ext_iff]
  by_cases hij : i = j <;> simp only [hij,ite_true,ite_false,mul_one,mul_zero] <;> ring

/-- Moving the unequal-pair weight changes only its literal mixed Gram form. -/
theorem leading_weight_difference (z w : ℝ) :
    gaussianGram (leadingMatrix 8 z)-gaussianGram (leadingMatrix 8 w) =
      (z-w) • mixedGram := by
  let B : Matrix (Fin 5) (Fin 5) ℝ :=
    fun i j => 8*bMoment 8 (i.val+j.val)/8^(i.val+j.val)
  have hm : leadingMatrix 8 z = leadingMatrix 8 w+(z-w) • B := by
    rw [leadingMatrix_eq,leadingMatrix_eq]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,B]
    ring
  have hB : gaussianGram B=mixedGram :=
    gaussian_eq (fun k => 8*bMoment 8 k/8^k)
  rw [hm,gaussianGram_add,gaussianGram_smul,hB]
  abel

end GaloisForLFunctions.ThetaCuspSections.EightCrossData
