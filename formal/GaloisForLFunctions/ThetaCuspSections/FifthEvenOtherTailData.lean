import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients
/-!
# Radial moments of the remaining unequal theta pairs

The four pairs `(1,4)`, `(2,3)`, `(2,4)`, `(3,4)` give signed radial
polynomials of degree at most eighteen. Their moment functionals preserve
scalar weights, convex interpolation, and the finite moment expansion.
-/
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.FifthOtherTail
open _root_.RHTower

namespace p14

/-- The signed pair polynomial applied to power moments. -/
def pairLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => m 0 * 9 + m 2 * 64 - m 1 * 102
 | 1 => -(m 2 * 25836) - m 4 * 57600 + m 1 * 1020 + m 3 * 96152
 | 2 => m 2 * 621456 + m 4 * 65993808 + m 6 * 51840000 - m 1 * 4080 - m 3 * 12815552 - m 5 * 106120800
 | 3 => -(m 2 * 10775616) - m 4 * 10704678720 - m 6 * 133210008000 - m 8 * 46656000000 + m 1 * 16320 + m 3 * 674934272 +
    m 5 * 59410038720 + m 7 * 127234800000
 | 4 => m 2 * 175739136 + m 4 * 1012927097088 + m 6 * 70788471774720 + m 8 * 239764989600000 + m 10 * 41990400000000 - m
    1 * 65280 - m 3 * 27970460672 - m 5 * 12925455406080 - m 7 * 184162374144000 - m 9 * 155755224000000
 | 5 => -(m 2 * 2825143296) - m 4 * 78248076579840 - m 6 * 20530043635921920 - m 8 * 298723447100160000 - m 10 *
    401595660720000000 - m 12 * 37791360000000000 + m 1 * 261120 + m 3 * 1066724360192 + m 5 * 1930285501793280 + m 7 *
    107451168908912640 + m 9 * 461209758192000000 + m 11 * 188720604000000000
 | 6 => m 2 * 45255561216 + m 4 * 5517353985773568 + m 6 * 4451489350847447040 + m 8 * 200164158569571102720 + m 10 *
    972017569980864000000 + m 12 * 634948228296000000000 + m 14 * 34012224000000000000 - m 1 * 1044480 - m 3 *
    39362771566592 - m 5 * 241594529945640960 - m 7 * 40505760084431093760 - m 9 * 570159998280930816000 - m 11 *
    1010731090533120000000 - m 13 * 223814605680000000000
 | 7 => -(m 2 * 724302053376) - m 4 * 371874824741928960 - m 6 * 825334657812221706240 - m 8 * 95587111638122857758720 -
    m 10 * 1266452410158373920768000 - m 12 * 2667845961801296640000000 - m 14 * 954202202125920000000000 - m 16 *
    30611001600000000000000 + m 1 * 4177920 + m 3 * 1432447250726912 + m 5 * 27561070880771850240 + m 7 *
    12035701307522254602240 + m 9 * 444150462579566812692480 + m 11 * 2287819757397933158400000 + m 13 *
    2012190508220256000000000 + m 15 * 259253925912000000000000
 | 8 => m 2 * 11589685149696 + m 4 * 24482273640054325248 + m 6 * 139706663293691730984960 + m 8 *
    37305801021327270168821760 + m 10 * 1147000216625857105418649600 + m 12 * 6026715545288790104064000000 + m 14 *
    6475978339596541440000000000 + m 16 * 1370571756258960000000000000 + m 18 * 27549901440000000000000000 - m 3 *
    51814366058381312 - m 5 * 2984603728680454717440 - m 7 * 3106960519072962175303680 - m 9 *
    262672882107196935772569600 - m 11 * 3229787849940936937635840000 - m 13 * 7583553851809455636480000000 - m 15 *
    3712533256916582400000000000 - m 17 * 293693428476000000000000000 - m 1 * 16711680
 | _ => 0

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k=radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem pairLinear_pow_0 (q : ℝ) :
 pairLinear (fun n => q^n) 0=(thetaPairRadialEvenPolynomial (16*q^2) 0).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_0_0,radialCoeffs_0_1,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_1 (q : ℝ) :
 pairLinear (fun n => q^n) 1=(thetaPairRadialEvenPolynomial (16*q^2) 1).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_2 (q : ℝ) :
 pairLinear (fun n => q^n) 2=(thetaPairRadialEvenPolynomial (16*q^2) 2).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_3 (q : ℝ) :
 pairLinear (fun n => q^n) 3=(thetaPairRadialEvenPolynomial (16*q^2) 3).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_4 (q : ℝ) :
 pairLinear (fun n => q^n) 4=(thetaPairRadialEvenPolynomial (16*q^2) 4).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_5 (q : ℝ) :
 pairLinear (fun n => q^n) 5=(thetaPairRadialEvenPolynomial (16*q^2) 5).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_6 (q : ℝ) :
 pairLinear (fun n => q^n) 6=(thetaPairRadialEvenPolynomial (16*q^2) 6).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_7 (q : ℝ) :
 pairLinear (fun n => q^n) 7=(thetaPairRadialEvenPolynomial (16*q^2) 7).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_8 (q : ℝ) :
 pairLinear (fun n => q^n) 8=(thetaPairRadialEvenPolynomial (16*q^2) 8).eval (17*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

/-- Each retained linear functional is the exact reflected pair polynomial. -/
theorem pairLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => q^n) k=(thetaPairRadialEvenPolynomial (16*q^2) k).eval (17*q) := by
 interval_cases k
 · exact pairLinear_pow_0 q
 · exact pairLinear_pow_1 q
 · exact pairLinear_pow_2 q
 · exact pairLinear_pow_3 q
 · exact pairLinear_pow_4 q
 · exact pairLinear_pow_5 q
 · exact pairLinear_pow_6 q
 · exact pairLinear_pow_7 q
 · exact pairLinear_pow_8 q

/-- Scalar radial weights pass through every pair moment. -/
theorem pairLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => c*m n) k=c*pairLinear m k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- Convex gamma interpolation is exact for the signed pair moments. -/
theorem pairLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun j => (1-t)*m j+t*n j) k=
  (1-t)*pairLinear m k+t*pairLinear n k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- The pair moment depends only on the nineteen retained power moments. -/
theorem pairLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 pairLinear m k=∑ j ∈ Finset.range 19,
  pairLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [pairLinear,Finset.sum_range_succ] <;> ring

end p14

namespace p23

/-- The signed pair polynomial applied to power moments. -/
def pairLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => m 0 * 9 + m 2 * 144 - m 1 * 78
 | 1 => -(m 2 * 6156) - m 4 * 14400 + m 1 * 780 + m 3 * 15288
 | 2 => m 2 * 220176 + m 4 * 4162128 + m 6 * 1440000 - m 1 * 3120 - m 3 * 1629888 - m 5 * 5272800
 | 3 => -(m 2 * 4009536) - m 4 * 741184320 - m 6 * 2520792000 - m 8 * 144000000 + m 1 * 12480 + m 3 * 113837568 + m 5 *
    1844057280 + m 7 * 1201200000
 | 4 => m 2 * 66099456 + m 4 * 86652004608 + m 6 * 1142989585920 + m 8 * 969213600000 + m 10 * 14400000000 - m 1 * 49920
    - m 3 * 5132295168 - m 5 * 477861995520 - m 7 * 1573737984000 - m 9 * 217464000000
 | 5 => -(m 2 * 1065378816) - m 4 * 7377052554240 - m 6 * 400910215173120 - m 8 * 1237810256640000 - m 10 *
    271160880000000 - m 12 * 1440000000000 + m 1 * 199680 + m 3 * 201915138048 + m 5 * 85839332766720 + m 7 *
    913846131394560 + m 9 * 870927408000000 + m 11 * 34476000000000
 | 6 => m 2 * 17077211136 + m 4 * 545033972748288 + m 6 * 103552351670845440 + m 8 * 897283335453880320 + m 10 *
    894625727424000000 + m 12 * 61847496000000000 + m 14 * 144000000000000 - m 1 * 798720 - m 3 * 7545810075648 - m 5 *
    11936819251568640 - m 7 * 416007395666903040 - m 9 * 1185518280900096000 - m 11 * 340416510720000000 - m 13 *
    5020080000000000
 | 7 => -(m 2 * 273359978496) - m 4 * 37619316299612160 - m 6 * 21493314729538928640 - m 8 * 515424848467041976320 - m
    10 * 1344528951143718912000 - m 12 * 455375000021760000000 - m 14 * 12281021280000000000 - m 16 * 14400000000000000
    + m 1 * 3194880 + m 3 * 276088704073728 + m 5 * 1445018574471413760 + m 7 * 146589703642631208960 + m 9 *
    1047386723816394424320 + m 11 * 1050895484704665600000 + m 13 * 104360247264000000000 + m 15 * 689208000000000000
 | 8 => m 2 * 4374258057216 + m 4 * 2507979923043975168 + m 6 * 3904477529748223426560 + m 8 * 237863021233473590722560
    + m 10 * 1419958250765664573849600 + m 12 * 1401523131484329984000000 + m 14 * 178360263728640000000000 + m 16 *
    2207970960000000000000 + m 18 * 1440000000000000000 - m 3 * 10010264806883328 - m 5 * 161970605970263900160 - m 7 *
    42650893791223252254720 - m 9 * 742935452298016908902400 - m 11 * 1766488331543367843840000 - m 13 *
    661884016262676480000000 - m 15 * 26915002982400000000000 - m 17 * 90636000000000000000 - m 1 * 12779520
 | _ => 0

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k=radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem pairLinear_pow_0 (q : ℝ) :
 pairLinear (fun n => q^n) 0=(thetaPairRadialEvenPolynomial (36*q^2) 0).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_0_0,radialCoeffs_0_1,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_1 (q : ℝ) :
 pairLinear (fun n => q^n) 1=(thetaPairRadialEvenPolynomial (36*q^2) 1).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_2 (q : ℝ) :
 pairLinear (fun n => q^n) 2=(thetaPairRadialEvenPolynomial (36*q^2) 2).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_3 (q : ℝ) :
 pairLinear (fun n => q^n) 3=(thetaPairRadialEvenPolynomial (36*q^2) 3).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_4 (q : ℝ) :
 pairLinear (fun n => q^n) 4=(thetaPairRadialEvenPolynomial (36*q^2) 4).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_5 (q : ℝ) :
 pairLinear (fun n => q^n) 5=(thetaPairRadialEvenPolynomial (36*q^2) 5).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_6 (q : ℝ) :
 pairLinear (fun n => q^n) 6=(thetaPairRadialEvenPolynomial (36*q^2) 6).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_7 (q : ℝ) :
 pairLinear (fun n => q^n) 7=(thetaPairRadialEvenPolynomial (36*q^2) 7).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_8 (q : ℝ) :
 pairLinear (fun n => q^n) 8=(thetaPairRadialEvenPolynomial (36*q^2) 8).eval (13*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

/-- Each retained linear functional is the exact reflected pair polynomial. -/
theorem pairLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => q^n) k=(thetaPairRadialEvenPolynomial (36*q^2) k).eval (13*q) := by
 interval_cases k
 · exact pairLinear_pow_0 q
 · exact pairLinear_pow_1 q
 · exact pairLinear_pow_2 q
 · exact pairLinear_pow_3 q
 · exact pairLinear_pow_4 q
 · exact pairLinear_pow_5 q
 · exact pairLinear_pow_6 q
 · exact pairLinear_pow_7 q
 · exact pairLinear_pow_8 q

/-- Scalar radial weights pass through every pair moment. -/
theorem pairLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => c*m n) k=c*pairLinear m k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- Convex gamma interpolation is exact for the signed pair moments. -/
theorem pairLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun j => (1-t)*m j+t*n j) k=
  (1-t)*pairLinear m k+t*pairLinear n k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- The pair moment depends only on the nineteen retained power moments. -/
theorem pairLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 pairLinear m k=∑ j ∈ Finset.range 19,
  pairLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [pairLinear,Finset.sum_range_succ] <;> ring

end p23

namespace p24

/-- The signed pair polynomial applied to power moments. -/
def pairLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => m 0 * 9 + m 2 * 256 - m 1 * 120
 | 1 => -(m 2 * 21696) - m 4 * 147456 + m 1 * 1200 + m 3 * 89600
 | 2 => m 2 * 635136 + m 4 * 51400704 + m 6 * 84934656 - m 1 * 4800 - m 3 * 10956800 - m 5 * 110592000
 | 3 => -(m 2 * 11314176) - m 4 * 9066725376 - m 6 * 105637478400 - m 8 * 48922361856 + m 1 * 19200 + m 3 * 644710400 +
    m 5 * 44123750400 + m 7 * 124853944320
 | 4 => m 2 * 185634816 + m 4 * 934659293184 + m 6 * 51195974516736 + m 8 * 182753559576576 + m 10 * 28179280429056 - m
    1 * 76800 - m 3 * 27720089600 - m 5 * 10651670937600 - m 7 * 129309050142720 - m 9 * 122795128258560
 | 5 => -(m 2 * 2988589056) - m 4 * 75231424413696 - m 6 * 16394975340134400 - m 8 * 195800762104676352 - m 10 *
    262708386619981824 - m 12 * 16231265527136256 + m 1 * 307200 + m 3 * 1072116531200 + m 5 * 1725054241996800 + m 7 *
    75671510282403840 + m 9 * 303489871773696000 + m 11 * 109053815260446720
 | 6 => m 2 * 47891152896 + m 4 * 5413421542539264 + m 6 * 3849046146328559616 + m 8 * 136970408270644641792 + m 10 *
    581188463010766651392 + m 12 * 325229925183610945536 + m 14 * 9349208943630483456 - m 1 * 1228800 - m 3 *
    39791388262400 - m 5 * 226157557658419200 - m 7 * 31322220341640560640 - m 9 * 355895697569501675520 - m 11 *
    580391731429008998400 - m 13 * 90083523675606220800
 | 7 => -(m 2 * 766553358336) - m 4 * 368713699914940416 - m 6 * 751079142576881664000 - m 8 * 71546384967231275532288 -
    m 10 * 758872689962910920736768 - m 12 * 1391451544588227138551808 - m 14 * 359424884132656818683904 - m 16 *
    5385144351531158470656 + m 1 * 4915200 + m 3 * 1451645468672000 + m 5 * 26494187399754547200 + m 7 *
    10064013385209017794560 + m 9 * 294857331480855576576000 + m 11 * 1276116008042062141194240 + m 13 *
    934821883643332814438400 + m 15 * 70586527524410150092800
 | 8 => m 2 * 12266033381376 + m 4 * 24410142724476370944 + m 6 * 131318544240765667639296 + m 8 *
    30161839799449001234792448 + m 10 * 737966359709270133448900608 + m 12 * 3180433191176505136930357248 + m 14 *
    2776229408483273719758716928 + m 16 * 364266870608592858167377920 + m 18 * 3101843146481947279097856 - m 3 *
    52565854335795200 - m 5 * 2914188873020787916800 - m 7 * 2744245322850099800309760 - m 9 *
    190247777089882608768122880 - m 11 * 1864222749473764768166707200 - m 13 * 3669266928516958977313996800 - m 15 *
    1313157477631333120553779200 - m 17 * 53151374749612534105374720 - m 1 * 19660800
 | _ => 0

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k=radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem pairLinear_pow_0 (q : ℝ) :
 pairLinear (fun n => q^n) 0=(thetaPairRadialEvenPolynomial (64*q^2) 0).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_0_0,radialCoeffs_0_1,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_1 (q : ℝ) :
 pairLinear (fun n => q^n) 1=(thetaPairRadialEvenPolynomial (64*q^2) 1).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_2 (q : ℝ) :
 pairLinear (fun n => q^n) 2=(thetaPairRadialEvenPolynomial (64*q^2) 2).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_3 (q : ℝ) :
 pairLinear (fun n => q^n) 3=(thetaPairRadialEvenPolynomial (64*q^2) 3).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_4 (q : ℝ) :
 pairLinear (fun n => q^n) 4=(thetaPairRadialEvenPolynomial (64*q^2) 4).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_5 (q : ℝ) :
 pairLinear (fun n => q^n) 5=(thetaPairRadialEvenPolynomial (64*q^2) 5).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_6 (q : ℝ) :
 pairLinear (fun n => q^n) 6=(thetaPairRadialEvenPolynomial (64*q^2) 6).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_7 (q : ℝ) :
 pairLinear (fun n => q^n) 7=(thetaPairRadialEvenPolynomial (64*q^2) 7).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_8 (q : ℝ) :
 pairLinear (fun n => q^n) 8=(thetaPairRadialEvenPolynomial (64*q^2) 8).eval (20*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

/-- Each retained linear functional is the exact reflected pair polynomial. -/
theorem pairLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => q^n) k=(thetaPairRadialEvenPolynomial (64*q^2) k).eval (20*q) := by
 interval_cases k
 · exact pairLinear_pow_0 q
 · exact pairLinear_pow_1 q
 · exact pairLinear_pow_2 q
 · exact pairLinear_pow_3 q
 · exact pairLinear_pow_4 q
 · exact pairLinear_pow_5 q
 · exact pairLinear_pow_6 q
 · exact pairLinear_pow_7 q
 · exact pairLinear_pow_8 q

/-- Scalar radial weights pass through every pair moment. -/
theorem pairLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => c*m n) k=c*pairLinear m k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- Convex gamma interpolation is exact for the signed pair moments. -/
theorem pairLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun j => (1-t)*m j+t*n j) k=
  (1-t)*pairLinear m k+t*pairLinear n k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- The pair moment depends only on the nineteen retained power moments. -/
theorem pairLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 pairLinear m k=∑ j ∈ Finset.range 19,
  pairLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [pairLinear,Finset.sum_range_succ] <;> ring

end p24

namespace p34

/-- The signed pair polynomial applied to power moments. -/
def pairLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => m 0 * 9 + m 2 * 576 - m 1 * 150
 | 1 => -(m 2 * 19116) - m 4 * 112896 + m 1 * 1500 + m 3 * 87000
 | 2 => m 2 * 755856 + m 4 * 37994064 + m 6 * 22127616 - m 1 * 6000 - m 3 * 8376000 - m 5 * 73500000
 | 3 => -(m 2 * 13893696) - m 4 * 6518519616 - m 6 * 61555838400 - m 8 * 4337012736 + m 1 * 24000 + m 3 * 662208000 + m
    5 * 27965208000 + m 7 * 34320854400
 | 4 => m 2 * 229499136 + m 4 * 847133247744 + m 6 * 29363250986496 + m 8 * 50686009549056 + m 10 * 850054496256 - m 1 *
    96000 - m 3 * 30717312000 - m 5 * 7296170112000 - m 7 * 66421729382400 - m 9 * 12365004019200
 | 5 => -(m 2 * 3700786176) - m 4 * 75160377332736 - m 6 * 10654288473830400 - m 8 * 89576100506253312 - m 10 *
    28747322578996224 - m 12 * 166610681266176 + m 1 * 384000 + m 3 * 1220296704000 + m 5 * 1426065438336000 + m 7 *
    40247250988492800 + m 9 * 82078062837120000 + m 11 * 3868633431398400
 | 6 => m 2 * 59327778816 + m 4 * 5655456710529024 + m 6 * 2954556346926514176 + m 8 * 68162255408378621952 + m 10 *
    149904569170426785792 + m 12 * 13060880984244473856 + m 14 * 32655693528170496 - m 1 * 1536000 - m 3 *
    45779970048000 - m 5 * 207596934994944000 - m 7 * 19223546587116748800 - m 9 * 146681247534132326400 - m 11 *
    66440962746267648000 - m 13 * 1108134583213056000
 | 7 => -(m 2 * 949705261056) - m 4 * 393850635087200256 - m 6 * 642465455376955392000 - m 8 * 41364666990389549334528 -
    m 10 * 284506663217594719469568 - m 12 * 161669201764763831943168 - m 14 * 5129286055227337457664 - m 16 *
    6400515931521417216 + m 1 * 6144000 + m 3 * 1677738393600000 + m 5 * 25749555468908544000 + m 7 *
    7224480138508067635200 + m 9 * 137554487820425195520000 + m 11 * 309817988659796589772800 + m 13 *
    41051848150439712768000 + m 15 * 298833612130185216000
 | 8 => m 2 * 15197127376896 + m 4 * 26378543021115899904 + m 6 * 120043336861086485446656 + m 8 *
    20297169673990826972479488 + m 10 * 322521000708045339294302208 + m 12 * 721556613733247083497259008 + m 14 *
    129378838650155882320232448 + m 16 * 1817568319711191468933120 + m 18 * 1254501122578197774336 - m 3 *
    60873417129984000 - m 5 * 2925747067794948096000 - m 7 * 2202595177708554957619200 - m 9 *
    103465169513987239319961600 - m 11 * 640231263239897869123584000 - m 13 * 422873363057897494020096000 - m 15 *
    21088866496661588803584000 - m 17 * 77132884178928412262400 - m 1 * 24576000
 | _ => 0

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k=radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem pairLinear_pow_0 (q : ℝ) :
 pairLinear (fun n => q^n) 0=(thetaPairRadialEvenPolynomial (144*q^2) 0).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_0_0,radialCoeffs_0_1,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_1 (q : ℝ) :
 pairLinear (fun n => q^n) 1=(thetaPairRadialEvenPolynomial (144*q^2) 1).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_2 (q : ℝ) :
 pairLinear (fun n => q^n) 2=(thetaPairRadialEvenPolynomial (144*q^2) 2).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_3 (q : ℝ) :
 pairLinear (fun n => q^n) 3=(thetaPairRadialEvenPolynomial (144*q^2) 3).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_4 (q : ℝ) :
 pairLinear (fun n => q^n) 4=(thetaPairRadialEvenPolynomial (144*q^2) 4).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_5 (q : ℝ) :
 pairLinear (fun n => q^n) 5=(thetaPairRadialEvenPolynomial (144*q^2) 5).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_6 (q : ℝ) :
 pairLinear (fun n => q^n) 6=(thetaPairRadialEvenPolynomial (144*q^2) 6).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_7 (q : ℝ) :
 pairLinear (fun n => q^n) 7=(thetaPairRadialEvenPolynomial (144*q^2) 7).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem pairLinear_pow_8 (q : ℝ) :
 pairLinear (fun n => q^n) 8=(thetaPairRadialEvenPolynomial (144*q^2) 8).eval (25*q) := by
 norm_num only [pairLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

/-- Each retained linear functional is the exact reflected pair polynomial. -/
theorem pairLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => q^n) k=(thetaPairRadialEvenPolynomial (144*q^2) k).eval (25*q) := by
 interval_cases k
 · exact pairLinear_pow_0 q
 · exact pairLinear_pow_1 q
 · exact pairLinear_pow_2 q
 · exact pairLinear_pow_3 q
 · exact pairLinear_pow_4 q
 · exact pairLinear_pow_5 q
 · exact pairLinear_pow_6 q
 · exact pairLinear_pow_7 q
 · exact pairLinear_pow_8 q

/-- Scalar radial weights pass through every pair moment. -/
theorem pairLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun n => c*m n) k=c*pairLinear m k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- Convex gamma interpolation is exact for the signed pair moments. -/
theorem pairLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 pairLinear (fun j => (1-t)*m j+t*n j) k=
  (1-t)*pairLinear m k+t*pairLinear n k := by
 interval_cases k <;> simp only [pairLinear] <;> ring

/-- The pair moment depends only on the nineteen retained power moments. -/
theorem pairLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 pairLinear m k=∑ j ∈ Finset.range 19,
  pairLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [pairLinear,Finset.sum_range_succ] <;> ring

end p34

end GaloisForLFunctions.ThetaCuspSections.FifthOtherTail
