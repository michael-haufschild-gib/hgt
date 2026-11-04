import GaloisForLFunctions.ThetaCuspSections.FifthEvenInheritedLoadBoundary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamCurvatureMoments

/-!
# The fifth even theta source forces a positive fifth load at the origin

The principal minor on indices zero, one, two, and four is strictly negative
at the modular seam. Its Schur coordinate gives the sharp positive fifth-load
threshold for a full origin repair. Together with the scale-seven capacity gap,
this excludes every real pair of constant diagonal loads, including the actual
weighted representative at each critical aperture.

Two coupled loads have a positive three-dimensional common kernel at the
origin; the four-dimensional kernel of the last-pair load alone is indefinite.
-/

noncomputable section
open RHTower RHTower.ThetaOddSeamCurvature
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveOrigin
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

private def source16 {K : Type*} [Field K] (a : K) : K :=
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

private def source14 {K : Type*} [Field K] (a : K) : K :=
  let s := 3-3*a/4
  let w := 2+a/2
  2*s^2*q20 a+2*s*w*q11 a+2*w^2*q02 a-2*a*w*q00A a-s/6*q00 a
private theorem source14_eq (X : ℝ) : HTGeometry.ThetaSeamFourteen.sourceFourteen X = source14 X := rfl
private theorem source16_eq (X : ℝ) : HTGeometry.ThetaSeamSixteen.sourceSixteen X = source16 X := rfl

/-- Complete signed seam moments, with the sixteenth source derivative retained. -/
private def mom (n : ℕ) (X : ℝ) : ℝ := M n X
private def cof (X : ℝ) : ℝ :=
  let a := mom 0 X
  let b := mom 1 X
  let c := mom 2 X
  let d := mom 3 X
  let e := mom 4 X
  let u := mom 4 X
  let v := mom 5 X
  let w := mom 6 X
  (a*c*e+2*b*c*d-a*d^2-c^3-b^2*e)*mom 8 X -
    ((c*e-d^2)*u^2+2*(c*d-b*e)*u*v+2*(b*d-c^2)*u*w+
      (a*e-c^2)*v^2+2*(b*c-a*d)*v*w+(a*c-b^2)*w^2)

/-- On the modular parameter band, the skipped principal determinant is strictly negative. -/
private theorem skipped_polynomial_negative {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) : cof X < 0 := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  unfold cof mom
  norm_num [M, P, Finset.sum_range_succ, Nat.choose, source14_eq, source16_eq,
    source14, source16, HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, hp 21, hp 22]
private def vector : Fin 5 → ℝ := ![-658560,47040,-420,1,-(1/1568)]
private def originEnergy (X : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, vector i*vector j*M (i.val+j.val) X

private def linearEnergy (X : ℝ) : ℝ :=
  658560^2*M 0 X - 2*658560*47040*M 1 X +
  (47040^2+2*658560*420)*M 2 X -
  (2*658560+2*47040*420)*M 3 X +
  (420^2+2*47040+2*658560/1568)*M 4 X -
  (2*420+2*47040/1568)*M 5 X +
  (1+2*420/1568)*M 6 X - 2/1568*M 7 X + 1/1568^2*M 8 X

private theorem originEnergy_eq (X : ℝ) : originEnergy X = linearEnergy X := by
  norm_num [originEnergy,vector,Fin.sum_univ_succ,linearEnergy,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  ring

private theorem originEnergy_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) :
    0 < originEnergy X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  rw [originEnergy_eq,hX]
  norm_num [linearEnergy,M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring_nf
  positivity

private theorem native_eight :
    thetaCuspNativeReflectionJet 16 0 = thetaCuspSelfDualThetaMass^2 *
      M 8 (thetaCuspSelfDualModularScale^2) := by
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=11) (by norm_num : Odd 11)
  have h13 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=13) (by norm_num : Odd 13)
  have h15 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=15) (by norm_num : Odd 15)
  have h0 := source_even (0:Fin 9)
  have h2 := source_even (1:Fin 9)
  have h4 := source_even (2:Fin 9)
  have h6 := source_even (3:Fin 9)
  have h8 := source_even (4:Fin 9)
  have h10 := source_even (5:Fin 9)
  have h12 := source_even (6:Fin 9)
  have h14 := source_even (7:Fin 9)
  have h16 := source_even (8:Fin 9)
  norm_num at h0 h2 h4 h6 h8 h10 h12 h14 h16
  norm_num [thetaCuspNativeReflectionJet_eq,M,Finset.sum_range_succ,Nat.choose,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]
  ring

private theorem native_all (k : Fin 9) :
    (-1:ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) 0 =
      thetaCuspSelfDualThetaMass^2*M k.val (thetaCuspSelfDualModularScale^2) := by
  have h0 : thetaCuspNativeReflectionJet 0 0 =
      thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    have h := source_even (0 : Fin 9)
    norm_num at h
    norm_num [thetaCuspNativeReflectionJet_eq, M, Finset.sum_range_succ, h]
    ring
  have h1 := native_value (0:Fin 7)
  have h2 := native_value (1:Fin 7)
  have h3 := native_value (2:Fin 7)
  have h4 := native_value (3:Fin 7)
  have h5 := native_value (4:Fin 7)
  have h6 := native_value (5:Fin 7)
  have h7 := native_value (6:Fin 7)
  norm_num at h1 h2 h3 h4 h5 h6 h7
  fin_cases k <;> norm_num [h0,h1,h2,h3,h4,h5,h6,h7,native_eight]

private theorem sourceEnergy_zero_eq :
    EvenFiveBoundary.sourceEnergy 0 = thetaCuspSelfDualThetaMass^2 *
      originEnergy (thetaCuspSelfDualModularScale^2) := by
  unfold EvenFiveBoundary.sourceEnergy originEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h := native_all ⟨i.val+j.val, by omega⟩
  dsimp only at h
  rw [h]
  change vector i*(thetaCuspSelfDualThetaMass^2 *
      M (i.val+j.val) (thetaCuspSelfDualModularScale^2))*vector j = _
  ring

/-- The scale-seven direction also has strictly positive complete-source energy at the origin. -/
theorem boundary_direction_positive_at_origin : 0 < EvenFiveBoundary.sourceEnergy 0 := by
  rw [sourceEnergy_zero_eq]
  have hM : 0 < thetaCuspSelfDualThetaMass := by
    have h := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith only [h]
  exact mul_pos (pow_pos hM 2) (originEnergy_positive
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le)


open Matrix
private theorem symmetric_four_det (a b c d e u v w t : ℝ) :
    (!![a,b,c,u; b,c,d,v; c,d,e,w; u,v,w,t] : Matrix (Fin 4) (Fin 4) ℝ).det =
      (a*c*e+2*b*c*d-a*d^2-c^3-b^2*e)*t -
        ((c*e-d^2)*u^2+2*(c*d-b*e)*u*v+2*(b*d-c^2)*u*w+
          (a*e-c^2)*v^2+2*(b*c-a*d)*v*w+(a*c-b^2)*w^2) := by
  have hcast : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    hcast, Fin.lt_def, Fin.le_def, Fin.isValue, -Fin.val_fin_lt, -Fin.val_fin_le, -Fin.val_pos_iff]
  ring


open Matrix Filter Topology RHTower.ThetaCuspGaussianLimit
open GaloisForLFunctions.HTGeometry

private def skipIndex : Fin 4 → Fin 5 := ![0,1,2,4]
private def skipped (D : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (evenFiveRepair 0 D 0).submatrix skipIndex skipIndex
private def A : Matrix (Fin 3) (Fin 3) ℝ := thetaCuspNativeEvenHead 0
private def b : Matrix (Fin 3) (Fin 1) ℝ := fun i _ =>
  (-1 : ℝ)^(i.val+4)*thetaCuspNativeReflectionJet (2*(i.val+4)) 0
private def gamma : ℝ := thetaCuspNativeReflectionJet 16 0 - (bᴴ*A⁻¹*b) 0 0
private def G : ℝ := 3*thetaCuspFullSource 0^2

private theorem G_pos : 0 < G := by
  unfold G
  exact mul_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))

private theorem skipped_independent (C D : ℝ) :
    (evenFiveRepair C D 0).submatrix skipIndex skipIndex = skipped D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [evenFiveRepair, skipped, skipIndex, Matrix.diagonal]

private theorem skipped_block (D : ℝ) :
    (skipped D).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks A b bᴴ (fun _ _ : Fin 1 => thetaCuspNativeReflectionJet 16 0 + D*G) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [skipped, skipIndex, evenFiveRepair, nativeShiftedMatrix, A, b, G,
      thetaCuspNativeEvenHead, finiteHankelMatrix, thetaCuspCenterCompensationSource,
      Matrix.diagonal, finSumFinEquiv, Fin.natAdd, Fin.castAdd, Fin.castLE, Fin.ext_iff]

private theorem skipped_det (D : ℝ) :
    (skipped D).det = A.det*(gamma+D*G) := by
  have hA : A.PosDef := thetaCuspNativeEvenHead_zero_posDef
  letI : Invertible A := hA.isUnit.invertible
  have he := congrArg Matrix.det (skipped_block D)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one] at he
  rw [he]
  unfold gamma
  simp only [Matrix.sub_apply]
  ring

private theorem skipped_native_polynomial :
    (skipped 0).det = thetaCuspSelfDualThetaMass^8*cof (thetaCuspSelfDualModularScale^2) := by
  have hm (k : Fin 7) := RHTower.ThetaOddSeamCurvature.native_value k
  have h0 : thetaCuspNativeReflectionJet 0 0 =
      thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    have h := source_even (0 : Fin 9)
    norm_num at h
    norm_num [thetaCuspNativeReflectionJet_eq, M, Finset.sum_range_succ, h]
    ring
  have h1 := hm 0
  have h2 := hm 1
  have h3 := hm 2
  have h4 := hm 3
  have h5 := hm 4
  have h6 := hm 5
  norm_num at h1 h2 h3 h4 h5 h6
  have he : skipped 0 = !![
      thetaCuspNativeReflectionJet 0 0,-thetaCuspNativeReflectionJet 2 0,
        thetaCuspNativeReflectionJet 4 0,thetaCuspNativeReflectionJet 8 0;
      -thetaCuspNativeReflectionJet 2 0,thetaCuspNativeReflectionJet 4 0,
        -thetaCuspNativeReflectionJet 6 0,-thetaCuspNativeReflectionJet 10 0;
      thetaCuspNativeReflectionJet 4 0,-thetaCuspNativeReflectionJet 6 0,
        thetaCuspNativeReflectionJet 8 0,thetaCuspNativeReflectionJet 12 0;
      thetaCuspNativeReflectionJet 8 0,-thetaCuspNativeReflectionJet 10 0,
        thetaCuspNativeReflectionJet 12 0,thetaCuspNativeReflectionJet 16 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [skipped, skipIndex, evenFiveRepair, nativeShiftedMatrix, Matrix.diagonal]
  rw [he, symmetric_four_det, h0, h1, h2, h3, h4, h5, h6, native_eight]
  unfold cof mom
  ring

private theorem gamma_neg : gamma < 0 := by
  have hM : 0 < thetaCuspSelfDualThetaMass := by
    have h := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith only [h]
  have hp := skipped_polynomial_negative
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
  have hn : (skipped 0).det < 0 := by
    rw [skipped_native_polynomial]
    exact mul_neg_of_pos_of_neg (pow_pos hM 8) hp
  rw [skipped_det] at hn
  simp only [zero_mul, add_zero] at hn
  by_contra hgamma
  have hp := mul_nonneg thetaCuspNativeEvenHead_zero_posDef.det_pos.le (le_of_not_gt hgamma)
  exact (not_lt_of_ge hp) hn

/-- Sharp fifth-diagonal threshold at the origin, independent of the fourth load. -/
def originFifthThreshold : ℝ := -gamma/G

/-- The skipped origin minor forces a strictly positive fifth load. -/
theorem originFifthThreshold_pos : 0 < originFifthThreshold :=
  div_pos (neg_pos.mpr gamma_neg) G_pos

private theorem threshold_le_of_skipped (D : ℝ) (h : (skipped D).PosSemidef) :
    originFifthThreshold ≤ D := by
  have hd := h.det_nonneg
  rw [skipped_det] at hd
  have hs := (mul_nonneg_iff_of_pos_left thetaCuspNativeEvenHead_zero_posDef.det_pos).mp hd
  rw [originFifthThreshold, div_le_iff₀ G_pos]
  linarith only [hs]

/-- Every positive semidefinite full origin block lies above the positive fifth-load threshold. -/
theorem origin_fifth_load_required (C D : ℝ) (h : (evenFiveRepair C D 0).PosSemidef) :
    originFifthThreshold ≤ D := by
  have hs := h.submatrix skipIndex
  rw [skipped_independent] at hs
  exact threshold_le_of_skipped D hs

/-- The origin and scale-seven source matrices cannot both be positive semidefinite,
for any real pair of constant diagonal loads. -/
theorem constant_source_repair_fails (C D : ℝ) :
    ¬ ((evenFiveRepair C D 0).PosSemidef ∧
      (evenFiveRepair C D EvenFiveBoundary.witnessCenter).PosSemidef) := by
  intro h
  have hD := originFifthThreshold_pos.trans_le (origin_fifth_load_required C D h.1)
  exact EvenFiveBoundary.constant_source_repair_fails C hD.le h


private theorem skipped_posSemidef_of_gap (D : ℝ) (hs : 0 ≤ gamma+D*G) :
    (skipped D).PosSemidef := by
  let T : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => thetaCuspNativeReflectionJet 16 0+D*G
  have hA : A.PosDef := thetaCuspNativeEvenHead_zero_posDef
  letI : Invertible A := hA.isUnit.invertible
  have hS : (T-bᴴ*A⁻¹*b).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i
      fin_cases j
      simp
    · intro v
      have he : (T-bᴴ*A⁻¹*b) 0 0 = gamma+D*G := by
        dsimp only [T, gamma, Matrix.sub_apply]
        ring
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one, he]
      nlinarith only [mul_nonneg hs (sq_nonneg (v 0))]
  have hb : (fromBlocks A b bᴴ T).PosSemidef := (Matrix.PosDef.fromBlocks₁₁ b T hA).mpr hS
  rw [← skipped_block D] at hb
  have h := hb.submatrix ((finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm)
  simpa using h

private theorem skipped_posDef (D : ℝ) (hD : originFifthThreshold < D) :
    (skipped D).PosDef := by
  have hs : 0 < gamma+D*G := by
    have h := (div_lt_iff₀ G_pos).mp hD
    linarith only [h]
  have h := skipped_posSemidef_of_gap D hs.le
  apply h.posDef_iff_det_ne_zero.mpr
  rw [skipped_det]
  exact (mul_pos thetaCuspNativeEvenHead_zero_posDef.det_pos hs).ne'

private theorem skipIndex_injective : Function.Injective skipIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [skipIndex, Fin.ext_iff]

private def originOrder : Fin 4 ⊕ Fin 1 ≃ Fin 5 :=
  finSumFinEquiv.trans (Equiv.swap 3 4)
private def c : Matrix (Fin 4) (Fin 1) ℝ := fun i _ =>
  (-1 : ℝ)^((skipIndex i).val+3)*thetaCuspNativeReflectionJet (2*((skipIndex i).val+3)) 0
private def originSchur (D : ℝ) : ℝ :=
  thetaCuspNativeReflectionJet 12 0 - (cᴴ*(skipped D)⁻¹*c) 0 0

private theorem full_origin_block (C D : ℝ) :
    (evenFiveRepair C D 0).submatrix originOrder originOrder =
      fromBlocks (skipped D) c cᴴ
        (fun _ _ : Fin 1 => thetaCuspNativeReflectionJet 12 0+C*G) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [originOrder, Equiv.swap_apply_def, skipped, skipIndex, evenFiveRepair,
      nativeShiftedMatrix, c, G, thetaCuspCenterCompensationSource, Matrix.diagonal,
      finSumFinEquiv, Fin.natAdd, Fin.castAdd, Fin.castLE, Fin.ext_iff]

private theorem full_origin_posDef (C D : ℝ) (hD : originFifthThreshold < D)
    (hs : 0 < originSchur D+C*G) : (evenFiveRepair C D 0).PosDef := by
  let T : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => thetaCuspNativeReflectionJet 12 0+C*G
  have hA := skipped_posDef D hD
  letI : Invertible (skipped D) := hA.isUnit.invertible
  have he : (T-cᴴ*(skipped D)⁻¹*c) 0 0 = originSchur D+C*G := by
    dsimp only [T, originSchur, Matrix.sub_apply]
    ring
  have hS : (T-cᴴ*(skipped D)⁻¹*c).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i
      fin_cases j
      simp
    · intro v
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one, he]
      nlinarith only [mul_nonneg hs.le (sq_nonneg (v 0))]
  have hb : (fromBlocks (skipped D) c cᴴ T).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ c T hA).mpr hS
  have hd : (fromBlocks (skipped D) c cᴴ T).det ≠ 0 := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one, he]
    exact mul_ne_zero hA.det_pos.ne' hs.ne'
  have hp := hb.posDef_iff_det_ne_zero.mpr hd
  rw [← full_origin_block C D] at hp
  have h := hp.submatrix originOrder.symm.injective
  simpa using h

/-- The remaining fourth-load threshold after admitting a fifth load at the origin. -/
def originFourthThreshold (D : ℝ) : ℝ := -originSchur D/G

private theorem full_origin_det (C D : ℝ) (hD : originFifthThreshold < D) :
    (evenFiveRepair C D 0).det = (skipped D).det*(originSchur D+C*G) := by
  have hA := skipped_posDef D hD
  letI : Invertible (skipped D) := hA.isUnit.invertible
  have he := congrArg Matrix.det (full_origin_block C D)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one] at he
  rw [he]
  unfold originSchur
  simp only [Matrix.sub_apply]
  ring

/-- Exact positivity region of the full fifth origin matrix in the two load coordinates. -/
theorem origin_posDef_iff (C D : ℝ) :
    (evenFiveRepair C D 0).PosDef ↔
      originFifthThreshold < D ∧ originFourthThreshold D < C := by
  constructor
  · intro h
    have hs := h.submatrix skipIndex_injective
    rw [skipped_independent] at hs
    have hd := hs.det_pos
    rw [skipped_det] at hd
    have hg := (mul_pos_iff_of_pos_left thetaCuspNativeEvenHead_zero_posDef.det_pos).mp hd
    have hD : originFifthThreshold < D := by
      rw [originFifthThreshold, div_lt_iff₀ G_pos]
      linarith only [hg]
    refine ⟨hD,?_⟩
    have hf := h.det_pos
    rw [full_origin_det C D hD] at hf
    have hgap := (mul_pos_iff_of_pos_left hs.det_pos).mp hf
    rw [originFourthThreshold, div_lt_iff₀ G_pos]
    linarith only [hgap]
  · rintro ⟨hD,hC⟩
    apply full_origin_posDef C D hD
    have h := (div_lt_iff₀ G_pos).mp hC
    linarith only [h]

/-- A fifth load admits a strictly positive full origin repair exactly above its sharp threshold.
The repairing fourth load can always be chosen strictly positive. -/
theorem exists_positive_origin_repair_iff (D : ℝ) :
    (∃ C : ℝ, 0 < C ∧ (evenFiveRepair C D 0).PosDef) ↔ originFifthThreshold < D := by
  constructor
  · rintro ⟨C,_,h⟩
    have hs := h.submatrix skipIndex_injective
    rw [skipped_independent] at hs
    have hd := hs.det_pos
    rw [skipped_det] at hd
    have hg := (mul_pos_iff_of_pos_left thetaCuspNativeEvenHead_zero_posDef.det_pos).mp hd
    rw [originFifthThreshold, div_lt_iff₀ G_pos]
    linarith only [hg]
  · intro hD
    let C := (|originSchur D|+thetaCuspFullSource 0^2)/G
    have hF := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
    have hC : 0 < C := div_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) hF) G_pos
    refine ⟨C,hC,full_origin_posDef C D hD ?_⟩
    have he : C*G = |originSchur D|+thetaCuspFullSource 0^2 := by
      dsimp only [C]
      exact div_mul_cancel₀ _ G_pos.ne'
    rw [he]
    linarith only [neg_le_abs (originSchur D), hF]


private theorem aperture_slack_linear {t : ℝ} (ht : 0 < t) :
    t*Real.cosh t-Real.sinh t < t*Real.sinh t := by
  have hs := Real.sinh_pos_iff.mpr ht
  have h := RHTower.rcoth_lt_one_add_inv ht
  unfold RHTower.rcoth at h
  have hm := mul_lt_mul_of_pos_left ((div_lt_iff₀ hs).mp h) ht
  have he : t*((1+1/t)*Real.sinh t) = t*Real.sinh t+Real.sinh t := by
    field_simp [ht.ne']
  rw [he] at hm
  linarith only [hm]

private theorem flux_slack_bounds {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 ≤ deriv (thetaCuspCenterCompensationFlux a) r -
      (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2) ∧
    deriv (thetaCuspCenterCompensationFlux a) r -
      (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2) ≤
      (r*Real.sinh (a*r))*(a*r)*thetaCuspFullSource (r/2)^2 := by
  have ht := mul_pos ha hr
  have h0 := sub_nonneg.mpr (RHTower.sinh_lt_mul_cosh ht).le
  have hU := (aperture_slack_linear ht).le
  have hF : 0 ≤ r*thetaCuspFullSource (r/2)^2 := mul_nonneg hr.le (sq_nonneg _)
  have h0' := mul_nonneg hF h0
  have hU' := mul_le_mul_of_nonneg_left hU hF
  rw [deriv_thetaCuspCenterCompensationFlux_eq_source_add_slack]
  constructor <;> nlinarith only [h0',hU']

private theorem diagonal_energy (C D : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (Matrix.diagonal (fun i : Fin 5 =>
      if i.val = 3 then C else if i.val = 4 then D else 0) *ᵥ v) =
      C*(v 3)^2+D*(v 4)^2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  have h3 : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
  have h4 : Fin.succ (Fin.succ (2 : Fin 3)) = (4 : Fin 5) := rfl
  norm_num [Fin.sum_univ_succ, h3, h4]
  ring

private theorem weighted_energy (a C D r : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (centerEvenFiveRepair a C D r *ᵥ v) =
      (r*Real.sinh (a*r))*(v ⬝ᵥ (evenFiveRepair C D (r/2) *ᵥ v)) +
      C*(deriv (thetaCuspCenterCompensationFlux a) r -
        (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))*(v 3)^2 +
      D*(deriv (thetaCuspCenterCompensationFlux a) r -
        (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))*(v 4)^2 := by
  have he : centerEvenFiveRepair a C D r =
      (r*Real.sinh (a*r)) • evenFiveRepair C D (r/2) +
      Matrix.diagonal (fun i : Fin 5 => if i.val = 3 then
        C*(deriv (thetaCuspCenterCompensationFlux a) r -
          (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))
        else if i.val = 4 then
        D*(deriv (thetaCuspCenterCompensationFlux a) r -
          (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2)) else 0) := by
    ext i j
    simp only [centerEvenFiveRepair, evenFiveRepair, nativeShiftedMatrix,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [he, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, diagonal_energy]
  ring

private def upperForm (a C D r : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v ⬝ᵥ (evenFiveRepair C D (r/2) *ᵥ v) +
    (a*r)*thetaCuspFullSource (r/2)^2*(|C| * (v 3)^2+|D| * (v 4)^2)

private theorem weighted_le_upper {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (C D : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (centerEvenFiveRepair a C D r *ᵥ v) ≤
      (r*Real.sinh (a*r))*upperForm a C D r v := by
  obtain ⟨h0,hU⟩ := flux_slack_bounds ha hr
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) h0
  have hCU := mul_le_mul_of_nonneg_left hU (abs_nonneg C)
  have hC' := mul_le_mul_of_nonneg_right (hC.trans hCU) (sq_nonneg (v 3))
  have hD := mul_le_mul_of_nonneg_right (le_abs_self D) h0
  have hDU := mul_le_mul_of_nonneg_left hU (abs_nonneg D)
  have hD' := mul_le_mul_of_nonneg_right (hD.trans hDU) (sq_nonneg (v 4))
  rw [weighted_energy]
  unfold upperForm
  nlinarith only [hC',hD']

private theorem repair_continuous (C D : ℝ) : Continuous (evenFiveRepair C D) := by
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold evenFiveRepair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private theorem upperForm_continuous (a C D : ℝ) (v : Fin 5 → ℝ) :
    Continuous (fun r : ℝ => upperForm a C D r v) := by
  have hM := repair_continuous C D
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  unfold upperForm
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The weighted slack divided by its positive weight vanishes at the origin.
A continuous upper quadratic form transfers global weighted positivity to the full native origin. -/
private theorem origin_of_weighted_positive {a C D : ℝ} (ha : 0 < a)
    (h : ∀ r : ℝ, 0 < r → (centerEvenFiveRepair a C D r).PosSemidef) :
    (evenFiveRepair C D 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · unfold evenFiveRepair
    apply Matrix.IsHermitian.add
    · rw [Matrix.IsHermitian]
      ext i j
      simp [nativeShiftedMatrix, add_comm]
    · exact Matrix.isHermitian_diagonal _
  · intro v
    simp only [star_trivial]
    have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ upperForm a C D r v := by
      have hh := (h r hr).dotProduct_mulVec_nonneg v
      simp only [star_trivial] at hh
      have hu := hh.trans (weighted_le_upper ha hr C D v)
      have hw : 0 < r*Real.sinh (a*r) :=
        mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
      by_contra hn
      exact (not_lt_of_ge hu) (mul_neg_of_pos_of_neg hw (lt_of_not_ge hn))
    have ht : Tendsto (fun r : ℝ => upperForm a C D r v) (𝓝[>] 0)
        (𝓝 (v ⬝ᵥ (evenFiveRepair C D 0 *ᵥ v))) := by
      have hc := (upperForm_continuous a C D v).tendsto 0
      simpa only [upperForm, zero_div, mul_zero, zero_mul, add_zero] using
        hc.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hnonneg r hr

/-- No real pair of constant diagonal loads gives a globally positive weighted representative
at any critical aperture. -/
theorem constant_weighted_repair_fails {a : ℝ} (ha : 0 < a) (haU : a < 1/2) (C D : ℝ) :
    ¬ ∀ r : ℝ, 0 < r → (centerEvenFiveRepair a C D r).PosSemidef := by
  intro h
  have h0 := origin_of_weighted_positive ha h
  have hD := originFifthThreshold_pos.trans_le (origin_fifth_load_required C D h0)
  exact EvenFiveBoundary.constant_weighted_repair_fails ha haU hD.le C h

private theorem moment_0 (X : ℝ) : M 0 X =
    9 / 64 + X * (-3 / 64) + X ^ 2 * (1 / 256) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_1 (X : ℝ) : M 1 X =
    45 / 64 + X * (-165 / 256) + X ^ 2 * (21 / 256) + X ^ 3 * (1 / 1024) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_2 (X : ℝ) : M 2 X =
    765 / 64 + X * (-2505 / 128) + X ^ 2 * (4461 / 1024) + X ^ 3 * (77 / 1024) + X ^ 4 * (27 / 4096) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_3 (X : ℝ) : M 3 X =
    24345 / 64 + X * (-243615 / 256) + X ^ 2 * (333759 / 1024) + X ^ 3 * (31519 / 4096) + X ^ 4 *
    (8199 / 4096) + X ^ 5 * (-21 / 16384) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_4 (X : ℝ) : M 4 X =
    1207665 / 64 + X * (-2122095 / 32) + X ^ 2 * (16407993 / 512) + X ^ 3 * (1024127 / 1024) + X ^ 4
    * (7963857 / 16384) + X ^ 5 * (-30027 / 16384) + X ^ 6 * (5133 / 65536) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_5 (X : ℝ) : M 5 X =
    85066245 / 64 + X * (-1591823865 / 256) + X ^ 2 * (2049802467 / 512) + X ^ 3 * (327670217 /
    2048) + X ^ 4 * (1966854177 / 16384) + X ^ 5 * (-62366877 / 65536) + X ^ 6 * (3218985 / 65536) +
    X ^ 7 * (-725859 / 262144) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_6 (X : ℝ) : M 6 X =
    8028542565 / 64 + X * (-96262740255 / 128) + X ^ 2 * (634560122211 / 1024) + X ^ 3 * (1975395347
    / 64) + X ^ 4 * (529421297031 / 16384) + X ^ 5 * (-13501200603 / 32768) + X ^ 6 * (6251467509 /
    262144) + X ^ 7 * (-888527835 / 262144) + X ^ 8 * (-10466793 / 1048576) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_7 (X : ℝ) : M 7 X =
    975220892145 / 64 + X * (-29124679352115 / 256) + X ^ 2 * (119242543472409 / 1024) + X ^ 3 *
    (28953599674549 / 4096) + X ^ 4 * (159032056610583 / 16384) + X ^ 5 * (-11525159347845 / 65536)
    + X ^ 6 * (2939734839795 / 262144) + X ^ 7 * (-3025910283417 / 1048576) + X ^ 8 * (-16707449205
    / 1048576) + X ^ 9 * (-202414761 / 4194304) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private theorem moment_8 (X : ℝ) : M 8 X =
    147972940725465 / 64 + X * (-1345440989479065 / 64) + X ^ 2 * (1671683363523321 / 64) + X ^ 3 *
    (971257441098301 / 512) + X ^ 4 * (26851592045541915 / 8192) + X ^ 5 * (-321887823511059 / 4096)
    + X ^ 6 * (359400635300889 / 65536) + X ^ 7 * (-288451649154465 / 131072) + X ^ 8 *
    (-73300953671271 / 4194304) + X ^ 9 * (-684133624179 / 4194304) + X ^ 10 * (139969720953 /
    16777216) := by
  norm_num [M,P,Finset.sum_range_succ,Nat.choose,
    source14_eq,source16_eq,source14,source16,HTGeometry.modularThetaEvenSeamSourcePolynomial,
    q00,q00A,q00AA,q20,q20A,q11,q11A,q02,q02A,q40,q31,q22,q13,q04]
  ring

private def coupledCof (X : ℝ) : ℝ :=
  let a := M 0 X
  let b := M 1 X
  let c := M 2 X
  let d := M 3 X
  let e := M 4 X
  let u := M 3 X - M 4 X/1568
  let v := M 4 X - M 5 X/1568
  let w := M 5 X - M 6 X/1568
  (a*c*e+2*b*c*d-a*d^2-c^3-b^2*e)*
      (M 6 X-2*M 7 X/1568+M 8 X/1568^2) -
    ((c*e-d^2)*u^2+2*(c*d-b*e)*u*v+2*(b*d-c^2)*u*w+
      (a*e-c^2)*v^2+2*(b*c-a*d)*v*w+(a*c-b^2)*w^2)
private theorem coupledCof_negative {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    coupledCof X < 0 := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [coupledCof,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6,moment_7,moment_8]
  ring_nf
  linarith only [pow_nonneg hz 1,pow_nonneg hz 2,pow_nonneg hz 3,pow_nonneg hz 4,
    pow_nonneg hz 5,pow_nonneg hz 6,pow_nonneg hz 7,pow_nonneg hz 8,pow_nonneg hz 9,
    pow_nonneg hz 10,pow_nonneg hz 11,pow_nonneg hz 12,pow_nonneg hz 13,pow_nonneg hz 14,
    pow_nonneg hz 15,pow_nonneg hz 16,pow_nonneg hz 17,pow_nonneg hz 18,
    pow_nonneg hz 19,pow_nonneg hz 20,pow_nonneg hz 21,pow_nonneg hz 22,
    hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,hp 8,hp 9,hp 10,hp 11,hp 12,hp 13,hp 14,
    hp 15,hp 16,hp 17,hp 18,hp 19,hp 20,hp 21,hp 22]


private def headTwoCof (X : ℝ) : ℝ :=
  let a := M 0 X
  let b := M 1 X
  let c := M 2 X
  let u := -420*M 2 X+M 3 X-M 4 X/1568
  let v := -420*M 3 X+M 4 X-M 5 X/1568
  let t := 176400*M 4 X-840*M 5 X+(1+840/1568)*M 6 X-
    2*M 7 X/1568+M 8 X/1568^2
  (a*c-b^2)*t-(c*u^2-2*b*u*v+a*v^2)

private theorem headTwoCof_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < headTwoCof X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [headTwoCof,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6,moment_7,moment_8]
  ring_nf
  linarith only [pow_nonneg hz 1,pow_nonneg hz 2,pow_nonneg hz 3,pow_nonneg hz 4,
    pow_nonneg hz 5,pow_nonneg hz 6,pow_nonneg hz 7,pow_nonneg hz 8,pow_nonneg hz 9,
    pow_nonneg hz 10,pow_nonneg hz 11,pow_nonneg hz 12,pow_nonneg hz 13,pow_nonneg hz 14,
    pow_nonneg hz 15,pow_nonneg hz 16,pow_nonneg hz 17,pow_nonneg hz 18,
    pow_nonneg hz 19,pow_nonneg hz 20,pow_nonneg hz 21,pow_nonneg hz 22,
    hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,hp 8,hp 9,hp 10,hp 11,hp 12,hp 13,hp 14,
    hp 15,hp 16,hp 17,hp 18,hp 19,hp 20,hp 21,hp 22]



/-- Coordinates for the common kernel of the two coupled source loads. -/
def coherentKernelBasis : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1,0,0; 0,1,0; 0,0,-420; 0,0,1; 0,0,-1/1568]

/-- The native form restricted to the common kernel of the coupled loads. -/
def coherentKernel (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coherentKernelBasisᴴ * nativeShiftedMatrix 5 0 x * coherentKernelBasis

/-- Kernel coordinates for the single load on the last two entries. -/
def singleCoherentKernelBasis : Matrix (Fin 5) (Fin 4) ℝ :=
  !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1; 0,0,0,-1/1568]

/-- The larger kernel left unchanged by a single coupled load. -/
def singleCoherentKernel (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  singleCoherentKernelBasisᴴ * nativeShiftedMatrix 5 0 x * singleCoherentKernelBasis

private theorem native_hankel_zero (i j : Fin 5) :
    nativeShiftedMatrix 5 0 0 i j = thetaCuspSelfDualThetaMass^2 *
      M (i.val+j.val) (thetaCuspSelfDualModularScale^2) := by
  simpa only [nativeShiftedMatrix, Nat.add_zero] using
    native_all ⟨i.val+j.val, by omega⟩

private def kernelMoments (X : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let u := -420*M 2 X+M 3 X-M 4 X/1568
  let v := -420*M 3 X+M 4 X-M 5 X/1568
  let t := 176400*M 4 X-840*M 5 X+(1+840/1568)*M 6 X-
    2*M 7 X/1568+M 8 X/1568^2
  !![M 0 X,M 1 X,u; M 1 X,M 2 X,v; u,v,t]

private def singleKernelMoments (X : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let u := M 3 X-M 4 X/1568
  let v := M 4 X-M 5 X/1568
  let w := M 5 X-M 6 X/1568
  let t := M 6 X-2*M 7 X/1568+M 8 X/1568^2
  !![M 0 X,M 1 X,M 2 X,u; M 1 X,M 2 X,M 3 X,v;
    M 2 X,M 3 X,M 4 X,w; u,v,w,t]

private theorem coherentKernel_zero : coherentKernel 0 =
    thetaCuspSelfDualThetaMass^2 • kernelMoments (thetaCuspSelfDualModularScale^2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coherentKernel, coherentKernelBasis, kernelMoments, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, native_hankel_zero,
      Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem singleCoherentKernel_zero : singleCoherentKernel 0 =
    thetaCuspSelfDualThetaMass^2 • singleKernelMoments (thetaCuspSelfDualModularScale^2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singleCoherentKernel, singleCoherentKernelBasis, singleKernelMoments,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, native_hankel_zero,
      Matrix.smul_apply, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem coherentKernel_det : (coherentKernel 0).det =
    thetaCuspSelfDualThetaMass^6*headTwoCof (thetaCuspSelfDualModularScale^2) := by
  rw [coherentKernel_zero, Matrix.det_smul]
  norm_num [kernelMoments, Matrix.det_fin_three, headTwoCof,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

private theorem singleCoherentKernel_det : (singleCoherentKernel 0).det =
    thetaCuspSelfDualThetaMass^8*coupledCof (thetaCuspSelfDualModularScale^2) := by
  rw [singleCoherentKernel_zero, Matrix.det_smul]
  simp only [singleKernelMoments]
  rw [symmetric_four_det]
  norm_num only [Fintype.card_fin]
  unfold coupledCof
  ring

private theorem seamMass_pos : 0 < thetaCuspSelfDualThetaMass := by
  have h := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
  linarith only [h]

/-- A single load leaves an indefinite four-dimensional origin kernel. -/
theorem singleCoherentKernel_zero_not_posSemidef : ¬ (singleCoherentKernel 0).PosSemidef := by
  have hd : (singleCoherentKernel 0).det < 0 := by
    rw [singleCoherentKernel_det]
    exact mul_neg_of_pos_of_neg (pow_pos seamMass_pos 8) (coupledCof_negative
      thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
      thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le)
  intro h
  exact (not_lt_of_ge h.det_nonneg) hd

private theorem three_posDef_of_head_det (K : Matrix (Fin 3) (Fin 3) ℝ)
    (hK : K.IsHermitian) (hA : (K.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hd : 0 < K.det) : K.PosDef := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := K.submatrix Fin.castSucc Fin.castSucc
  let b : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => K (Fin.castSucc i) 2
  let t : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => K 2 2
  let e : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
  have hsym (i j : Fin 3) : K i j = K j i := by
    have h := congrArg (fun Q : Matrix (Fin 3) (Fin 3) ℝ => Q j i)
      (show Kᴴ = K from hK)
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have he : K.submatrix e e = fromBlocks A b bᴴ t := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [A,b,t,e,finSumFinEquiv,Fin.castAdd,Fin.natAdd,Fin.castLE] <;>
      first | rfl | exact hsym _ _
  letI : Invertible A := hA.isUnit.invertible
  let g := K 2 2-(bᴴ*A⁻¹*b) 0 0
  have hedet : K.det = A.det*g := by
    have h := congrArg Matrix.det he
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁,
      Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one] at h
    simpa only [t,Matrix.sub_apply,g] using h
  have hg : 0 < g := (mul_pos_iff_of_pos_left hA.det_pos).mp (by rwa [← hedet])
  have hs : (t-bᴴ*A⁻¹*b).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i
      fin_cases j
      simp
    · intro v
      simp only [star_trivial,dotProduct,Matrix.mulVec,Fin.sum_univ_one]
      change 0 ≤ v 0*(g*v 0)
      nlinarith only [mul_nonneg hg.le (sq_nonneg (v 0))]
  have hb := (Matrix.PosDef.fromBlocks₁₁ b t hA).mpr hs
  rw [← he] at hb
  have hk : K.PosSemidef := by
    have h := hb.submatrix e.symm
    simpa using h
  exact hk.posDef_iff_det_ne_zero.mpr hd.ne'

/-- The common kernel of the two coupled loads is strictly positive at the actual origin. -/
theorem coherentKernel_zero_posDef : (coherentKernel 0).PosDef := by
  apply three_posDef_of_head_det
  · rw [coherentKernel_zero, Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kernelMoments, Matrix.conjTranspose_apply]
  · have he : (coherentKernel 0).submatrix Fin.castSucc Fin.castSucc =
        (thetaCuspNativeEvenHead 0).submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [coherentKernel, coherentKernelBasis, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Fin.sum_univ_succ, thetaCuspNativeEvenHead,
          finiteHankelMatrix, nativeShiftedMatrix]
    rw [he]
    exact thetaCuspNativeEvenHead_zero_posDef.submatrix (Fin.castSucc_injective 2)
  · rw [coherentKernel_det]
    exact mul_pos (pow_pos seamMass_pos 6) (headTwoCof_positive
      thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
      thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le)


private def headDet (X : ℝ) : ℝ := M 0 X*M 2 X-(M 1 X)^2
private def adjPair (X p q r s : ℝ) : ℝ :=
  M 2 X*p*r-M 1 X*(p*s+q*r)+M 0 X*q*s
private def fixedLoad (C X : ℝ) : ℝ := 3*C*M 0 X
private def s00 (C _D X : ℝ) : ℝ :=
  headDet X*(M 4 X+fixedLoad C X)-adjPair X (M 2 X) (M 3 X) (M 2 X) (M 3 X)
private def s01 (C _D X : ℝ) : ℝ :=
  headDet X*(M 5 X+420*fixedLoad C X)-adjPair X (M 2 X) (M 3 X) (M 3 X) (M 4 X)
private def s02 (_C _D X : ℝ) : ℝ :=
  headDet X*M 6 X-adjPair X (M 2 X) (M 3 X) (M 4 X) (M 5 X)
private def s11 (C D X : ℝ) : ℝ :=
  headDet X*(M 6 X+176400*fixedLoad C X+fixedLoad D X)-adjPair X (M 3 X) (M 4 X) (M 3 X) (M 4 X)
private def s12 (_C D X : ℝ) : ℝ :=
  headDet X*(M 7 X+1568*fixedLoad D X)-adjPair X (M 3 X) (M 4 X) (M 4 X) (M 5 X)
private def s22 (_C D X : ℝ) : ℝ :=
  headDet X*(M 8 X+2458624*fixedLoad D X)-adjPair X (M 4 X) (M 5 X) (M 4 X) (M 5 X)
private def minorTwo (C D X : ℝ) : ℝ := s00 C D X*s11 C D X-(s01 C D X)^2
private def minorThree (C D X : ℝ) : ℝ :=
  s00 C D X*s11 C D X*s22 C D X+2*s01 C D X*s02 C D X*s12 C D X-s00 C D X*(s12 C D X)^2-
    s11 C D X*(s02 C D X)^2-s22 C D X*(s01 C D X)^2

private theorem common_second_negative {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    minorTwo 1000000000 1000000000 X < 0 := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [minorTwo,s00,s01,s11,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, pow_nonneg hz 25, pow_nonneg hz 26, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24, hp 25, hp 26]

private theorem unequal_second_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < minorTwo 100000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [minorTwo,s00,s01,s11,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, pow_nonneg hz 25, pow_nonneg hz 26, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24, hp 25, hp 26]

private theorem unequal_third_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < minorThree 100000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [minorThree,s00,s01,s02,s11,s12,s22,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6,moment_7,moment_8]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, pow_nonneg hz 25, pow_nonneg hz 26, pow_nonneg hz 27, pow_nonneg hz 28, pow_nonneg hz 29, pow_nonneg hz 30, pow_nonneg hz 31, pow_nonneg hz 32, pow_nonneg hz 33, pow_nonneg hz 34, pow_nonneg hz 35, pow_nonneg hz 36, pow_nonneg hz 37, pow_nonneg hz 38, pow_nonneg hz 39, pow_nonneg hz 40, pow_nonneg hz 41, pow_nonneg hz 42, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24, hp 25, hp 26, hp 27, hp 28, hp 29, hp 30, hp 31, hp 32, hp 33, hp 34, hp 35, hp 36, hp 37, hp 38, hp 39, hp 40, hp 41, hp 42]


private theorem unequal_first_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) :
    0 < s00 100000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  rw [hX]
  simp only [s00,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12]

/-- The two coupled loads with independent coefficients. -/
def coupledLoad (C D : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,0,0,0,0; 0,0,0,0,0; 0,0,C,420*C,0;
    0,0,420*C,176400*C+D,1568*D; 0,0,0,1568*D,2458624*D]

/-- Independent coupled corrections of the fifth native even source. -/
def coupledRepair (C D x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 x + thetaCuspCenterCompensationSource x • coupledLoad C D

private def normHead (X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![M 0 X,M 1 X; M 1 X,M 2 X]
private def normBorder (X : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![M 2 X,M 3 X,M 4 X; M 3 X,M 4 X,M 5 X]
private def normTail (C D X : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![M 4 X+fixedLoad C X,M 5 X+420*fixedLoad C X,M 6 X;
    M 5 X+420*fixedLoad C X,M 6 X+176400*fixedLoad C X+fixedLoad D X,
      M 7 X+1568*fixedLoad D X;
    M 6 X,M 7 X+1568*fixedLoad D X,M 8 X+2458624*fixedLoad D X]
private def schurNumerator (C D X : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s00 C D X,s01 C D X,s02 C D X;
    s01 C D X,s11 C D X,s12 C D X;
    s02 C D X,s12 C D X,s22 C D X]

private theorem normHead_posDef : (normHead (thetaCuspSelfDualModularScale^2)).PosDef := by
  have h := coherentKernel_zero_posDef.submatrix (Fin.castSucc_injective 2)
  have he : (coherentKernel 0).submatrix Fin.castSucc Fin.castSucc =
      thetaCuspSelfDualThetaMass^2 • normHead (thetaCuspSelfDualModularScale^2) := by
    rw [coherentKernel_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [kernelMoments,normHead]
  rw [he] at h
  have hp := h.smul (inv_pos.mpr (pow_pos seamMass_pos 2))
  simpa only [smul_smul,inv_mul_cancel₀ (pow_pos seamMass_pos 2).ne',one_smul] using hp

private theorem headDet_pos : 0 < headDet (thetaCuspSelfDualModularScale^2) := by
  simpa [normHead,Matrix.det_fin_two,headDet,pow_two] using normHead_posDef.det_pos

private theorem normHead_inverse (X : ℝ) (hd : headDet X ≠ 0) :
    (normHead X)⁻¹ = (headDet X)⁻¹ • (!![M 2 X,-M 1 X; -M 1 X,M 0 X] : Matrix (Fin 2) (Fin 2) ℝ) := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ :=
    (headDet X)⁻¹ • !![M 2 X,-M 1 X; -M 1 X,M 0 X]
  have hl : Q*normHead X=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q,normHead,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;>
      field_simp [hd] <;> simp only [headDet] <;> ring
  have hr : normHead X*Q=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q,normHead,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;>
      field_simp [hd] <;> simp only [headDet] <;> ring
  letI : Invertible (normHead X) := ⟨Q,hl,hr⟩
  rw [← Matrix.invOf_eq_nonsing_inv]
  rfl

private theorem norm_schur (C D X : ℝ) (hd : headDet X ≠ 0) :
    normTail C D X-(normBorder X)ᴴ*(normHead X)⁻¹*normBorder X =
      (headDet X)⁻¹ • schurNumerator C D X := by
  rw [normHead_inverse X hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normTail,normBorder,schurNumerator,s00,s01,s02,s11,s12,s22,adjPair,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;>
    field_simp [hd] <;> ring

private theorem coupled_origin_block (C D : ℝ) :
    (coupledRepair C D 0).submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)
      (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5) =
    thetaCuspSelfDualThetaMass^2 • fromBlocks
      (normHead (thetaCuspSelfDualModularScale^2))
      (normBorder (thetaCuspSelfDualModularScale^2))
      (normBorder (thetaCuspSelfDualModularScale^2))ᴴ
      (normTail C D (thetaCuspSelfDualModularScale^2)) := by
  have hphi : thetaCuspFullSource 0^2 = thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    have h := native_all (0 : Fin 9)
    simpa [thetaCuspNativeReflectionJet_zero,thetaCuspSourceReflectionJetZero,pow_two] using h
  have hg : thetaCuspCenterCompensationSource 0 =
      3*thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    simp only [thetaCuspCenterCompensationSource,mul_zero,zero_mul,add_zero,hphi]
    ring
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [coupledRepair,coupledLoad,Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,
      native_hankel_zero,hg,normHead,normBorder,normTail,fixedLoad,Matrix.conjTranspose_apply,
      finSumFinEquiv,Fin.castAdd,Fin.natAdd,Fin.castLE,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.vecHead,Matrix.vecTail] <;> ring

private theorem two_posDef_of_minors (a b c : ℝ) (ha : 0 < a) (hd : 0 < a*c-b^2) :
    (!![a,b;b,c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro v hv
    simp only [star_trivial,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
    change 0 < v 0*(a*v 0+b*v 1)+v 1*(b*v 0+c*v 1)
    by_cases h1 : v 1=0
    · have h0 : v 0 ≠ 0 := by
        intro hz
        apply hv
        ext i
        fin_cases i <;> simp [hz,h1]
      simp only [h1,mul_zero,zero_mul,add_zero]
      nlinarith only [mul_pos ha (sq_pos_of_ne_zero h0)]
    · have hp := add_pos_of_nonneg_of_pos (sq_nonneg (a*v 0+b*v 1))
        (mul_pos hd (sq_pos_of_ne_zero h1))
      have he : (a*v 0+b*v 1)^2+(a*c-b^2)*(v 1)^2 =
          a*(v 0*(a*v 0+b*v 1)+v 1*(b*v 0+c*v 1)) := by ring
      rw [he] at hp
      exact (mul_pos_iff_of_pos_left ha).mp hp

private theorem unequal_schur_posDef :
    (schurNumerator 100000000 1000000000000 (thetaCuspSelfDualModularScale^2)).PosDef := by
  have hlo := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hhi := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
  apply three_posDef_of_head_det
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schurNumerator]
  · have he : (schurNumerator 100000000 1000000000000 (thetaCuspSelfDualModularScale^2)).submatrix
        Fin.castSucc Fin.castSucc = !![
          s00 100000000 1000000000000 (thetaCuspSelfDualModularScale^2),
          s01 100000000 1000000000000 (thetaCuspSelfDualModularScale^2);
          s01 100000000 1000000000000 (thetaCuspSelfDualModularScale^2),
          s11 100000000 1000000000000 (thetaCuspSelfDualModularScale^2)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [he]
    exact two_posDef_of_minors _ _ _ (unequal_first_positive hlo)
      (unequal_second_positive hlo hhi)
  · have he : (schurNumerator 100000000 1000000000000 (thetaCuspSelfDualModularScale^2)).det =
        minorThree 100000000 1000000000000 (thetaCuspSelfDualModularScale^2) := by
      norm_num [schurNumerator,Matrix.det_fin_three,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,minorThree]
      ring
    rw [he]
    exact unequal_third_positive hlo hhi

private theorem coupled_zero_posDef_of_schur (C D : ℝ)
    (hs : (schurNumerator C D (thetaCuspSelfDualModularScale^2)).PosDef) :
    (coupledRepair C D 0).PosDef := by
  let X := thetaCuspSelfDualModularScale^2
  let A := normHead X
  let B := normBorder X
  let T := normTail C D X
  have hA : A.PosDef := normHead_posDef
  letI : Invertible A := hA.isUnit.invertible
  have hS : (T-Bᴴ*A⁻¹*B).PosDef := by
    rw [show T-Bᴴ*A⁻¹*B = normTail C D X-
      (normBorder X)ᴴ*(normHead X)⁻¹*normBorder X from rfl,
      norm_schur _ _ _ headDet_pos.ne']
    exact hs.smul (inv_pos.mpr headDet_pos)
  have hp : (fromBlocks A B Bᴴ T).PosDef := by
    have hh := (Matrix.PosDef.fromBlocks₁₁ B T hA).mpr hS.posSemidef
    apply hh.posDef_iff_det_ne_zero.mpr
    rw [Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv]
    exact mul_ne_zero hA.det_pos.ne' hS.det_pos.ne'
  have hfull := hp.smul (pow_pos seamMass_pos 2)
  rw [← coupled_origin_block] at hfull
  have hh := hfull.submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm.injective
  simpa using hh

/-- A fixed unequal pair of coupled loads repairs the actual origin. -/
theorem coupledRepair_unequal_zero_posDef :
    (coupledRepair 100000000 1000000000000 0).PosDef :=
  coupled_zero_posDef_of_schur _ _ unequal_schur_posDef

/-- A billion units on both coupled loads still leaves a negative fourth origin minor. -/
theorem coupledRepair_common_billion_not_posSemidef :
    ¬ (coupledRepair 1000000000 1000000000 0).PosSemidef := by
  intro h
  let X := thetaCuspSelfDualModularScale^2
  let A := normHead X
  let B := normBorder X
  let T := normTail 1000000000 1000000000 X
  have hA : A.PosDef := normHead_posDef
  letI : Invertible A := hA.isUnit.invertible
  have hn := (h.submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)).smul
    (inv_pos.mpr (pow_pos seamMass_pos 2)).le
  rw [coupled_origin_block,smul_smul,inv_mul_cancel₀ (pow_pos seamMass_pos 2).ne',one_smul] at hn
  have hS := (Matrix.PosDef.fromBlocks₁₁ B T hA).mp hn
  change (normTail 1000000000 1000000000 X-(normBorder X)ᴴ*(normHead X)⁻¹*normBorder X).PosSemidef at hS
  rw [norm_schur _ _ _ headDet_pos.ne'] at hS
  have hc := hS.smul headDet_pos.le
  rw [smul_smul,mul_inv_cancel₀ headDet_pos.ne',one_smul] at hc
  have hd := (hc.submatrix Fin.castSucc).det_nonneg
  have he : ((schurNumerator 1000000000 1000000000 X).submatrix Fin.castSucc Fin.castSucc).det =
      minorTwo 1000000000 1000000000 X := by
    norm_num [schurNumerator,Matrix.det_fin_two,Matrix.submatrix_apply,minorTwo]
    ring
  rw [he] at hd
  exact (not_lt_of_ge hd) (common_second_negative
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le)




private theorem coupledLoad_one_posSemidef : (coupledLoad 1 1).PosSemidef := by
  let U : Matrix (Fin 2) (Fin 5) ℝ := !![0,0,1,420,0; 0,0,0,1,1568]
  have he : coupledLoad 1 1=Uᴴ*U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coupledLoad,U,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self U

private theorem coupledLoad_hermitian (C D : ℝ) : (coupledLoad C D).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coupledLoad,Matrix.conjTranspose_apply,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.vecHead,Matrix.vecTail]

private theorem coupledRepair_hermitian (C D x : ℝ) : (coupledRepair C D x).IsHermitian := by
  apply Matrix.IsHermitian.add
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeShiftedMatrix,add_comm]
  · exact (coupledLoad_hermitian C D).smul (by simp [IsSelfAdjoint])

private theorem coupledRepair_continuous (C D : ℝ) : Continuous (coupledRepair C D) := by
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold coupledRepair nativeShiftedMatrix thetaCuspCenterCompensationSource
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

/-- The common load must exceed a billion already at the origin. -/
theorem coupled_common_origin_load_needed {C : ℝ}
    (h : (coupledRepair C C 0).PosSemidef) : 1000000000 < C := by
  by_contra hC
  have hc : C ≤ 1000000000 := le_of_not_gt hC
  have hg : 0 < thetaCuspCenterCompensationSource 0 := by
    simp only [thetaCuspCenterCompensationSource,mul_zero,zero_mul,add_zero]
    exact mul_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))
  have hp := h.add (coupledLoad_one_posSemidef.smul
    (mul_nonneg (sub_nonneg.mpr hc) hg.le))
  have he : coupledRepair C C 0 +
      ((1000000000-C)*thetaCuspCenterCompensationSource 0) • coupledLoad 1 1 =
      coupledRepair 1000000000 1000000000 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coupledRepair,coupledLoad,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.vecHead,Matrix.vecTail] <;> ring
  rw [he] at hp
  exact coupledRepair_common_billion_not_posSemidef hp

private theorem coupled_witness_center_pos : 0 < EvenFiveBoundary.witnessCenter := by
  unfold EvenFiveBoundary.witnessCenter
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  apply (one_lt_div Real.pi_pos).mpr
  linarith only [Real.pi_lt_d2]

/-- No real common coefficient makes both coupled source loads globally positive. -/
theorem coupled_common_source_fails (C : ℝ) :
    ¬ ∀ x : ℝ, 0 ≤ x → (coupledRepair C C x).PosSemidef := by
  intro h
  have hc := coupled_common_origin_load_needed (h 0 le_rfl)
  have hp := (h EvenFiveBoundary.witnessCenter coupled_witness_center_pos.le).diag_nonneg (i := (2 : Fin 5))
  have hn := EvenFiveBoundary.fourth_moment_load_negative_of_oneBillion_le hc.le
  norm_num [coupledRepair,coupledLoad,nativeShiftedMatrix,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail] at hp
  nlinarith only [hp,hn]

/-- The literal weighted source with independent coupled zero-flux loads. -/
def coupledWeightedRepair (a C D r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (r*Real.sinh (a*r)) • nativeShiftedMatrix 5 0 (r/2) +
    deriv (thetaCuspCenterCompensationFlux a) r • coupledLoad C D

private theorem coupled_weighted_energy (a C r : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (coupledWeightedRepair a C C r *ᵥ v) =
      (r*Real.sinh (a*r))*(v ⬝ᵥ (coupledRepair C C (r/2) *ᵥ v)) +
      C*(deriv (thetaCuspCenterCompensationFlux a) r-
        (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))*
        (v ⬝ᵥ (coupledLoad 1 1 *ᵥ v)) := by
  have he : coupledWeightedRepair a C C r =
      (r*Real.sinh (a*r)) • coupledRepair C C (r/2) +
      (C*(deriv (thetaCuspCenterCompensationFlux a) r-
        (r*Real.sinh (a*r))*thetaCuspCenterCompensationSource (r/2))) • coupledLoad 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [coupledWeightedRepair,coupledRepair,coupledLoad,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] <;> ring
  simp only [he,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

private def coupledUpper (a C r : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v ⬝ᵥ (coupledRepair C C (r/2) *ᵥ v)+
    (a*r)*thetaCuspFullSource (r/2)^2 * |C| *(v ⬝ᵥ (coupledLoad 1 1 *ᵥ v))

private theorem coupled_weighted_le_upper {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (C : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (coupledWeightedRepair a C C r *ᵥ v) ≤
      (r*Real.sinh (a*r))*coupledUpper a C r v := by
  obtain ⟨h0,hU⟩ := flux_slack_bounds ha hr
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) h0
  have hCU := mul_le_mul_of_nonneg_left hU (abs_nonneg C)
  have hN := coupledLoad_one_posSemidef.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hN
  have hh := mul_le_mul_of_nonneg_right (hC.trans hCU) hN
  rw [coupled_weighted_energy]
  unfold coupledUpper
  nlinarith only [hh]

private theorem coupledUpper_continuous (a C : ℝ) (v : Fin 5 → ℝ) :
    Continuous (fun r => coupledUpper a C r v) := by
  have hM := coupledRepair_continuous C C
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  unfold coupledUpper
  simp only [dotProduct,Matrix.mulVec]
  fun_prop

private theorem coupled_origin_of_weighted {a C : ℝ} (ha : 0 < a)
    (h : ∀ r : ℝ, 0 < r → (coupledWeightedRepair a C C r).PosSemidef) :
    (coupledRepair C C 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (coupledRepair_hermitian C C 0)
  intro v
  simp only [star_trivial]
  have hnonneg (r : ℝ) (hr : 0 < r) : 0 ≤ coupledUpper a C r v := by
    have hh := (h r hr).dotProduct_mulVec_nonneg v
    simp only [star_trivial] at hh
    have hu := hh.trans (coupled_weighted_le_upper ha hr C v)
    have hw : 0 < r*Real.sinh (a*r) := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
    by_contra hn
    exact (not_lt_of_ge hu) (mul_neg_of_pos_of_neg hw (lt_of_not_ge hn))
  have ht : Tendsto (fun r => coupledUpper a C r v) (𝓝[>] 0)
      (𝓝 (v ⬝ᵥ (coupledRepair C C 0 *ᵥ v))) := by
    have hc := (coupledUpper_continuous a C v).tendsto 0
    simpa only [coupledUpper,zero_div,mul_zero,zero_mul,add_zero] using
      hc.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hnonneg r hr

/-- Equal coupled coefficients also fail for every literal critical-aperture representative. -/
theorem coupled_common_weighted_fails {a : ℝ} (ha : 0 < a) (haU : a < 1/2) (C : ℝ) :
    ¬ ∀ r : ℝ, 0 < r → (coupledWeightedRepair a C C r).PosSemidef := by
  intro h
  have hc := coupled_common_origin_load_needed (coupled_origin_of_weighted ha h)
  have hr : 0 < EvenFiveBoundary.witnessRadius := by
    unfold EvenFiveBoundary.witnessRadius
    exact mul_pos (by norm_num) coupled_witness_center_pos
  have hp := (h EvenFiveBoundary.witnessRadius hr).diag_nonneg (i := (2 : Fin 5))
  have hn := EvenFiveBoundary.fourth_moment_weighted_load_negative_of_oneBillion_le ha haU hc.le
  norm_num [coupledWeightedRepair,coupledLoad,nativeShiftedMatrix,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,EvenFiveBoundary.witnessRadius,
    EvenFiveBoundary.witnessWeight,EvenFiveBoundary.weightedLoad] at hp hn
  nlinarith only [hp,hn]



private theorem reduced_first_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < s00 10000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  rw [hX]
  simp only [s00,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12]


private theorem reduced_second_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < minorTwo 10000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [minorTwo,s00,s01,s11,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, pow_nonneg hz 25, pow_nonneg hz 26, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24, hp 25, hp 26]
private theorem reduced_third_positive {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 96/5) :
    0 < minorThree 10000000 1000000000000 X := by
  let z := 10*X-191
  have hz : 0 ≤ z := by dsimp [z]; linarith only [hlo]
  have hzU : z ≤ 1 := by dsimp [z]; linarith only [hhi]
  have hX : X = (z+191)/10 := by dsimp [z]; ring
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  rw [hX]
  simp only [minorThree,s00,s01,s02,s11,s12,s22,headDet,adjPair,fixedLoad,moment_0,moment_1,moment_2,moment_3,moment_4,moment_5,moment_6,moment_7,moment_8]
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, pow_nonneg hz 25, pow_nonneg hz 26, pow_nonneg hz 27, pow_nonneg hz 28, pow_nonneg hz 29, pow_nonneg hz 30, pow_nonneg hz 31, pow_nonneg hz 32, pow_nonneg hz 33, pow_nonneg hz 34, pow_nonneg hz 35, pow_nonneg hz 36, pow_nonneg hz 37, pow_nonneg hz 38, pow_nonneg hz 39, pow_nonneg hz 40, pow_nonneg hz 41, pow_nonneg hz 42, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24, hp 25, hp 26, hp 27, hp 28, hp 29, hp 30, hp 31, hp 32, hp 33, hp 34, hp 35, hp 36, hp 37, hp 38, hp 39, hp 40, hp 41, hp 42]
private theorem reduced_schur_posDef :
    (schurNumerator 10000000 1000000000000 (thetaCuspSelfDualModularScale^2)).PosDef := by
  have hlo := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hhi := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
  apply three_posDef_of_head_det
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schurNumerator]
  · have he : (schurNumerator 10000000 1000000000000 (thetaCuspSelfDualModularScale^2)).submatrix
        Fin.castSucc Fin.castSucc = !![
          s00 10000000 1000000000000 (thetaCuspSelfDualModularScale^2),
          s01 10000000 1000000000000 (thetaCuspSelfDualModularScale^2);
          s01 10000000 1000000000000 (thetaCuspSelfDualModularScale^2),
          s11 10000000 1000000000000 (thetaCuspSelfDualModularScale^2)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [he]
    exact two_posDef_of_minors _ _ _ (reduced_first_positive hlo hhi)
      (reduced_second_positive hlo hhi)
  · have he : (schurNumerator 10000000 1000000000000 (thetaCuspSelfDualModularScale^2)).det =
        minorThree 10000000 1000000000000 (thetaCuspSelfDualModularScale^2) := by
      norm_num [schurNumerator,Matrix.det_fin_three,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,minorThree]
      ring
    rw [he]
    exact reduced_third_positive hlo hhi

/-- The smaller first coupled coefficient still gives a strict actual origin. -/
theorem coupledRepair_reduced_zero_posDef :
    (coupledRepair 10000000 1000000000000 0).PosDef :=
  coupled_zero_posDef_of_schur _ _ reduced_schur_posDef

/-- The first nine origin moment polynomials, extended by zero for indices above eight. -/
def originMomentPolynomial (X : ℝ) (k : ℕ) : ℝ :=
  if k=0 then (9 / 64 + X * (-3 / 64) + X ^ 2 * (1 / 256)) else
  if k=1 then (45 / 64 + X * (-165 / 256) + X ^ 2 * (21 / 256) + X ^ 3 * (1 / 1024)) else
  if k=2 then (765 / 64 + X * (-2505 / 128) + X ^ 2 * (4461 / 1024) + X ^ 3 * (77 / 1024) + X ^ 4 * (27 / 4096)) else
  if k=3 then (24345 / 64 + X * (-243615 / 256) + X ^ 2 * (333759 / 1024) + X ^ 3 * (31519 / 4096) + X ^ 4 *
    (8199 / 4096) + X ^ 5 * (-21 / 16384)) else
  if k=4 then (1207665 / 64 + X * (-2122095 / 32) + X ^ 2 * (16407993 / 512) + X ^ 3 * (1024127 / 1024) + X ^ 4
    * (7963857 / 16384) + X ^ 5 * (-30027 / 16384) + X ^ 6 * (5133 / 65536)) else
  if k=5 then (85066245 / 64 + X * (-1591823865 / 256) + X ^ 2 * (2049802467 / 512) + X ^ 3 * (327670217 /
    2048) + X ^ 4 * (1966854177 / 16384) + X ^ 5 * (-62366877 / 65536) + X ^ 6 * (3218985 / 65536) +
    X ^ 7 * (-725859 / 262144)) else
  if k=6 then (8028542565 / 64 + X * (-96262740255 / 128) + X ^ 2 * (634560122211 / 1024) + X ^ 3 * (1975395347
    / 64) + X ^ 4 * (529421297031 / 16384) + X ^ 5 * (-13501200603 / 32768) + X ^ 6 * (6251467509 /
    262144) + X ^ 7 * (-888527835 / 262144) + X ^ 8 * (-10466793 / 1048576)) else
  if k=7 then (975220892145 / 64 + X * (-29124679352115 / 256) + X ^ 2 * (119242543472409 / 1024) + X ^ 3 *
    (28953599674549 / 4096) + X ^ 4 * (159032056610583 / 16384) + X ^ 5 * (-11525159347845 / 65536)
    + X ^ 6 * (2939734839795 / 262144) + X ^ 7 * (-3025910283417 / 1048576) + X ^ 8 * (-16707449205
    / 1048576) + X ^ 9 * (-202414761 / 4194304)) else
  if k=8 then (147972940725465 / 64 + X * (-1345440989479065 / 64) + X ^ 2 * (1671683363523321 / 64) + X ^ 3 *
    (971257441098301 / 512) + X ^ 4 * (26851592045541915 / 8192) + X ^ 5 * (-321887823511059 / 4096)
    + X ^ 6 * (359400635300889 / 65536) + X ^ 7 * (-288451649154465 / 131072) + X ^ 8 *
    (-73300953671271 / 4194304) + X ^ 9 * (-684133624179 / 4194304) + X ^ 10 * (139969720953 /
    16777216)) else
  0

private theorem moment_eq_polynomial (X : ℝ) (k : Fin 9) :
    M k.val X = originMomentPolynomial X k.val := by
  fin_cases k <;>
    norm_num [originMomentPolynomial,moment_0,moment_1,moment_2,moment_3,moment_4,
      moment_5,moment_6,moment_7,moment_8]

/-- Dividing the native origin matrix by its center compensation cancels the self-dual mass. -/
theorem native_normalized_zero (i j : Fin 5) :
    nativeShiftedMatrix 5 0 0 i j/thetaCuspCenterCompensationSource 0 =
      originMomentPolynomial (thetaCuspSelfDualModularScale^2) (i.val+j.val)/
        (3*originMomentPolynomial (thetaCuspSelfDualModularScale^2) 0) := by
  have hij : M (i.val+j.val) (thetaCuspSelfDualModularScale^2) =
      originMomentPolynomial (thetaCuspSelfDualModularScale^2) (i.val+j.val) :=
    moment_eq_polynomial _ ⟨i.val+j.val,by omega⟩
  have hzero : M 0 (thetaCuspSelfDualModularScale^2) =
      originMomentPolynomial (thetaCuspSelfDualModularScale^2) 0 :=
    moment_eq_polynomial _ (0 : Fin 9)
  rw [← hij,← hzero]
  have hphi : thetaCuspFullSource 0^2 =
      thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    have h := native_all (0 : Fin 9)
    simpa [thetaCuspNativeReflectionJet_zero,thetaCuspSourceReflectionJetZero,pow_two] using h
  have hg : thetaCuspCenterCompensationSource 0 =
      3*thetaCuspSelfDualThetaMass^2*M 0 (thetaCuspSelfDualModularScale^2) := by
    simp only [thetaCuspCenterCompensationSource,mul_zero,zero_mul,add_zero,hphi]
    ring
  have hx : thetaCuspSelfDualModularScale^2-6 ≠ 0 := by
    have h := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
    linarith only [h]
  have hm : M 0 (thetaCuspSelfDualModularScale^2) ≠ 0 := by
    apply ne_of_gt
    rw [moment_0]
    nlinarith only [sq_pos_of_ne_zero hx]
  rw [native_hankel_zero,hg]
  field_simp [seamMass_pos.ne',hm]

end GaloisForLFunctions.ThetaCuspSections.EvenFiveOrigin
