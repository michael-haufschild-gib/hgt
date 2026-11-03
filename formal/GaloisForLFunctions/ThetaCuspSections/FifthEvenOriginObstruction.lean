import GaloisForLFunctions.ThetaCuspSections.FifthEvenInheritedLoadBoundary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamCurvatureMoments

/-!
# The fifth even theta source forces a positive fifth load at the origin

The principal minor on indices zero, one, two, and four is strictly negative
at the modular seam. Its Schur coordinate gives the sharp positive fifth-load
threshold for a full origin repair. Together with the scale-seven capacity gap,
this excludes every real pair of constant diagonal loads, including the actual
weighted representative at each critical aperture.
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

end GaloisForLFunctions.ThetaCuspSections.EvenFiveOrigin
