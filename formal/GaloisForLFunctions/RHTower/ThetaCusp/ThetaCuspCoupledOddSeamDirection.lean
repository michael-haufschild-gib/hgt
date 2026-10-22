import GaloisForLFunctions.HTGeometry.HankelFourDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurCompensation

/-!
# Exact direction criterion for the canonically repaired fourth odd seam block

The canonical coefficient correlates with the native source by C3*G*H2=-3*D3.
Jacobi's identity then gives an exact squared direction penalty. Its vanishing
direction maximizes the repaired determinant, and the resulting load criterion
is necessary and sufficient. These are literal-source identities and criteria;
no global fourth-row positivity or RH conclusion is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Exact determinant of the coupled rank-one repair plus its last diagonal correction. -/
private theorem det_coupled_odd_four {K : Type*} [CommRing K] (a b c d e f g s t L : K) :
    Matrix.det !![a,b,c,d; b,c,d,e; c,d,e+s,f+s*t; d,e,f+s*t,g+s*t^2+L] =
      hankelFourDet a b c d e f g+
      s*((a*c*g-a*e^2-b^2*g+2*b*d*e-c*d^2)+
        2*t*(-(a*c*f-a*d*e-b^2*f+b*c*e+b*d^2-c^2*d))+
        t^2*(a*c*e-a*d^2-b^2*e+2*b*c*d-c^3))+
      L*((a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)+s*(a*c-b^2)) := by
  have hcast : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    hcast, Fin.lt_def, Fin.le_def, Fin.isValue, -Fin.val_fin_lt, -Fin.val_fin_le, -Fin.val_pos_iff]
  unfold hankelFourDet
  ring

/-- Jacobi's identity keeps the first two rows as the exact Schur denominator. -/
private theorem hankelFour_jacobi {K : Type*} [CommRing K] (a b c d e f g : K) :
    (a*c-b^2)*hankelFourDet a b c d e f g =
      (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)*(a*c*g-a*e^2-b^2*g+2*b*d*e-c*d^2)-
      (a*c*f-a*d*e-b^2*f+b*c*e+b*d^2-c^2*d)^2 := by
  unfold hankelFourDet
  ring

end GaloisForLFunctions.HTGeometry

namespace RHTower.ThetaCuspCoupledSeamDirection
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Signed odd moments of the literal infinite source at the self-dual seam. -/
def sourceMoment (k : Fin 7) : ℝ :=
  (-1:ℝ)^(k.val+1)*thetaCuspNativeReflectionJet (2*(k.val+1)) 0

private def symmetricDet (a b c d e f g h i j : ℝ) : ℝ :=
  (a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)*j-
    ((e*h-f^2)*d^2+2*(c*f-b*h)*d*g+2*(b*f-c*e)*d*i+
      (a*h-c^2)*g^2+2*(b*c-a*f)*g*i+(a*e-b^2)*i^2)

private def symmetricEnergy (a b c d e f g h i j x y z w : ℝ) : ℝ :=
  a*x^2+2*b*x*y+2*c*x*z+2*d*x*w+e*y^2+2*f*y*z+2*g*y*w+
    h*z^2+2*i*z*w+j*w^2

private theorem positive_mul_nonpos {a b : ℝ} (ha : 0 < a) (h : a*b ≤ 0) : b ≤ 0 := by
  by_contra hb
  exact (not_lt_of_ge h) (mul_pos ha (lt_of_not_ge hb))

private theorem symmetricEnergy_pos {a b c d e f g h i j x y z w : ℝ}
    (ha : 0 < a) (h2 : 0 < a*e-b^2)
    (h3 : 0 < a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e)
    (h4 : 0 < symmetricDet a b c d e f g h i j)
    (hne : x=0 → y=0 → z=0 → w=0 → False) :
    0 < symmetricEnergy a b c d e f g h i j x y z w := by
  let D2 := a*e-b^2
  let D3 := a*e*h-a*f^2-b^2*h+2*b*c*f-c^2*e
  let D4 := symmetricDet a b c d e f g h i j
  let E := a*e*i-a*f*g-b^2*i+b*c*g+b*d*f-c*d*e
  have hD2 : 0 < D2 := h2
  have hD3 : 0 < D3 := h3
  have hD4 : 0 < D4 := h4
  have he : a*D2*D3*symmetricEnergy a b c d e f g h i j x y z w =
      D2*D3*(a*x+b*y+c*z+d*w)^2+
      D3*(D2*y+(a*f-b*c)*z+(a*g-b*d)*w)^2+
      a*(D3*z+E*w)^2+a*D2*D4*w^2 := by
    dsimp [D2,D3,D4,E,symmetricEnergy,symmetricDet]
    ring
  by_contra hnot
  have hQ : symmetricEnergy a b c d e f g h i j x y z w ≤ 0 := le_of_not_gt hnot
  have hsum := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ a*D2*D3 by positivity) hQ
  rw [he] at hsum
  have hn0 : 0 ≤ D2*D3*(a*x+b*y+c*z+d*w)^2 := by positivity
  have hn1 : 0 ≤ D3*(D2*y+(a*f-b*c)*z+(a*g-b*d)*w)^2 := by positivity
  have hn2 : 0 ≤ a*(D3*z+E*w)^2 := by positivity
  have hw2 : w^2 ≤ 0 := positive_mul_nonpos (by positivity : 0 < a*D2*D4)
    (show a*D2*D4*w^2 ≤ 0 by linarith only [hsum,hn0,hn1,hn2])
  have hw : w=0 := by nlinarith only [hw2]
  have hz2 : (D3*z+E*w)^2 ≤ 0 := positive_mul_nonpos ha
    (show a*(D3*z+E*w)^2 ≤ 0 by
      have hn3 : 0 ≤ a*D2*D4*w^2 := by positivity
      linarith only [hsum,hn0,hn1,hn3])
  have hz : z=0 := by
    rw [hw] at hz2
    simp only [mul_zero,add_zero,mul_pow] at hz2
    have : z^2 ≤ 0 := positive_mul_nonpos (sq_pos_of_pos hD3) hz2
    nlinarith only [this]
  rw [hw,hz] at hsum
  simp only [mul_zero,add_zero,zero_pow (by decide : 2≠0)] at hsum
  have hy2 : (D2*y)^2 ≤ 0 := positive_mul_nonpos hD3
    (show D3*(D2*y)^2 ≤ 0 by
      have hn : 0 ≤ D2*D3*(a*x+b*y)^2 := by positivity
      linarith only [hsum,hn])
  have hy : y=0 := by
    rw [mul_pow] at hy2
    have : y^2 ≤ 0 := positive_mul_nonpos (sq_pos_of_pos hD2) hy2
    nlinarith only [this]
  rw [hy] at hsum
  simp only [mul_zero,add_zero,zero_pow (by decide : 2≠0),mul_pow] at hsum
  have hx2 : x^2 ≤ 0 :=
    positive_mul_nonpos (by positivity : 0 < D2*D3*a^2)
      (by nlinarith only [hsum] : D2*D3*a^2*x^2 ≤ 0)
  have hx : x=0 := by nlinarith only [hx2]
  exact hne hx hy hz hw


local notation "H" => thetaCuspNativeOddHeadDet 0
local notation "D" => thetaCuspNativeOddHankelThreeDet 0
local notation "G" => thetaCuspCenterCompensationSource 0
local notation "S" => thetaCuspNativeOddCompensationCoefficient*G

/-- Actual uncorrected fourth odd seam determinant. -/
def nativeFourth : ℝ := hankelFourDet (sourceMoment 0) (sourceMoment 1) (sourceMoment 2) (sourceMoment 3) (sourceMoment 4) (sourceMoment 5) (sourceMoment 6)

/-- Actual off-diagonal cofactor selecting the optimal correction direction. -/
def borderCofactor : ℝ := -(sourceMoment 0*sourceMoment 2*sourceMoment 5-sourceMoment 0*sourceMoment 3*sourceMoment 4-(sourceMoment 1)^2*sourceMoment 5+
  sourceMoment 1*sourceMoment 2*sourceMoment 4+sourceMoment 1*(sourceMoment 3)^2-(sourceMoment 2)^2*sourceMoment 3)

private def A : ℝ := sourceMoment 0*sourceMoment 2*sourceMoment 6-sourceMoment 0*(sourceMoment 4)^2-(sourceMoment 1)^2*sourceMoment 6+
  2*sourceMoment 1*sourceMoment 3*sourceMoment 4-sourceMoment 2*(sourceMoment 3)^2

/-- Canonical source repair with free final load and seam direction. -/
def seamMatrix (C t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![sourceMoment 0,sourceMoment 1,sourceMoment 2,sourceMoment 3; sourceMoment 1,sourceMoment 2,sourceMoment 3,sourceMoment 4;
     sourceMoment 2,sourceMoment 3,sourceMoment 4+S,sourceMoment 5+S*t; sourceMoment 3,sourceMoment 4,sourceMoment 5+S*t,sourceMoment 6+S*t^2+C*G]

private theorem head_eq : sourceMoment 0*sourceMoment 2-(sourceMoment 1)^2=H := by
  norm_num [sourceMoment,thetaCuspNativeOddHeadDet]

private theorem three_eq :
    sourceMoment 0*sourceMoment 2*sourceMoment 4-sourceMoment 0*(sourceMoment 3)^2-(sourceMoment 1)^2*sourceMoment 4+2*sourceMoment 1*sourceMoment 2*sourceMoment 3-(sourceMoment 2)^3=D := by
  norm_num [sourceMoment,thetaCuspNativeOddHankelThreeDet,HilbertMetric.signedEvenHankelThreeDet]

private theorem coefficient_exact : S*H = -3*D := by
  have h := thetaCuspNativeOddCompensatedDet_zero
  unfold thetaCuspNativeOddCompensatedDet at h
  nlinarith only [h]

private theorem det_eq (C t : ℝ) :
    (seamMatrix C t).det=nativeFourth+S*(A+2*t*borderCofactor+t^2*D)+C*G*(D+S*H) := by
  have h := det_coupled_odd_four (sourceMoment 0) (sourceMoment 1) (sourceMoment 2) (sourceMoment 3) (sourceMoment 4) (sourceMoment 5) (sourceMoment 6) S t (C*G)
  rw [head_eq,three_eq] at h
  exact h

private theorem jacobi : H*nativeFourth=D*A-borderCofactor^2 := by
  have h := hankelFour_jacobi (sourceMoment 0) (sourceMoment 1) (sourceMoment 2) (sourceMoment 3) (sourceMoment 4) (sourceMoment 5) (sourceMoment 6)
  rw [head_eq,three_eq] at h
  dsimp only [nativeFourth,A,borderCofactor]
  nlinarith only [h]

/-- Exact literal-source direction penalty, with no supplied source hypotheses. -/
theorem determinant_direction_square (C t : ℝ) :
    H*(seamMatrix C t).det =
      -2*H*(nativeFourth+C*G*D)-3*(D*t+borderCofactor)^2 := by
  calc
    H*(seamMatrix C t).det = H*nativeFourth+
        (S*H)*(A+2*t*borderCofactor+t^2*D)+C*G*H*D+C*G*H*(S*H) := by
      rw [det_eq]
      ring
    _ = -2*H*(nativeFourth+C*G*D)-3*(D*t+borderCofactor)^2 := by
      rw [coefficient_exact,jacobi]
      have h := jacobi
      nlinarith only [h]

/-- Sharp positive determinant criterion for the actual canonically repaired seam source. -/
theorem determinant_pos_iff (C t : ℝ) :
    0 < (seamMatrix C t).det ↔
      3*(D*t+borderCofactor)^2 < -2*H*(nativeFourth+C*G*D) := by
  have hp := thetaCuspNativeOddHeadDet_pos 0
  have he := determinant_direction_square C t
  constructor
  · intro hd
    have hm := mul_pos hp hd
    linarith only [he,hm]
  · intro hi
    have hm : 0 < H*(seamMatrix C t).det := by linarith only [he,hi]
    by_contra hn
    exact (not_le_of_gt hm) (mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hn))

/-- Direction with zero canonical seam penalty. -/
def optimalDirection : ℝ := -borderCofactor/D

private theorem optimal_cancellation : D*optimalDirection+borderCofactor=0 := by
  have hd : D ≠ 0 := thetaCuspNativeOddHankelThreeDet_zero_neg.ne
  unfold optimalDirection
  field_simp [hd]
  ring

/-- The source-selected cofactor direction maximizes the corrected seam determinant. -/
theorem determinant_le_optimal (C t : ℝ) :
    (seamMatrix C t).det ≤ (seamMatrix C optimalDirection).det := by
  have hprod : H*(seamMatrix C t).det ≤ H*(seamMatrix C optimalDirection).det := by
    rw [determinant_direction_square,determinant_direction_square,optimal_cancellation]
    nlinarith only [sq_nonneg (D*t+borderCofactor)]
  by_contra hn
  have hd : 0 < (seamMatrix C t).det-(seamMatrix C optimalDirection).det := by
    linarith
  have hm := mul_pos (thetaCuspNativeOddHeadDet_pos 0) hd
  nlinarith only [hprod,hm]

/-- Exact load criterion at the optimal seam direction. -/
theorem optimal_determinant_pos_iff (C : ℝ) :
    0 < (seamMatrix C optimalDirection).det ↔ nativeFourth+C*G*D < 0 := by
  rw [determinant_pos_iff,optimal_cancellation]
  norm_num only [zero_pow (by decide : 2≠0),mul_zero]
  have hp := thetaCuspNativeOddHeadDet_pos 0
  constructor
  · intro h
    by_contra hn
    have hz := mul_nonneg hp.le (le_of_not_gt hn)
    nlinarith only [h,hz]
  · intro h
    have hz := mul_pos hp (neg_pos.mpr h)
    nlinarith only [hz]

private theorem seam_energy_polynomial (C t : ℝ) (c : Fin 4 → ℝ) :
    dotProduct (star c) (Matrix.mulVec (seamMatrix C t) c) =
      symmetricEnergy (sourceMoment 0) (sourceMoment 1) (sourceMoment 2) (sourceMoment 3)
        (sourceMoment 2) (sourceMoment 3) (sourceMoment 4) (sourceMoment 4+S)
        (sourceMoment 5+S*t) (sourceMoment 6+S*t^2+C*G) (c 0) (c 1) (c 2) (c 3) := by
  unfold seamMatrix symmetricEnergy
  norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    show Fin.succ (2 : Fin 3)=(3 : Fin 4) from rfl]
  ring

private theorem seamMatrix_hermitian (C t : ℝ) : (seamMatrix C t).IsHermitian := by
  change (seamMatrix C t).conjTranspose=seamMatrix C t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [seamMatrix,Matrix.conjTranspose]

/-- For the actual canonical source, all preceding principal minors are already positive. -/
theorem posDef_of_determinant_pos (C t : ℝ) (hd : 0 < (seamMatrix C t).det) :
    (seamMatrix C t).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨seamMatrix_hermitian C t,?_⟩
  intro c hc
  rw [seam_energy_polynomial]
  apply symmetricEnergy_pos
  · simpa [sourceMoment] using (thetaCuspNativeOddHankelThree_head_pos 0).1
  · rw [head_eq]
    exact thetaCuspNativeOddHeadDet_pos 0
  · have he : sourceMoment 0*sourceMoment 2*(sourceMoment 4+S)-
        sourceMoment 0*(sourceMoment 3)^2-(sourceMoment 1)^2*(sourceMoment 4+S)+
        2*sourceMoment 1*sourceMoment 2*sourceMoment 3-(sourceMoment 2)^2*sourceMoment 2 =
          D+S*H := by
      rw [← head_eq,← three_eq]
      ring
    rw [he,coefficient_exact]
    have hn := thetaCuspNativeOddHankelThreeDet_zero_neg
    linarith
  · have he : symmetricDet (sourceMoment 0) (sourceMoment 1) (sourceMoment 2) (sourceMoment 3)
        (sourceMoment 2) (sourceMoment 3) (sourceMoment 4) (sourceMoment 4+S)
        (sourceMoment 5+S*t) (sourceMoment 6+S*t^2+C*G)=(seamMatrix C t).det := by
      rw [det_eq,← head_eq,← three_eq]
      unfold symmetricDet nativeFourth A borderCofactor hankelFourDet
      ring
    rw [he]
    exact hd
  · intro h0 h1 h2 h3
    apply hc
    funext i
    fin_cases i <;> assumption

/-- The determinant criterion characterizes strict positivity of the whole literal source form. -/
theorem posDef_iff_determinant_pos (C t : ℝ) :
    (seamMatrix C t).PosDef ↔ 0 < (seamMatrix C t).det :=
  ⟨fun h => h.det_pos,posDef_of_determinant_pos C t⟩

end
end RHTower.ThetaCuspCoupledSeamDirection
