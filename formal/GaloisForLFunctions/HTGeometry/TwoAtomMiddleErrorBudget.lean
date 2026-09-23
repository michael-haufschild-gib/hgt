import GaloisForLFunctions.HTGeometry.TwoAtomInnerQuadraticAbsorption
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
private def P (k : ℕ) (q : ℝ) := innerEvenErrorPolynomial k q
private def D (q : ℝ) := innerErrorDenominator q
/-- Twice the inner polynomial controls the complete derivative convolution through order twelve. -/
def middleEvenErrorBound (k : ℕ) (q : ℝ) : ℝ := 2*innerEvenErrorBound k q

private theorem budget_zero {v : ℝ} (hv : 0 ≤ v) : 0 < (1/2000000)*(D (5+v))^(2 : ℕ)-(2*P 0 (5+v)*D (5+v)) := by
  dsimp [D,P]
  simp only [innerErrorDenominator_eq]
  norm_num [innerEvenErrorPolynomial,innerPartitionErrorCoefficient,
    innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerDeepCoefficient,
    innerFirstMomentCeiling,Finset.sum_range_succ,Nat.choose]
  apply sub_pos.mp
  ring_nf
  positivity

/-- Strict middle-interval coordinate budget. -/
theorem middleEvenErrorBound_zero {q : ℝ} (hq : 5 ≤ q) :
    middleEvenErrorBound 0 q < 1/2000000 := by
  have hd : 0 < D q := by
    have h := innerErrorDenominator_lower (q:=q) (by linarith)
    dsimp [D]
    linarith
  have h := budget_zero (v:=q-5) (by linarith)
  rw [show (5 : ℝ)+(q-5)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : (1/2000000)-(middleEvenErrorBound 0 q) = ((1/2000000)*(D q)^(2 : ℕ)-(2*P 0 q*D q))/(D q)^(2 : ℕ) := by
    simp only [middleEvenErrorBound,innerEvenErrorBound_eq,P,D]
    field_simp [show innerErrorDenominator q ≠ 0 from hd.ne']
    all_goals ring
  rw [← he] at hp
  linarith only [hp]

private theorem budget_one {v : ℝ} (hv : 0 ≤ v) : 0 < (1/40000)*(D (5+v))^(2 : ℕ)-(2*P 2 (5+v)*D (5+v)+32000000*(P 1 (5+v))^(2 : ℕ)) := by
  dsimp [D,P]
  simp only [innerErrorDenominator_eq]
  norm_num [innerEvenErrorPolynomial,innerPartitionErrorCoefficient,
    innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerDeepCoefficient,
    innerFirstMomentCeiling,Finset.sum_range_succ,Nat.choose]
  apply sub_pos.mp
  ring_nf
  positivity

/-- Strict middle-interval coordinate budget. -/
theorem middleEvenErrorBound_one {q : ℝ} (hq : 5 ≤ q) :
    middleEvenErrorBound 2 q+8000000*(middleEvenErrorBound 1 q)^(2 : ℕ) < 1/40000 := by
  have hd : 0 < D q := by
    have h := innerErrorDenominator_lower (q:=q) (by linarith)
    dsimp [D]
    linarith
  have h := budget_one (v:=q-5) (by linarith)
  rw [show (5 : ℝ)+(q-5)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : (1/40000)-(middleEvenErrorBound 2 q+8000000*(middleEvenErrorBound 1 q)^(2 : ℕ)) = ((1/40000)*(D q)^(2 : ℕ)-(2*P 2 q*D q+32000000*(P 1 q)^(2 : ℕ)))/(D q)^(2 : ℕ) := by
    simp only [middleEvenErrorBound,innerEvenErrorBound_eq,P,D]
    field_simp [show innerErrorDenominator q ≠ 0 from hd.ne']
    all_goals ring
  rw [← he] at hp
  linarith only [hp]

private theorem budget_two {v : ℝ} (hv : 0 ≤ v) : 0 < (1/20)*(D (5+v))^(2 : ℕ)-(2*P 4 (5+v)*D (5+v)+32000000*(P 2 (5+v))^(2 : ℕ)+160000*(P 3 (5+v))^(2 : ℕ)) := by
  dsimp [D,P]
  simp only [innerErrorDenominator_eq]
  norm_num [innerEvenErrorPolynomial,innerPartitionErrorCoefficient,
    innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerDeepCoefficient,
    innerFirstMomentCeiling,Finset.sum_range_succ,Nat.choose]
  apply sub_pos.mp
  ring_nf
  positivity

/-- Strict middle-interval coordinate budget. -/
theorem middleEvenErrorBound_two {q : ℝ} (hq : 5 ≤ q) :
    middleEvenErrorBound 4 q+8000000*(middleEvenErrorBound 2 q)^(2 : ℕ)+40000*(middleEvenErrorBound 3 q)^(2 : ℕ) < 1/20 := by
  have hd : 0 < D q := by
    have h := innerErrorDenominator_lower (q:=q) (by linarith)
    dsimp [D]
    linarith
  have h := budget_two (v:=q-5) (by linarith)
  rw [show (5 : ℝ)+(q-5)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : (1/20)-(middleEvenErrorBound 4 q+8000000*(middleEvenErrorBound 2 q)^(2 : ℕ)+40000*(middleEvenErrorBound 3 q)^(2 : ℕ)) = ((1/20)*(D q)^(2 : ℕ)-(2*P 4 q*D q+32000000*(P 2 q)^(2 : ℕ)+160000*(P 3 q)^(2 : ℕ)))/(D q)^(2 : ℕ) := by
    simp only [middleEvenErrorBound,innerEvenErrorBound_eq,P,D]
    field_simp [show innerErrorDenominator q ≠ 0 from hd.ne']
    all_goals ring
  rw [← he] at hp
  linarith only [hp]

private theorem budget_three {v : ℝ} (hv : 0 ≤ v) : 0 < (1)*(D (5+v))^(2 : ℕ)-(2*P 6 (5+v)*D (5+v)+16000000*(P 3 (5+v))^(2 : ℕ)+80000*(P 4 (5+v))^(2 : ℕ)+80*(P 5 (5+v))^(2 : ℕ)) := by
  dsimp [D,P]
  simp only [innerErrorDenominator_eq]
  norm_num [innerEvenErrorPolynomial,innerPartitionErrorCoefficient,
    innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerDeepCoefficient,
    innerFirstMomentCeiling,Finset.sum_range_succ,Nat.choose]
  apply sub_pos.mp
  ring_nf
  positivity

/-- Strict middle-interval coordinate budget. -/
theorem middleEvenErrorBound_three {q : ℝ} (hq : 5 ≤ q) :
    middleEvenErrorBound 6 q+4000000*(middleEvenErrorBound 3 q)^(2 : ℕ)+20000*(middleEvenErrorBound 4 q)^(2 : ℕ)+20*(middleEvenErrorBound 5 q)^(2 : ℕ) < 1 := by
  have hd : 0 < D q := by
    have h := innerErrorDenominator_lower (q:=q) (by linarith)
    dsimp [D]
    linarith
  have h := budget_three (v:=q-5) (by linarith)
  rw [show (5 : ℝ)+(q-5)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : (1)-(middleEvenErrorBound 6 q+4000000*(middleEvenErrorBound 3 q)^(2 : ℕ)+20000*(middleEvenErrorBound 4 q)^(2 : ℕ)+20*(middleEvenErrorBound 5 q)^(2 : ℕ)) = ((1)*(D q)^(2 : ℕ)-(2*P 6 q*D q+16000000*(P 3 q)^(2 : ℕ)+80000*(P 4 q)^(2 : ℕ)+80*(P 5 q)^(2 : ℕ)))/(D q)^(2 : ℕ) := by
    simp only [middleEvenErrorBound,innerEvenErrorBound_eq,P,D]
    field_simp [show innerErrorDenominator q ≠ 0 from hd.ne']
    all_goals ring
  rw [← he] at hp
  linarith only [hp]

/-- Previously proved complete derivative coefficients through order twelve. -/
def middleDeepCoefficient (n : ℕ) : ℝ := if n ≤ 10 then 1 else 5/4
def middlePartitionDeepCoefficient (n : ℕ) : ℝ := middleDeepCoefficient n*16^n
def middlePartitionErrorCoefficient (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
    (innerPartitionKeptCoefficient i*middlePartitionDeepCoefficient (n-i)+
      middlePartitionDeepCoefficient i*innerPartitionKeptCoefficient (n-i)+
      middlePartitionDeepCoefficient i*middlePartitionDeepCoefficient (n-i)/22000000000)

theorem middleDeepCoefficient_nonneg (n : ℕ) : 0 ≤ middleDeepCoefficient n := by
  unfold middleDeepCoefficient
  split <;> norm_num

theorem middlePartitionDeepCoefficient_nonneg (n : ℕ) : 0 ≤ middlePartitionDeepCoefficient n := by
  unfold middlePartitionDeepCoefficient
  exact mul_nonneg (middleDeepCoefficient_nonneg n) (by positivity)

private theorem middle_c_le (n : ℕ) : middleDeepCoefficient n ≤ 2*innerDeepCoefficient n := by
  unfold middleDeepCoefficient innerDeepCoefficient
  split_ifs <;> norm_num

private theorem middle_c_mul_le {i j : ℕ} (hij : i+j ≤ 12) :
    middleDeepCoefficient i*middleDeepCoefficient j ≤ 2*innerDeepCoefficient i*innerDeepCoefficient j := by
  unfold middleDeepCoefficient innerDeepCoefficient
  split_ifs <;> norm_num at * <;> omega

private theorem middle_beta_le (n : ℕ) :
    middlePartitionDeepCoefficient n ≤ 2*innerPartitionDeepCoefficient n := by
  have h := mul_le_mul_of_nonneg_right (middle_c_le n) (show (0 : ℝ) ≤ 16^n by positivity)
  dsimp [middlePartitionDeepCoefficient,innerPartitionDeepCoefficient]
  nlinarith only [h]

private theorem middle_beta_mul_le {i j : ℕ} (hij : i+j ≤ 12) :
    middlePartitionDeepCoefficient i*middlePartitionDeepCoefficient j ≤
      2*innerPartitionDeepCoefficient i*innerPartitionDeepCoefficient j := by
  have h := mul_le_mul_of_nonneg_right (middle_c_mul_le hij) (show (0 : ℝ) ≤ 16^i*16^j by positivity)
  dsimp [middlePartitionDeepCoefficient,innerPartitionDeepCoefficient]
  nlinarith only [h]

/-- Total derivative order twelve prevents two large coefficients from occurring together. -/
theorem middlePartitionErrorCoefficient_le_two_inner {n : ℕ} (hn : n ≤ 12) :
    middlePartitionErrorCoefficient n ≤ 2*innerPartitionErrorCoefficient n := by
  unfold middlePartitionErrorCoefficient innerPartitionErrorCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hai : 0 ≤ innerPartitionKeptCoefficient i := by unfold innerPartitionKeptCoefficient; positivity
  have haj : 0 ≤ innerPartitionKeptCoefficient (n-i) := by unfold innerPartitionKeptCoefficient; positivity
  have h1 := mul_le_mul_of_nonneg_left (middle_beta_le (n-i)) hai
  have h2 := mul_le_mul_of_nonneg_right (middle_beta_le i) haj
  have h3 := mul_le_mul_of_nonneg_right (middle_beta_mul_le (i:=i) (j:=n-i) (by omega))
    (by norm_num : (0 : ℝ) ≤ 1/22000000000)
  have hcoef : innerPartitionKeptCoefficient i*middlePartitionDeepCoefficient (n-i)+
      middlePartitionDeepCoefficient i*innerPartitionKeptCoefficient (n-i)+
      middlePartitionDeepCoefficient i*middlePartitionDeepCoefficient (n-i)/22000000000 ≤
      2*(innerPartitionKeptCoefficient i*innerPartitionDeepCoefficient (n-i)+
        innerPartitionDeepCoefficient i*innerPartitionKeptCoefficient (n-i)+
        innerPartitionDeepCoefficient i*innerPartitionDeepCoefficient (n-i)/22000000000) := by
    nlinarith only [h1,h2,h3]
  have hh := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (n.choose i))
  nlinarith only [hh]

private theorem weighted_pair (t a b : ℝ) {W : ℝ} (hW : 0 < W) :
    2*t*|a*b| ≤ a^(2 : ℕ)/W+W*t^(2 : ℕ)*b^(2 : ℕ) := by
  have h := div_nonneg (sq_nonneg (|a|-W*t*|b|)) hW.le
  have he : a^(2 : ℕ)/W+W*t^(2 : ℕ)*b^(2 : ℕ)-2*t*|a*b| = (|a|-W*t*|b|)^(2 : ℕ)/W := by
    rw [abs_mul,show a^(2 : ℕ)=|a|^(2 : ℕ) by rw [sq_abs],show b^(2 : ℕ)=|b|^(2 : ℕ) by rw [sq_abs]]
    field_simp
    all_goals ring
  rw [← he] at h
  linarith only [h]
/-- All sixteen normalized entry-error contributions, with both ordered off-diagonal entries. -/
def middleEvenErrorQuadratic (q x y z w : ℝ) : ℝ :=
  let e := fun k => middleEvenErrorBound k q
  e 0*x^(2 : ℕ)+2*e 1*|x*y|+2*e 2*|x*z|+2*e 3*|x*w|+
    e 2*y^(2 : ℕ)+2*e 3*|y*z|+2*e 4*|y*w|+e 4*z^(2 : ℕ)+2*e 5*|z*w|+e 6*w^(2 : ℕ)
/-- Coordinate reserve after charging the complete middle compensation. -/
def middleEvenCoordinateReserve (_q x y z w : ℝ) : ℝ :=
  x^(2 : ℕ)/1000000+y^(2 : ℕ)/10000+z^(2 : ℕ)/10+
    w^(2 : ℕ)
/-- The complete sixteen-entry error is strictly absorbed in every nonzero direction. -/
theorem middleEvenErrorQuadratic_lt_reserve {q : ℝ} (hq : 5 ≤ q)
    (x y z w : ℝ) (hc : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) :
    middleEvenErrorQuadratic q x y z w < middleEvenCoordinateReserve q x y z w := by
  let e := fun k => middleEvenErrorBound k q
  let d : ℝ := 1
  let A : ℝ := e 0+1/2000000
  let B : ℝ := e 2+8000000*(e 1)^(2 : ℕ)+3/40000
  let C : ℝ := e 4+8000000*(e 2)^(2 : ℕ)+40000*(e 3)^(2 : ℕ)+1/20
  let D : ℝ := e 6+4000000*(e 3)^(2 : ℕ)+20000*(e 4)^(2 : ℕ)+20*(e 5)^(2 : ℕ)
  have hA : A < 1/1000000 := by
    have h := middleEvenErrorBound_zero hq
    dsimp [A,e]; linarith
  have hB : B < 1/10000 := by
    have h := middleEvenErrorBound_one hq
    dsimp [B,e]; linarith
  have hC : C < 1/10 := by
    have h := middleEvenErrorBound_two hq
    dsimp [C,e]; linarith
  have hD : D < d := by
    exact middleEvenErrorBound_three hq
  have h01 := weighted_pair (e 1) x y (W:=8000000) (by norm_num)
  have h02 := weighted_pair (e 2) x z (W:=8000000) (by norm_num)
  have h03 := weighted_pair (e 3) x w (W:=4000000) (by norm_num)
  have h12 := weighted_pair (e 3) y z (W:=40000) (by norm_num)
  have h13 := weighted_pair (e 4) y w (W:=20000) (by norm_num)
  have h23 := weighted_pair (e 5) z w (W:=20) (by norm_num)
  have hsum : middleEvenErrorQuadratic q x y z w ≤ A*x^(2 : ℕ)+B*y^(2 : ℕ)+C*z^(2 : ℕ)+D*w^(2 : ℕ) := by
    dsimp [middleEvenErrorQuadratic,A,B,C,D,e] at *
    nlinarith only [h01,h02,h03,h12,h13,h23]
  have hAp : 0 < 1/1000000-A := by linarith
  have hBp : 0 < 1/10000-B := by linarith
  have hCp : 0 < 1/10-C := by linarith
  have hDp : 0 < d-D := by linarith
  have hgap : 0 < (1/1000000-A)*x^(2 : ℕ)+(1/10000-B)*y^(2 : ℕ)+(1/10-C)*z^(2 : ℕ)+(d-D)*w^(2 : ℕ) := by
    rcases hc with hx | hy | hz | hw
    · have : 0 < x^(2 : ℕ) := sq_pos_of_ne_zero hx
      positivity
    · have : 0 < y^(2 : ℕ) := sq_pos_of_ne_zero hy
      positivity
    · have : 0 < z^(2 : ℕ) := sq_pos_of_ne_zero hz
      positivity
    · have : 0 < w^(2 : ℕ) := sq_pos_of_ne_zero hw
      positivity
  dsimp [middleEvenCoordinateReserve]
  dsimp [d] at hgap
  nlinarith only [hsum,hgap]

/-- The complete middle quadratic uses exactly twice the inner coefficient polynomial. -/
theorem middleEvenErrorQuadratic_eq_two_inner (q x y z w : ℝ) :
    middleEvenErrorQuadratic q x y z w = 2*innerEvenErrorQuadratic q x y z w := by
  unfold middleEvenErrorQuadratic middleEvenErrorBound innerEvenErrorQuadratic
  ring
end
end HTGeometry
