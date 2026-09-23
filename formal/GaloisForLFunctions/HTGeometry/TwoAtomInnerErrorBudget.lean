import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenFourReserve
/-!
# Complete inner-scale error absorption through degree six

The seven error polynomials retain both ordered mixed derivative products and
the quadratic complete deep-tail product. A Taylor lower bound for exponential
decay gives a positive denominator. Four strict inequalities allocate every
entry to the affine coordinate reserves; the last uses the actual extra source
compensation on the lower subinterval. Literal source admission is separate.
-/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
/-- Retained cancellation coefficient for deep derivatives through twelve. -/
def innerDeepCoefficient (n : ℕ) : ℝ := if n ≤ 5 then 1 else 3/4
/-- Seven absolute first-atom moment ceilings in the q normalization. -/
def innerFirstMomentCeiling (r : ℕ) : ℝ := match r with
  | 0 => 1 | 1 => 11 | 2 => 310 | 3 => 14000
  | 4 => 800000 | 5 => 55000000 | _ => 20000000000
/-- Retained two-atom partition derivative coefficient in powers of q. -/
def innerPartitionKeptCoefficient (n : ℕ) : ℝ := 0^n+6^n/100
/-- Complete deep derivative coefficient in powers of q. -/
def innerPartitionDeepCoefficient (n : ℕ) : ℝ := innerDeepCoefficient n*16^n
/-- Both mixed products and the quadratic deep product after one exponential absorption. -/
def innerPartitionErrorCoefficient (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
    (innerPartitionKeptCoefficient i*innerPartitionDeepCoefficient (n-i)+innerPartitionDeepCoefficient i*innerPartitionKeptCoefficient (n-i)+innerPartitionDeepCoefficient i*innerPartitionDeepCoefficient (n-i)/22000000000)
private def H (k : ℕ) (A B : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (k+1), ((2*k).choose (2*r) : ℝ)*innerFirstMomentCeiling r/8^k*A^(k-r)*B^r*innerPartitionErrorCoefficient (2*(k-r))
private def N (k : ℕ) (A B : ℝ) : ℝ := H k A B*B^(10-k)
private def D (A B : ℝ) : ℝ := 22000000000*∑ j ∈ Finset.range 11,
  (8*(A-(37/10)*B))^j*B^(10-j)/(j.factorial : ℝ)

private theorem budget_zero {v : ℝ} (hv : 0 ≤ v) :
    0 < (1/2000000)*(D (37/10+v) 1)^(2 : ℕ)-N 0 (37/10+v) 1*D (37/10+v) 1 := by
  conv_rhs => norm_num [D,N,H,innerPartitionErrorCoefficient,innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerFirstMomentCeiling,innerDeepCoefficient,Finset.sum_range_succ,Nat.choose]
  ring_nf
  positivity

private theorem budget_one {v : ℝ} (hv : 0 ≤ v) :
    0 < (1/40000)*(D (37/10+v) 1)^(2 : ℕ)-N 2 (37/10+v) 1*D (37/10+v) 1-8000000*(N 1 (37/10+v) 1)^(2 : ℕ) := by
  conv_rhs => norm_num [D,N,H,innerPartitionErrorCoefficient,innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerFirstMomentCeiling,innerDeepCoefficient,Finset.sum_range_succ,Nat.choose]
  ring_nf
  positivity

private theorem budget_two {v : ℝ} (hv : 0 ≤ v) :
    0 < (1/20)*(D (37/10+v) 1)^(2 : ℕ)-N 4 (37/10+v) 1*D (37/10+v) 1-8000000*(N 2 (37/10+v) 1)^(2 : ℕ)-40000*(N 3 (37/10+v) 1)^(2 : ℕ) := by
  conv_rhs => norm_num [D,N,H,innerPartitionErrorCoefficient,innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerFirstMomentCeiling,innerDeepCoefficient,Finset.sum_range_succ,Nat.choose]
  ring_nf
  positivity


private def finalDebt (A B : ℝ) : ℝ :=
  N 6 A B*D A B+4000000*(N 3 A B)^(2 : ℕ)+
    20000*(N 4 A B)^(2 : ℕ)+20*(N 5 A B)^(2 : ℕ)
private def hA (u v : ℝ) : ℝ := 37*u+45*v
private def hB (u v : ℝ) : ℝ := 10*(u+v)
private theorem budget_three_inner {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u+v) :
    let A := hA u v
    let B := hB u v
    0 < ((500*(5*B-A)^(2 : ℕ)+B^(2 : ℕ))*(8*A)^(6 : ℕ)+
       1000000000000*(2/5)*(A-(5/2)*B)*((9/2)*B-A)*B^(6 : ℕ))*(D A B)^(2 : ℕ)-
      (8*A)^(6 : ℕ)*B^(2 : ℕ)*finalDebt A B := by
  dsimp only
  conv_rhs => norm_num [finalDebt,D,N,H,innerPartitionErrorCoefficient,innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerFirstMomentCeiling,innerDeepCoefficient,hA,hB,Finset.sum_range_succ,Nat.choose]
  ring_nf
  rcases lt_or_ge 0 u with hup | hup
  · positivity
  · have hvp : 0 < v := by linarith
    positivity

private def hAUpper (u v : ℝ) : ℝ := 45*u+50*v
private def hBUpper (u v : ℝ) : ℝ := 10*(u+v)
private theorem budget_three_upper {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u+v) :
    let A := hAUpper u v
    let B := hBUpper u v
    0 < (500*(5*B-A)^(2 : ℕ)+B^(2 : ℕ))*(D A B)^(2 : ℕ)-B^(2 : ℕ)*finalDebt A B := by
  dsimp only
  conv_rhs => norm_num [finalDebt,D,N,H,innerPartitionErrorCoefficient,innerPartitionKeptCoefficient,innerPartitionDeepCoefficient,innerFirstMomentCeiling,innerDeepCoefficient,hAUpper,hBUpper,Finset.sum_range_succ,Nat.choose]
  ring_nf
  rcases lt_or_ge 0 u with hup | hup
  · positivity
  · have hvp : 0 < v := by linarith
    positivity

private theorem H_scale (k : ℕ) (q C : ℝ) : H k (C*q) C = C^k*H k q 1 := by
  unfold H
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrk : r ≤ k := by have := Finset.mem_range.mp hr; omega
  have hp : C^(k-r)*C^r = C^k := by rw [← pow_add,Nat.sub_add_cancel hrk]
  simp only [one_pow,mul_one]
  calc
    _ = (((2*k).choose (2*r) : ℝ)*innerFirstMomentCeiling r/8^k)*
      (C^(k-r)*C^r)*q^(k-r)*innerPartitionErrorCoefficient (2*(k-r)) := by rw [mul_pow]; ring
    _ = _ := by rw [hp]; ring
private theorem N_scale {k : ℕ} (hk : k ≤ 10) (q C : ℝ) :
    N k (C*q) C = C^(10 : ℕ)*N k q 1 := by
  unfold N
  rw [H_scale]
  simp only [one_pow,mul_one]
  have hp : C^k*C^(10-k) = C^(10 : ℕ) := by rw [← pow_add,Nat.add_sub_of_le hk]
  calc
    _ = (C^k*C^(10-k))*H k q 1 := by ring
    _ = _ := by rw [hp]
private theorem D_scale (q C : ℝ) : D (C*q) C = C^(10 : ℕ)*D q 1 := by
  unfold D
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj10 : j ≤ 10 := by have := Finset.mem_range.mp hj; omega
  have hp : C^j*C^(10-j) = C^(10 : ℕ) := by rw [← pow_add,Nat.add_sub_of_le hj10]
  have he : 8*(C*q-(37/10)*C)=C*(8*(q-37/10)) := by ring
  rw [he,mul_pow]
  simp only [one_pow,mul_one]
  calc
    _ = (C^j*C^(10-j))*(22000000000*(8*(q-37/10))^j/(j.factorial : ℝ)) := by ring
    _ = _ := by rw [hp]; ring
private theorem finalDebt_scale (q C : ℝ) : finalDebt (C*q) C = C^(20 : ℕ)*finalDebt q 1 := by
  unfold finalDebt
  rw [N_scale (by norm_num),N_scale (by norm_num),N_scale (by norm_num),
    N_scale (by norm_num),D_scale]
  ring


/-- Positive rational denominator retaining inner-scale exponential decay. -/
def innerErrorDenominator (q : ℝ) : ℝ := D q 1
/-- Explicit Taylor denominator, with its constant term retained. -/
theorem innerErrorDenominator_eq (q : ℝ) : innerErrorDenominator q =
    22000000000*∑ j ∈ Finset.range 11, (8*(q-37/10))^j/(j.factorial : ℝ) := by
  simp only [innerErrorDenominator,D,one_pow,mul_one]
/-- Complete convolution error in the first-atom `8q` coordinates. -/
def innerEvenErrorBound (k : ℕ) (q : ℝ) : ℝ := N k q 1 / innerErrorDenominator q
/-- Polynomial numerator for the complete even convolution error. -/
def innerEvenErrorPolynomial (k : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (k+1), ((2*k).choose (2*r) : ℝ)*innerFirstMomentCeiling r/8^k*
    q^(k-r)*innerPartitionErrorCoefficient (2*(k-r))
/-- The cleared homogeneous bound is exactly the physical polynomial ratio. -/
theorem innerEvenErrorBound_eq (k : ℕ) (q : ℝ) :
    innerEvenErrorBound k q = innerEvenErrorPolynomial k q/innerErrorDenominator q := by
  simp only [innerEvenErrorBound,innerEvenErrorPolynomial,N,H,one_pow,mul_one]

/-- Extra complete-source correction available on the lower inner interval. -/
def innerExtraCompensation (q : ℝ) : ℝ :=
  1000000000000*(2/5)*(q-5/2)*(9/2-q)/(8*q)^(6 : ℕ)

theorem innerErrorDenominator_lower {q : ℝ} (hq : 37/10 ≤ q) :
    22000000000 ≤ innerErrorDenominator q := by
  have hv : 0 ≤ 8*(q-37/10) := by linarith
  have h := Finset.single_le_sum
    (f := fun j : ℕ => (8*(q-37/10))^j/(j.factorial : ℝ))
    (fun j hj => by positivity) (by simp : 0 ∈ Finset.range 11)
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at h
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 22000000000)
  simpa only [innerErrorDenominator,D,one_pow,mul_one] using hh

private theorem D_pos {q : ℝ} (hq : 37/10 ≤ q) : 0 < D q 1 := by
  have h := innerErrorDenominator_lower hq
  change 22000000000 ≤ D q 1 at h
  linarith

/-- The mass error leaves its assigned strict reserve. -/
theorem innerEvenErrorBound_zero {q : ℝ} (hq : 37/10 ≤ q) :
    innerEvenErrorBound 0 q < 1/2000000 := by
  have hd := D_pos hq
  have h := budget_zero (v:=q-37/10) (by linarith)
  rw [show (37/10 : ℝ)+(q-37/10)=q by ring] at h
  have hh : 0 < D q 1*((1/2000000)*D q 1-N 0 q 1) := by nlinarith only [h]
  have hg := (mul_pos_iff_of_pos_left hd).mp hh
  unfold innerEvenErrorBound innerErrorDenominator
  apply (div_lt_iff₀ hd).mpr
  nlinarith only [hg]

/-- The second diagonal absorbs its first off-diagonal allocation. -/
theorem innerEvenErrorBound_one {q : ℝ} (hq : 37/10 ≤ q) :
    innerEvenErrorBound 2 q+8000000*(innerEvenErrorBound 1 q)^(2 : ℕ) < 1/40000 := by
  have hd := D_pos hq
  have h := budget_one (v:=q-37/10) (by linarith)
  rw [show (37/10 : ℝ)+(q-37/10)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : 1/40000-(innerEvenErrorBound 2 q+8000000*(innerEvenErrorBound 1 q)^(2 : ℕ)) =
      ((1/40000)*(D q 1)^(2 : ℕ)-N 2 q 1*D q 1-8000000*(N 1 q 1)^(2 : ℕ))/(D q 1)^(2 : ℕ) := by
    unfold innerEvenErrorBound innerErrorDenominator
    field_simp [hd.ne']
    <;> ring
  rw [← he] at hp
  linarith only [hp]

/-- The third diagonal absorbs both lower-coordinate allocations. -/
theorem innerEvenErrorBound_two {q : ℝ} (hq : 37/10 ≤ q) :
    innerEvenErrorBound 4 q+8000000*(innerEvenErrorBound 2 q)^(2 : ℕ)+
      40000*(innerEvenErrorBound 3 q)^(2 : ℕ) < 1/20 := by
  have hd := D_pos hq
  have h := budget_two (v:=q-37/10) (by linarith)
  rw [show (37/10 : ℝ)+(q-37/10)=q by ring] at h
  have hp := div_pos h (pow_pos hd 2)
  have he : 1/20-(innerEvenErrorBound 4 q+8000000*(innerEvenErrorBound 2 q)^(2 : ℕ)+
      40000*(innerEvenErrorBound 3 q)^(2 : ℕ)) =
      ((1/20)*(D q 1)^(2 : ℕ)-N 4 q 1*D q 1-8000000*(N 2 q 1)^(2 : ℕ)-
        40000*(N 3 q 1)^(2 : ℕ))/(D q 1)^(2 : ℕ) := by
    unfold innerEvenErrorBound innerErrorDenominator
    field_simp [hd.ne']
    <;> ring
  rw [← he] at hp
  linarith only [hp]

private theorem debt_ratio {q : ℝ} (hq : 37/10 ≤ q) :
    innerEvenErrorBound 6 q+4000000*(innerEvenErrorBound 3 q)^(2 : ℕ)+
      20000*(innerEvenErrorBound 4 q)^(2 : ℕ)+20*(innerEvenErrorBound 5 q)^(2 : ℕ) =
      finalDebt q 1/(D q 1)^(2 : ℕ) := by
  have hd := D_pos hq
  unfold innerEvenErrorBound innerErrorDenominator finalDebt
  field_simp [hd.ne']

/-- All highest-coordinate losses fit the reserve plus the actual extra correction. -/
theorem innerEvenErrorBound_three_lower {q : ℝ} (hq : 37/10 ≤ q) (hqu : q ≤ 9/2) :
    innerEvenErrorBound 6 q+4000000*(innerEvenErrorBound 3 q)^(2 : ℕ)+
      20000*(innerEvenErrorBound 4 q)^(2 : ℕ)+20*(innerEvenErrorBound 5 q)^(2 : ℕ) <
        500*(5-q)^(2 : ℕ)+1+innerExtraCompensation q := by
  have hd := D_pos hq
  have hqp : 0 < q := by linarith
  have h := budget_three_inner (u:=45-10*q) (v:=10*q-37)
    (by linarith) (by linarith) (by linarith)
  dsimp only at h
  have ha : hA (45-10*q) (10*q-37) = 80*q := by unfold hA; ring
  have hb : hB (45-10*q) (10*q-37) = 80 := by unfold hB; ring
  rw [ha,hb,D_scale,finalDebt_scale] at h
  have he : 0 < (80 : ℝ)^(28 : ℕ)*
      (((500*(5-q)^(2 : ℕ)+1)*(8*q)^(6 : ℕ)+1000000000000*(2/5)*(q-5/2)*(9/2-q))*(D q 1)^(2 : ℕ)-
        (8*q)^(6 : ℕ)*finalDebt q 1) := by convert h using 1 <;> ring
  have hp := (mul_pos_iff_of_pos_left (by positivity)).mp he
  rw [debt_ratio hq]
  apply (div_lt_iff₀ (pow_pos hd 2)).mpr
  apply (mul_lt_mul_iff_right₀ (pow_pos (show 0 < 8*q by positivity) 6)).mp
  have hclear : ((500*(5-q)^(2 : ℕ)+1+innerExtraCompensation q)*(D q 1)^(2 : ℕ))*(8*q)^(6 : ℕ) =
      ((500*(5-q)^(2 : ℕ)+1)*(8*q)^(6 : ℕ)+1000000000000*(2/5)*(q-5/2)*(9/2-q))*(D q 1)^(2 : ℕ) := by
    unfold innerExtraCompensation
    field_simp [hqp.ne']
  nlinarith only [hp,hclear]

/-- The upper inner interval needs no extra compensation in the last reserve. -/
theorem innerEvenErrorBound_three_upper {q : ℝ} (hq : 9/2 ≤ q) (hqu : q ≤ 5) :
    innerEvenErrorBound 6 q+4000000*(innerEvenErrorBound 3 q)^(2 : ℕ)+
      20000*(innerEvenErrorBound 4 q)^(2 : ℕ)+20*(innerEvenErrorBound 5 q)^(2 : ℕ) <
        500*(5-q)^(2 : ℕ)+1 := by
  have hq0 : 37/10 ≤ q := by linarith
  have hd := D_pos hq0
  have h := budget_three_upper (u:=50-10*q) (v:=10*q-45)
    (by linarith) (by linarith) (by linarith)
  dsimp only at h
  have ha : hAUpper (50-10*q) (10*q-45) = 50*q := by unfold hAUpper; ring
  have hb : hBUpper (50-10*q) (10*q-45) = 50 := by unfold hBUpper; ring
  rw [ha,hb,D_scale,finalDebt_scale] at h
  have he : 0 < (50 : ℝ)^(22 : ℕ)*
      ((500*(5-q)^(2 : ℕ)+1)*(D q 1)^(2 : ℕ)-finalDebt q 1) := by convert h using 1 <;> ring
  have hp := (mul_pos_iff_of_pos_left (by positivity)).mp he
  rw [debt_ratio hq0]
  apply (div_lt_iff₀ (pow_pos hd 2)).mpr
  nlinarith only [hp]
end
end HTGeometry
