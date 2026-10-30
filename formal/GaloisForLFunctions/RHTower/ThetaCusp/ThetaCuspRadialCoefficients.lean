import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPairRadialRecurrence

/-!
# Coefficients of the theta-pair radial polynomials

The radial step `P ↦ -4((X² - 4a)(P'' - 2P' + P) + X(P' - P))` acts on coefficients by a
five-term recursion. This gives every radial polynomial as an explicit coefficient table of
length `2k+2`, so its values are finite sums without symbolic polynomial normalization.
-/

open Polynomial
namespace RHTower
noncomputable section

/-- Coefficients of `P'' - 2P' + P` from those of `P`. -/
def radialInnerCoeff (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  (i+2)*(i+1)*p (i+2) - 2*(i+1)*p (i+1) + p i

/-- Coefficients of one radial step. -/
def radialStepCoeff (a : ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => -4*(-(4*a)*radialInnerCoeff p 0)
  | 1 => -4*(-(4*a)*radialInnerCoeff p 1 + (p 1 - p 0))
  | i+2 => -4*(radialInnerCoeff p i - 4*a*radialInnerCoeff p (i+2) + ((i+2)*p (i+2) - p (i+1)))

/-- Coefficient table of the `k`-th radial polynomial. -/
def radialCoeffs (a : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun i => if i = 0 then 4*a+9 else if i = 1 then -6 else 0
  | k+1 => radialStepCoeff a (radialCoeffs a k)

theorem coeff_thetaPairRadialEvenStep (a : ℝ) (P : ℝ[X]) (i : ℕ) :
    (thetaPairRadialEvenStep a P).coeff i = radialStepCoeff a (fun j => P.coeff j) i := by
  have hQ (j : ℕ) : (P.derivative.derivative - C 2*P.derivative + P).coeff j =
      radialInnerCoeff (fun j => P.coeff j) j := by
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_derivative, radialInnerCoeff]
    push_cast
    ring
  have hD (j : ℕ) : (P.derivative - P).coeff j = P.coeff (j+1)*(j+1) - P.coeff j := by
    simp only [coeff_sub, coeff_derivative]
  unfold thetaPairRadialEvenStep
  rcases i with _ | _ | i
  · simp only [coeff_neg, coeff_C_mul, coeff_add, sub_mul, coeff_sub, coeff_X_pow_mul',
      coeff_X_mul_zero, hQ, radialStepCoeff]
    norm_num
  · simp only [coeff_neg, coeff_C_mul, coeff_add, sub_mul, coeff_sub, coeff_X_pow_mul',
      coeff_X_mul, hQ, hD, radialStepCoeff]
    norm_num
  · simp only [coeff_neg, coeff_C_mul, coeff_add, sub_mul, coeff_sub, coeff_X_pow_mul',
      coeff_X_mul, hQ, hD, radialStepCoeff]
    simp only [show 2 ≤ i + 2 from by omega, if_true, show i + 2 - 2 = i from by omega]
    push_cast
    ring

theorem coeff_thetaPairRadialEvenPolynomial (a : ℝ) (k i : ℕ) :
    (thetaPairRadialEvenPolynomial a k).coeff i = radialCoeffs a k i := by
  induction k generalizing i with
  | zero =>
    simp only [thetaPairRadialEvenPolynomial, radialCoeffs, coeff_sub, coeff_C, coeff_C_mul,
      coeff_X]
    rcases i with _ | _ | i <;> simp
  | succ k ih =>
    rw [thetaPairRadialEvenPolynomial, coeff_thetaPairRadialEvenStep, radialCoeffs]
    congr 1
    funext j
    exact ih j

theorem radialCoeffs_eq_zero (a : ℝ) {k i : ℕ} (hi : 2*k+2 ≤ i) : radialCoeffs a k i = 0 := by
  induction k generalizing i with
  | zero =>
    simp only [radialCoeffs]
    rw [if_neg (by omega), if_neg (by omega)]
  | succ k ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    simp only [radialCoeffs, radialStepCoeff, radialInnerCoeff]
    rw [ih (by omega : 2*k+2 ≤ j), ih (by omega : 2*k+2 ≤ j+1), ih (by omega : 2*k+2 ≤ j+2),
      ih (by omega : 2*k+2 ≤ j+2+1), ih (by omega : 2*k+2 ≤ j+2+2)]
    ring

/-- Every radial polynomial is the finite sum of its coefficient table. -/
theorem eval_thetaPairRadialEvenPolynomial (a x : ℝ) (k : ℕ) :
    (thetaPairRadialEvenPolynomial a k).eval x =
      ∑ i ∈ Finset.range (2*k+2), radialCoeffs a k i * x^i := by
  have hdeg : (thetaPairRadialEvenPolynomial a k).natDegree < 2*k+2 := by
    have h : (thetaPairRadialEvenPolynomial a k).natDegree ≤ 2*k+1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_thetaPairRadialEvenPolynomial]
      exact radialCoeffs_eq_zero a (by omega)
    omega
  rw [eval_eq_sum_range' hdeg]
  simp only [coeff_thetaPairRadialEvenPolynomial]


theorem radialStepCoeff_zero (a : ℝ) (p : ℕ → ℝ) :
    radialStepCoeff a p 0 = -4*(-(4*a)*radialInnerCoeff p 0) := rfl

theorem radialStepCoeff_one (a : ℝ) (p : ℕ → ℝ) :
    radialStepCoeff a p 1 = -4*(-(4*a)*radialInnerCoeff p 1 + (p 1 - p 0)) := rfl

theorem radialStepCoeff_add_two (a : ℝ) (p : ℕ → ℝ) (i : ℕ) :
    radialStepCoeff a p (i+2) =
      -4*(radialInnerCoeff p i - 4*a*radialInnerCoeff p (i+2) + ((i+2)*p (i+2) - p (i+1))) := rfl

/-! ### Explicit coefficient tables through order seven -/

theorem radialCoeffs_0_0 (a : ℝ) : radialCoeffs a 0 0 = (9 : ℝ) * a ^ 0 + (4 : ℝ) * a ^ 1 := by
  simp [radialCoeffs]
  ring

theorem radialCoeffs_0_1 (a : ℝ) : radialCoeffs a 0 1 = (-6 : ℝ) * a ^ 0 := by
  simp [radialCoeffs]

theorem radialCoeffs_1_0 (a : ℝ) :
    radialCoeffs a 1 0 = (336 : ℝ) * a ^ 1 + (64 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 1 0 = radialStepCoeff a (radialCoeffs a 0) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_0_0 a, radialCoeffs_0_1 a, radialCoeffs_eq_zero a (show 2*0+2 ≤ 2 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_1_1 (a : ℝ) :
    radialCoeffs a 1 1 = (60 : ℝ) * a ^ 0 + (-80 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 1 1 = radialStepCoeff a (radialCoeffs a 0) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_0_0 a, radialCoeffs_0_1 a, radialCoeffs_eq_zero a (show 2*0+2 ≤ 2 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 3 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_1_2 (a : ℝ) :
    radialCoeffs a 1 2 = (-108 : ℝ) * a ^ 0 + (-16 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 1 2 = radialStepCoeff a (radialCoeffs a 0) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_0_0 a, radialCoeffs_0_1 a, radialCoeffs_eq_zero a (show 2*0+2 ≤ 2 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 3 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 4 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_1_3 (a : ℝ) :
    radialCoeffs a 1 3 = (24 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 1 3 = radialStepCoeff a (radialCoeffs a 0) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_0_1 a, radialCoeffs_eq_zero a (show 2*0+2 ≤ 2 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 3 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 4 by norm_num), radialCoeffs_eq_zero a (show 2*0+2 ≤ 5 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_2_0 (a : ℝ) :
    radialCoeffs a 2 0 = (-5376 : ℝ) * a ^ 1 + (7424 : ℝ) * a ^ 2 + (1024 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 2 0 = radialStepCoeff a (radialCoeffs a 1) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_0 a, radialCoeffs_1_1 a, radialCoeffs_1_2 a]
  push_cast
  ring

theorem radialCoeffs_2_1 (a : ℝ) :
    radialCoeffs a 2 1 = (-240 : ℝ) * a ^ 0 + (11840 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 2 1 = radialStepCoeff a (radialCoeffs a 1) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_0 a, radialCoeffs_1_1 a, radialCoeffs_1_2 a, radialCoeffs_1_3 a]
  push_cast
  ring

theorem radialCoeffs_2_2 (a : ℝ) :
    radialCoeffs a 2 2 = (2448 : ℝ) * a ^ 0 + (-6080 : ℝ) * a ^ 1 + (-512 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 2 2 = radialStepCoeff a (radialCoeffs a 1) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_0 a, radialCoeffs_1_1 a, radialCoeffs_1_2 a, radialCoeffs_1_3 a, radialCoeffs_eq_zero a (show 2*1+2 ≤ 4 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_2_3 (a : ℝ) :
    radialCoeffs a 2 3 = (-3264 : ℝ) * a ^ 0 + (384 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 2 3 = radialStepCoeff a (radialCoeffs a 1) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_1 a, radialCoeffs_1_2 a, radialCoeffs_1_3 a, radialCoeffs_eq_zero a (show 2*1+2 ≤ 4 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 5 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_2_4 (a : ℝ) :
    radialCoeffs a 2 4 = (1104 : ℝ) * a ^ 0 + (64 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 2 4 = radialStepCoeff a (radialCoeffs a 1) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_2 a, radialCoeffs_1_3 a, radialCoeffs_eq_zero a (show 2*1+2 ≤ 4 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 5 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 6 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_2_5 (a : ℝ) :
    radialCoeffs a 2 5 = (-96 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 2 5 = radialStepCoeff a (radialCoeffs a 1) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_1_3 a, radialCoeffs_eq_zero a (show 2*1+2 ≤ 4 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 5 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 6 by norm_num), radialCoeffs_eq_zero a (show 2*1+2 ≤ 7 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_3_0 (a : ℝ) :
    radialCoeffs a 3 0 = (86016 : ℝ) * a ^ 1 + (-659456 : ℝ) * a ^ 2 + (102400 : ℝ) * a ^ 3 + (16384 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 3 0 = radialStepCoeff a (radialCoeffs a 2) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_0 a, radialCoeffs_2_1 a, radialCoeffs_2_2 a]
  push_cast
  ring

theorem radialCoeffs_3_1 (a : ℝ) :
    radialCoeffs a 3 1 = (960 : ℝ) * a ^ 0 + (-542720 : ℝ) * a ^ 1 + (645120 : ℝ) * a ^ 2 + (36864 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 3 1 = radialStepCoeff a (radialCoeffs a 2) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_0 a, radialCoeffs_2_1 a, radialCoeffs_2_2 a, radialCoeffs_2_3 a]
  push_cast
  ring

theorem radialCoeffs_3_2 (a : ℝ) :
    radialCoeffs a 3 2 = (-42048 : ℝ) * a ^ 0 + (825344 : ℝ) * a ^ 1 + (-143360 : ℝ) * a ^ 2 + (-12288 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 3 2 = radialStepCoeff a (radialCoeffs a 2) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_0 a, radialCoeffs_2_1 a, radialCoeffs_2_2 a, radialCoeffs_2_3 a, radialCoeffs_2_4 a]
  push_cast
  ring

theorem radialCoeffs_3_3 (a : ℝ) :
    radialCoeffs a 3 3 = (167424 : ℝ) * a ^ 0 + (-407040 : ℝ) * a ^ 1 + (-12288 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 3 3 = radialStepCoeff a (radialCoeffs a 2) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_1 a, radialCoeffs_2_2 a, radialCoeffs_2_3 a, radialCoeffs_2_4 a, radialCoeffs_2_5 a]
  push_cast
  ring

theorem radialCoeffs_3_4 (a : ℝ) :
    radialCoeffs a 3 4 = (-171840 : ℝ) * a ^ 0 + (64000 : ℝ) * a ^ 1 + (3072 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 3 4 = radialStepCoeff a (radialCoeffs a 2) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_2 a, radialCoeffs_2_3 a, radialCoeffs_2_4 a, radialCoeffs_2_5 a, radialCoeffs_eq_zero a (show 2*2+2 ≤ 6 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_3_5 (a : ℝ) :
    radialCoeffs a 3 5 = (62400 : ℝ) * a ^ 0 + (-768 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 3 5 = radialStepCoeff a (radialCoeffs a 2) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_3 a, radialCoeffs_2_4 a, radialCoeffs_2_5 a, radialCoeffs_eq_zero a (show 2*2+2 ≤ 6 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 7 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_3_6 (a : ℝ) :
    radialCoeffs a 3 6 = (-8640 : ℝ) * a ^ 0 + (-256 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 3 6 = radialStepCoeff a (radialCoeffs a 2) (4 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_4 a, radialCoeffs_2_5 a, radialCoeffs_eq_zero a (show 2*2+2 ≤ 6 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 7 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 8 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_3_7 (a : ℝ) :
    radialCoeffs a 3 7 = (384 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 3 7 = radialStepCoeff a (radialCoeffs a 2) (5 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_2_5 a, radialCoeffs_eq_zero a (show 2*2+2 ≤ 6 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 7 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 8 by norm_num), radialCoeffs_eq_zero a (show 2*2+2 ≤ 9 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_4_0 (a : ℝ) :
    radialCoeffs a 4 0 = (-1376256 : ℝ) * a ^ 1 + (45154304 : ℝ) * a ^ 2 + (-35782656 : ℝ) * a ^ 3 + (65536 : ℝ) * a ^ 4 + (262144 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 4 0 = radialStepCoeff a (radialCoeffs a 3) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_0 a, radialCoeffs_3_1 a, radialCoeffs_3_2 a]
  push_cast
  ring

theorem radialCoeffs_4_1 (a : ℝ) :
    radialCoeffs a 4 1 = (-3840 : ℝ) * a ^ 0 + (21294080 : ℝ) * a ^ 1 + (-105799680 : ℝ) * a ^ 2 + (18579456 : ℝ) * a ^ 3 + (1441792 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 4 1 = radialStepCoeff a (radialCoeffs a 3) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_0 a, radialCoeffs_3_1 a, radialCoeffs_3_2 a, radialCoeffs_3_3 a]
  push_cast
  ring

theorem radialCoeffs_4_2 (a : ℝ) :
    radialCoeffs a 4 2 = (684288 : ℝ) * a ^ 0 + (-69800960 : ℝ) * a ^ 1 + (77242368 : ℝ) * a ^ 2 + (-294912 : ℝ) * a ^ 3 + (-262144 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 4 2 = radialStepCoeff a (radialCoeffs a 3) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_0 a, radialCoeffs_3_1 a, radialCoeffs_3_2 a, radialCoeffs_3_3 a, radialCoeffs_3_4 a]
  push_cast
  ring

theorem radialCoeffs_4_3 (a : ℝ) :
    radialCoeffs a 4 3 = (-6872064 : ℝ) * a ^ 0 + (77973504 : ℝ) * a ^ 1 + (-19955712 : ℝ) * a ^ 2 + (-983040 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 4 3 = radialStepCoeff a (radialCoeffs a 3) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_1 a, radialCoeffs_3_2 a, radialCoeffs_3_3 a, radialCoeffs_3_4 a, radialCoeffs_3_5 a]
  push_cast
  ring

theorem radialCoeffs_4_4 (a : ℝ) :
    radialCoeffs a 4 4 = (15853824 : ℝ) * a ^ 0 + (-35675136 : ℝ) * a ^ 1 + (1056768 : ℝ) * a ^ 2 + (98304 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 4 4 = radialStepCoeff a (radialCoeffs a 3) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_2 a, radialCoeffs_3_3 a, radialCoeffs_3_4 a, radialCoeffs_3_5 a, radialCoeffs_3_6 a]
  push_cast
  ring

theorem radialCoeffs_4_5 (a : ℝ) :
    radialCoeffs a 4 5 = (-13095936 : ℝ) * a ^ 0 + (6924288 : ℝ) * a ^ 1 + (196608 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 4 5 = radialStepCoeff a (radialCoeffs a 3) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_3 a, radialCoeffs_3_4 a, radialCoeffs_3_5 a, radialCoeffs_3_6 a, radialCoeffs_3_7 a]
  push_cast
  ring

theorem radialCoeffs_4_6 (a : ℝ) :
    radialCoeffs a 4 6 = (4677120 : ℝ) * a ^ 0 + (-477184 : ℝ) * a ^ 1 + (-16384 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 4 6 = radialStepCoeff a (radialCoeffs a 3) (4 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_4 a, radialCoeffs_3_5 a, radialCoeffs_3_6 a, radialCoeffs_3_7 a, radialCoeffs_eq_zero a (show 2*3+2 ≤ 8 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_4_7 (a : ℝ) :
    radialCoeffs a 4 7 = (-774144 : ℝ) * a ^ 0 + (-4096 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 4 7 = radialStepCoeff a (radialCoeffs a 3) (5 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_5 a, radialCoeffs_3_6 a, radialCoeffs_3_7 a, radialCoeffs_eq_zero a (show 2*3+2 ≤ 8 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 9 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_4_8 (a : ℝ) :
    radialCoeffs a 4 8 = (57600 : ℝ) * a ^ 0 + (1024 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 4 8 = radialStepCoeff a (radialCoeffs a 3) (6 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_6 a, radialCoeffs_3_7 a, radialCoeffs_eq_zero a (show 2*3+2 ≤ 8 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 9 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 10 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_4_9 (a : ℝ) :
    radialCoeffs a 4 9 = (-1536 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 4 9 = radialStepCoeff a (radialCoeffs a 3) (7 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_3_7 a, radialCoeffs_eq_zero a (show 2*3+2 ≤ 8 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 9 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 10 by norm_num), radialCoeffs_eq_zero a (show 2*3+2 ≤ 11 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_5_0 (a : ℝ) :
    radialCoeffs a 5 0 = (22020096 : ℝ) * a ^ 1 + (-2937061376 : ℝ) * a ^ 2 + (6579814400 : ℝ) * a ^ 3 + (-1176502272 : ℝ) * a ^ 4 + (-53477376 : ℝ) * a ^ 5 + (4194304 : ℝ) * a ^ 6 := by
  rw [show radialCoeffs a 5 0 = radialStepCoeff a (radialCoeffs a 4) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_0 a, radialCoeffs_4_1 a, radialCoeffs_4_2 a]
  push_cast
  ring

theorem radialCoeffs_5_1 (a : ℝ) :
    radialCoeffs a 5 1 = (15360 : ℝ) * a ^ 0 + (-794255360 : ℝ) * a ^ 1 + (12897239040 : ℝ) * a ^ 2 + (-8769503232 : ℝ) * a ^ 3 + (216268800 : ℝ) * a ^ 4 + (40894464 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 5 1 = radialStepCoeff a (radialCoeffs a 4) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_0 a, radialCoeffs_4_1 a, radialCoeffs_4_2 a, radialCoeffs_4_3 a]
  push_cast
  ring

theorem radialCoeffs_5_2 (a : ℝ) :
    radialCoeffs a 5 2 = (-10994688 : ℝ) * a ^ 0 + (5092450304 : ℝ) * a ^ 1 + (-18137989120 : ℝ) * a ^ 2 + (3725328384 : ℝ) * a ^ 3 + (129761280 : ℝ) * a ^ 4 + (-5242880 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 5 2 = radialStepCoeff a (radialCoeffs a 4) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_0 a, radialCoeffs_4_1 a, radialCoeffs_4_2 a, radialCoeffs_4_3 a, radialCoeffs_4_4 a]
  push_cast
  ring

theorem radialCoeffs_5_3 (a : ℝ) :
    radialCoeffs a 5 3 = (261095424 : ℝ) * a ^ 0 + (-10618183680 : ℝ) * a ^ 1 + (10716217344 : ℝ) * a ^ 2 + (-436469760 : ℝ) * a ^ 3 + (-39321600 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 5 3 = radialStepCoeff a (radialCoeffs a 4) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_1 a, radialCoeffs_4_2 a, radialCoeffs_4_3 a, radialCoeffs_4_4 a, radialCoeffs_4_5 a]
  push_cast
  ring

theorem radialCoeffs_5_4 (a : ℝ) :
    radialCoeffs a 5 4 = (-1209799680 : ℝ) * a ^ 0 + (9339699200 : ℝ) * a ^ 1 + (-2843099136 : ℝ) * a ^ 2 + (-55050240 : ℝ) * a ^ 3 + (2621440 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 5 4 = radialStepCoeff a (radialCoeffs a 4) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_2 a, radialCoeffs_4_3 a, radialCoeffs_4_4 a, radialCoeffs_4_5 a, radialCoeffs_4_6 a]
  push_cast
  ring

theorem radialCoeffs_5_5 (a : ℝ) :
    radialCoeffs a 5 5 = (1907819520 : ℝ) * a ^ 0 + (-3916394496 : ℝ) * a ^ 1 + (297861120 : ℝ) * a ^ 2 + (13762560 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 5 5 = radialStepCoeff a (radialCoeffs a 4) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_3 a, radialCoeffs_4_4 a, radialCoeffs_4_5 a, radialCoeffs_4_6 a, radialCoeffs_4_7 a]
  push_cast
  ring

theorem radialCoeffs_5_6 (a : ℝ) :
    radialCoeffs a 5 6 = (-1313141760 : ℝ) * a ^ 0 + (815935488 : ℝ) * a ^ 1 + (983040 : ℝ) * a ^ 2 + (-655360 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 5 6 = radialStepCoeff a (radialCoeffs a 4) (4 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_4 a, radialCoeffs_4_5 a, radialCoeffs_4_6 a, radialCoeffs_4_7 a, radialCoeffs_4_8 a]
  push_cast
  ring

theorem radialCoeffs_5_7 (a : ℝ) :
    radialCoeffs a 5 7 = (447326208 : ℝ) * a ^ 0 + (-80609280 : ℝ) * a ^ 1 + (-1966080 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 5 7 = radialStepCoeff a (radialCoeffs a 4) (5 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_5 a, radialCoeffs_4_6 a, radialCoeffs_4_7 a, radialCoeffs_4_8 a, radialCoeffs_4_9 a]
  push_cast
  ring

theorem radialCoeffs_5_8 (a : ℝ) :
    radialCoeffs a 5 8 = (-79902720 : ℝ) * a ^ 0 + (2764800 : ℝ) * a ^ 1 + (81920 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 5 8 = radialStepCoeff a (radialCoeffs a 4) (6 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_6 a, radialCoeffs_4_7 a, radialCoeffs_4_8 a, radialCoeffs_4_9 a, radialCoeffs_eq_zero a (show 2*4+2 ≤ 10 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_5_9 (a : ℝ) :
    radialCoeffs a 5 9 = (7511040 : ℝ) * a ^ 0 + (61440 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 5 9 = radialStepCoeff a (radialCoeffs a 4) (7 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_7 a, radialCoeffs_4_8 a, radialCoeffs_4_9 a, radialCoeffs_eq_zero a (show 2*4+2 ≤ 10 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 11 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_5_10 (a : ℝ) :
    radialCoeffs a 5 10 = (-347136 : ℝ) * a ^ 0 + (-4096 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 5 10 = radialStepCoeff a (radialCoeffs a 4) (8 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_8 a, radialCoeffs_4_9 a, radialCoeffs_eq_zero a (show 2*4+2 ≤ 10 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 11 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 12 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_5_11 (a : ℝ) :
    radialCoeffs a 5 11 = (6144 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 5 11 = radialStepCoeff a (radialCoeffs a 4) (9 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_4_9 a, radialCoeffs_eq_zero a (show 2*4+2 ≤ 10 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 11 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 12 by norm_num), radialCoeffs_eq_zero a (show 2*4+2 ≤ 13 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_6_0 (a : ℝ) :
    radialCoeffs a 6 0 = (-352321536 : ℝ) * a ^ 1 + (188726902784 : ℝ) * a ^ 2 + (-1040120283136 : ℝ) * a ^ 3 + (505111642112 : ℝ) * a ^ 4 + (-21592276992 : ℝ) * a ^ 5 + (-2332033024 : ℝ) * a ^ 6 + (67108864 : ℝ) * a ^ 7 := by
  rw [show radialCoeffs a 6 0 = radialStepCoeff a (radialCoeffs a 5) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_0 a, radialCoeffs_5_1 a, radialCoeffs_5_2 a]
  push_cast
  ring

theorem radialCoeffs_6_1 (a : ℝ) :
    radialCoeffs a 6 1 = (-61440 : ℝ) * a ^ 0 + (29034168320 : ℝ) * a ^ 1 + (-1421307740160 : ℝ) * a ^ 2 + (2457341263872 : ℝ) * a ^ 3 + (-426205249536 : ℝ) * a ^ 4 + (-8996782080 : ℝ) * a ^ 5 + (1006632960 : ℝ) * a ^ 6 := by
  rw [show radialCoeffs a 6 1 = radialStepCoeff a (radialCoeffs a 5) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_0 a, radialCoeffs_5_1 a, radialCoeffs_5_2 a, radialCoeffs_5_3 a]
  push_cast
  ring

theorem radialCoeffs_6_2 (a : ℝ) :
    radialCoeffs a 6 2 = (176099328 : ℝ) * a ^ 0 + (-348620963840 : ℝ) * a ^ 1 + (3350770024448 : ℝ) * a ^ 2 + (-2055998275584 : ℝ) * a ^ 3 + (96161759232 : ℝ) * a ^ 4 + (7142899712 : ℝ) * a ^ 5 + (-100663296 : ℝ) * a ^ 6 := by
  rw [show radialCoeffs a 6 2 = radialStepCoeff a (radialCoeffs a 5) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_0 a, radialCoeffs_5_1 a, radialCoeffs_5_2 a, radialCoeffs_5_3 a, radialCoeffs_5_4 a]
  push_cast
  ring

theorem radialCoeffs_6_3 (a : ℝ) :
    radialCoeffs a 6 3 = (-9619390464 : ℝ) * a ^ 0 + (1256814772224 : ℝ) * a ^ 1 + (-3418751238144 : ℝ) * a ^ 2 + (755989217280 : ℝ) * a ^ 3 + (7612661760 : ℝ) * a ^ 4 + (-1233125376 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 6 3 = radialStepCoeff a (radialCoeffs a 5) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_1 a, radialCoeffs_5_2 a, radialCoeffs_5_3 a, radialCoeffs_5_4 a, radialCoeffs_5_5 a]
  push_cast
  ring

theorem radialCoeffs_6_4 (a : ℝ) :
    radialCoeffs a 6 4 = (84781830144 : ℝ) * a ^ 0 + (-1870335655936 : ℝ) * a ^ 1 + (1722271727616 : ℝ) * a ^ 2 + (-116274757632 : ℝ) * a ^ 3 + (-5185208320 : ℝ) * a ^ 4 + (62914560 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 6 4 = radialStepCoeff a (radialCoeffs a 5) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_2 a, radialCoeffs_5_3 a, radialCoeffs_5_4 a, radialCoeffs_5_5 a, radialCoeffs_5_6 a]
  push_cast
  ring

theorem radialCoeffs_6_5 (a : ℝ) :
    radialCoeffs a 6 5 = (-235379122176 : ℝ) * a ^ 0 + (1353592897536 : ℝ) * a ^ 1 + (-448493912064 : ℝ) * a ^ 2 + (1643642880 : ℝ) * a ^ 3 + (597688320 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 6 5 = radialStepCoeff a (radialCoeffs a 5) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_3 a, radialCoeffs_5_4 a, radialCoeffs_5_5 a, radialCoeffs_5_6 a, radialCoeffs_5_7 a]
  push_cast
  ring

theorem radialCoeffs_6_6 (a : ℝ) :
    radialCoeffs a 6 6 = (277875671040 : ℝ) * a ^ 0 + (-519979040768 : ℝ) * a ^ 1 + (57925435392 : ℝ) * a ^ 2 + (1449656320 : ℝ) * a ^ 3 + (-20971520 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 6 6 = radialStepCoeff a (radialCoeffs a 5) (4 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_4 a, radialCoeffs_5_5 a, radialCoeffs_5_6 a, radialCoeffs_5_7 a, radialCoeffs_5_8 a]
  push_cast
  ring

theorem radialCoeffs_6_7 (a : ℝ) :
    radialCoeffs a 6 7 = (-163590586368 : ℝ) * a ^ 0 + (110158675968 : ℝ) * a ^ 1 + (-2681733120 : ℝ) * a ^ 2 + (-141557760 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 6 7 = radialStepCoeff a (radialCoeffs a 5) (5 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_5 a, radialCoeffs_5_6 a, radialCoeffs_5_7 a, radialCoeffs_5_8 a, radialCoeffs_5_9 a]
  push_cast
  ring

theorem radialCoeffs_6_8 (a : ℝ) :
    radialCoeffs a 6 8 = (52547235840 : ℝ) * a ^ 0 + (-12749586432 : ℝ) * a ^ 1 + (-122224640 : ℝ) * a ^ 2 + (3932160 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 6 8 = radialStepCoeff a (radialCoeffs a 5) (6 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_6 a, radialCoeffs_5_7 a, radialCoeffs_5_8 a, radialCoeffs_5_9 a, radialCoeffs_5_10 a]
  push_cast
  ring

theorem radialCoeffs_6_9 (a : ℝ) :
    radialCoeffs a 6 9 = (-9656266752 : ℝ) * a ^ 0 + (732610560 : ℝ) * a ^ 1 + (15728640 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 6 9 = radialStepCoeff a (radialCoeffs a 5) (7 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_7 a, radialCoeffs_5_8 a, radialCoeffs_5_9 a, radialCoeffs_5_10 a, radialCoeffs_5_11 a]
  push_cast
  ring

theorem radialCoeffs_6_10 (a : ℝ) :
    radialCoeffs a 6 10 = (1029304320 : ℝ) * a ^ 0 + (-12468224 : ℝ) * a ^ 1 + (-393216 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 6 10 = radialStepCoeff a (radialCoeffs a 5) (8 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_8 a, radialCoeffs_5_9 a, radialCoeffs_5_10 a, radialCoeffs_5_11 a, radialCoeffs_eq_zero a (show 2*5+2 ≤ 12 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_6_11 (a : ℝ) :
    radialCoeffs a 6 11 = (-62177280 : ℝ) * a ^ 0 + (-491520 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 6 11 = radialStepCoeff a (radialCoeffs a 5) (9 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_9 a, radialCoeffs_5_10 a, radialCoeffs_5_11 a, radialCoeffs_eq_zero a (show 2*5+2 ≤ 12 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 13 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_6_12 (a : ℝ) :
    radialCoeffs a 6 12 = (1953792 : ℝ) * a ^ 0 + (16384 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 6 12 = radialStepCoeff a (radialCoeffs a 5) (10 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_10 a, radialCoeffs_5_11 a, radialCoeffs_eq_zero a (show 2*5+2 ≤ 12 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 13 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 14 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_6_13 (a : ℝ) :
    radialCoeffs a 6 13 = (-24576 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 6 13 = radialStepCoeff a (radialCoeffs a 5) (11 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_5_11 a, radialCoeffs_eq_zero a (show 2*5+2 ≤ 12 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 13 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 14 by norm_num), radialCoeffs_eq_zero a (show 2*5+2 ≤ 15 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_7_0 (a : ℝ) :
    radialCoeffs a 7 0 = (5637144576 : ℝ) * a ^ 1 + (-12090601373696 : ℝ) * a ^ 2 + (155726118912000 : ℝ) * a ^ 3 + (-161068789792768 : ℝ) * a ^ 4 + (24797530554368 : ℝ) * a ^ 5 + (170993385472 : ℝ) * a ^ 6 + (-72746008576 : ℝ) * a ^ 7 + (1073741824 : ℝ) * a ^ 8 := by
  rw [show radialCoeffs a 7 0 = radialStepCoeff a (radialCoeffs a 6) 0 from rfl, radialStepCoeff_zero]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_0 a, radialCoeffs_6_1 a, radialCoeffs_6_2 a]
  push_cast
  ring

theorem radialCoeffs_7_1 (a : ℝ) :
    radialCoeffs a 7 1 = (245760 : ℝ) * a ^ 0 + (-1052278784000 : ℝ) * a ^ 1 + (149870645084160 : ℝ) * a ^ 2 + (-579380170457088 : ℝ) * a ^ 3 + (247201582284800 : ℝ) * a ^ 4 + (-12293203034112 : ℝ) * a ^ 5 + (-732828794880 : ℝ) * a ^ 6 + (22817013760 : ℝ) * a ^ 7 := by
  rw [show radialCoeffs a 7 1 = radialStepCoeff a (radialCoeffs a 6) 1 from rfl, radialStepCoeff_one]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_0 a, radialCoeffs_6_1 a, radialCoeffs_6_2 a, radialCoeffs_6_3 a]
  push_cast
  ring

theorem radialCoeffs_7_2 (a : ℝ) :
    radialCoeffs a 7 2 = (-2818326528 : ℝ) * a ^ 0 + (23132145188864 : ℝ) * a ^ 1 + (-556759520378880 : ℝ) * a ^ 2 + (779033159663616 : ℝ) * a ^ 3 + (-136469188444160 : ℝ) * a ^ 4 + (-323666051072 : ℝ) * a ^ 5 + (267764367360 : ℝ) * a ^ 6 + (-1879048192 : ℝ) * a ^ 7 := by
  rw [show radialCoeffs a 7 2 = radialStepCoeff a (radialCoeffs a 6) (0 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_0 a, radialCoeffs_6_1 a, radialCoeffs_6_2 a, radialCoeffs_6_3 a, radialCoeffs_6_4 a]
  push_cast
  ring

theorem radialCoeffs_7_3 (a : ℝ) :
    radialCoeffs a 7 3 = (349820289024 : ℝ) * a ^ 0 + (-138661191352320 : ℝ) * a ^ 1 + (888437403549696 : ℝ) * a ^ 2 + (-496833795194880 : ℝ) * a ^ 3 + (30858962534400 : ℝ) * a ^ 4 + (1200007151616 : ℝ) * a ^ 5 + (-33822867456 : ℝ) * a ^ 6 := by
  rw [show radialCoeffs a 7 3 = radialStepCoeff a (radialCoeffs a 6) (1 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_1 a, radialCoeffs_6_2 a, radialCoeffs_6_3 a, radialCoeffs_6_4 a, radialCoeffs_6_5 a]
  push_cast
  ring

theorem radialCoeffs_7_4 (a : ℝ) :
    radialCoeffs a 7 4 = (-5696084459520 : ℝ) * a ^ 0 + (328684270387200 : ℝ) * a ^ 1 + (-715443679002624 : ℝ) * a ^ 2 + (163952858234880 : ℝ) * a ^ 3 + (-1267183124480 : ℝ) * a ^ 4 + (-255785435136 : ℝ) * a ^ 5 + (1409286144 : ℝ) * a ^ 6 := by
  rw [show radialCoeffs a 7 4 = radialStepCoeff a (radialCoeffs a 6) (2 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_2 a, radialCoeffs_6_3 a, radialCoeffs_6_4 a, radialCoeffs_6_5 a, radialCoeffs_6_6 a]
  push_cast
  ring

theorem radialCoeffs_7_5 (a : ℝ) :
    radialCoeffs a 7 5 = (26628535664640 : ℝ) * a ^ 0 + (-374769701289984 : ℝ) * a ^ 1 + (316046270791680 : ℝ) * a ^ 2 + (-27473923276800 : ℝ) * a ^ 3 + (-624049520640 : ℝ) * a ^ 4 + (20786970624 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 7 5 = radialStepCoeff a (radialCoeffs a 6) (3 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_3 a, radialCoeffs_6_4 a, radialCoeffs_6_5 a, radialCoeffs_6_6 a, radialCoeffs_6_7 a]
  push_cast
  ring

theorem radialCoeffs_7_6 (a : ℝ) :
    radialCoeffs a 7 6 = (-50709905326080 : ℝ) * a ^ 0 + (230089037381632 : ℝ) * a ^ 1 + (-79382919249920 : ℝ) * a ^ 2 + (1746670714880 : ℝ) * a ^ 3 + (108485672960 : ℝ) * a ^ 4 + (-587202560 : ℝ) * a ^ 5 := by
  rw [show radialCoeffs a 7 6 = radialStepCoeff a (radialCoeffs a 6) (4 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_4 a, radialCoeffs_6_5 a, radialCoeffs_6_6 a, radialCoeffs_6_7 a, radialCoeffs_6_8 a]
  push_cast
  ring

theorem radialCoeffs_7_7 (a : ℝ) :
    radialCoeffs a 7 7 = (47454806310912 : ℝ) * a ^ 0 + (-81237943255040 : ℝ) * a ^ 1 + (11202118287360 : ℝ) * a ^ 2 + (103054049280 : ℝ) * a ^ 3 + (-6752829440 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 7 7 = radialStepCoeff a (radialCoeffs a 6) (5 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_5 a, radialCoeffs_6_6 a, radialCoeffs_6_7 a, radialCoeffs_6_8 a, radialCoeffs_6_9 a]
  push_cast
  ring

theorem radialCoeffs_7_8 (a : ℝ) :
    radialCoeffs a 7 8 = (-24379030241280 : ℝ) * a ^ 0 + (17057289666560 : ℝ) * a ^ 1 + (-794255687680 : ℝ) * a ^ 2 + (-22350397440 : ℝ) * a ^ 3 + (146800640 : ℝ) * a ^ 4 := by
  rw [show radialCoeffs a 7 8 = radialStepCoeff a (radialCoeffs a 6) (6 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_6 a, radialCoeffs_6_7 a, radialCoeffs_6_8 a, radialCoeffs_6_9 a, radialCoeffs_6_10 a]
  push_cast
  ring

theorem radialCoeffs_7_9 (a : ℝ) :
    radialCoeffs a 7 9 = (7356204810240 : ℝ) * a ^ 0 + (-2138282065920 : ℝ) * a ^ 1 + (12166103040 : ℝ) * a ^ 2 + (1211105280 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 7 9 = radialStepCoeff a (radialCoeffs a 6) (7 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_7 a, radialCoeffs_6_8 a, radialCoeffs_6_9 a, radialCoeffs_6_10 a, radialCoeffs_6_11 a]
  push_cast
  ring

theorem radialCoeffs_7_10 (a : ℝ) :
    radialCoeffs a 7 10 = (-1355786944512 : ℝ) * a ^ 0 + (154145718272 : ℝ) * a ^ 1 + (1849688064 : ℝ) * a ^ 2 + (-22020096 : ℝ) * a ^ 3 := by
  rw [show radialCoeffs a 7 10 = radialStepCoeff a (radialCoeffs a 6) (8 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_8 a, radialCoeffs_6_9 a, radialCoeffs_6_10 a, radialCoeffs_6_11 a, radialCoeffs_6_12 a]
  push_cast
  ring

theorem radialCoeffs_7_11 (a : ℝ) :
    radialCoeffs a 7 11 = (155180433408 : ℝ) * a ^ 0 + (-5546311680 : ℝ) * a ^ 1 + (-110100480 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 7 11 = radialStepCoeff a (radialCoeffs a 6) (9 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_9 a, radialCoeffs_6_10 a, radialCoeffs_6_11 a, radialCoeffs_6_12 a, radialCoeffs_6_13 a]
  push_cast
  ring

theorem radialCoeffs_7_12 (a : ℝ) :
    radialCoeffs a 7 12 = (-10962911232 : ℝ) * a ^ 0 + (36700160 : ℝ) * a ^ 1 + (1835008 : ℝ) * a ^ 2 := by
  rw [show radialCoeffs a 7 12 = radialStepCoeff a (radialCoeffs a 6) (10 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_10 a, radialCoeffs_6_11 a, radialCoeffs_6_12 a, radialCoeffs_6_13 a, radialCoeffs_eq_zero a (show 2*6+2 ≤ 14 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_7_13 (a : ℝ) :
    radialCoeffs a 7 13 = (460701696 : ℝ) * a ^ 0 + (3211264 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 7 13 = radialStepCoeff a (radialCoeffs a 6) (11 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_11 a, radialCoeffs_6_12 a, radialCoeffs_6_13 a, radialCoeffs_eq_zero a (show 2*6+2 ≤ 14 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 15 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_7_14 (a : ℝ) :
    radialCoeffs a 7 14 = (-10469376 : ℝ) * a ^ 0 + (-65536 : ℝ) * a ^ 1 := by
  rw [show radialCoeffs a 7 14 = radialStepCoeff a (radialCoeffs a 6) (12 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_12 a, radialCoeffs_6_13 a, radialCoeffs_eq_zero a (show 2*6+2 ≤ 14 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 15 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 16 by norm_num)]
  push_cast
  ring

theorem radialCoeffs_7_15 (a : ℝ) :
    radialCoeffs a 7 15 = (98304 : ℝ) * a ^ 0 := by
  rw [show radialCoeffs a 7 15 = radialStepCoeff a (radialCoeffs a 6) (13 + 2) from rfl, radialStepCoeff_add_two]
  simp only [radialInnerCoeff, Nat.reduceAdd, radialCoeffs_6_13 a, radialCoeffs_eq_zero a (show 2*6+2 ≤ 14 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 15 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 16 by norm_num), radialCoeffs_eq_zero a (show 2*6+2 ≤ 17 by norm_num)]
  push_cast
  ring

end
end RHTower
