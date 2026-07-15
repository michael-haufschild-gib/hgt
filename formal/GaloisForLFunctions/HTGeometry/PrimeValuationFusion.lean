import GaloisForLFunctions.HTGeometry.HomogeneousConstraintValuationFunctoriality

/-!
# Prime-valuation fusion

Dirichlet convolution mixes different primes.  Prime valuation also carries a transverse graded
product: it fuses the `p^(e+1)` and `p^(f+1)` entries at the same prime into the
`p^(e+f+2)` entry.  This module proves that the product is bilinear, symmetric, associative, and
that the rotated logarithmic derivation satisfies Leibniz for it.  Homogeneous source
multiplication is represented literally by this fusion product.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction MvPolynomial

noncomputable section

/-- The prime-local graded fusion product.  Only the indicated input valuation layers are read;
their same-prime coefficients are multiplied and placed in the sum valuation layer. -/
def primeValuationFusion (e f : ℕ)
    (A B : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  arithmeticOfPrimePowerColumn (e + f + 1) fun p =>
    A ((p : ℕ) ^ (e + 1)) * B ((p : ℕ) ^ (f + 1))

theorem arithmeticOfPrimePowerColumn_add (e : ℕ)
    (c d : Nat.Primes → ℂ) :
    arithmeticOfPrimePowerColumn e (fun p => c p + d p) =
      arithmeticOfPrimePowerColumn e c + arithmeticOfPrimePowerColumn e d := by
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · obtain ⟨p, rfl⟩ := hpow
    simp
  · simp [arithmeticOfPrimePowerColumn, hpow]

@[simp]
theorem primeValuationFusion_apply (e f : ℕ)
    (A B : ArithmeticFunction ℂ) (p : Nat.Primes) :
    primeValuationFusion e f A B ((p : ℕ) ^ (e + f + 2)) =
      A ((p : ℕ) ^ (e + 1)) * B ((p : ℕ) ^ (f + 1)) := by
  simpa [primeValuationFusion, Nat.add_assoc] using
    arithmeticOfPrimePowerColumn_apply (e + f + 1)
      (fun q => A ((q : ℕ) ^ (e + 1)) * B ((q : ℕ) ^ (f + 1))) p

/-- Fusion of pure columns multiplies their same-prime coefficient profiles. -/
theorem primeValuationFusion_columns (e f : ℕ)
    (c d : Nat.Primes → ℂ) :
    primeValuationFusion e f
        (arithmeticOfPrimePowerColumn e c)
        (arithmeticOfPrimePowerColumn f d) =
      arithmeticOfPrimePowerColumn (e + f + 1) (fun p => c p * d p) := by
  unfold primeValuationFusion
  congr 1
  funext p
  simp

theorem primeValuationFusion_add_left (e f : ℕ)
    (A B C : ArithmeticFunction ℂ) :
    primeValuationFusion e f (A + B) C =
      primeValuationFusion e f A C + primeValuationFusion e f B C := by
  unfold primeValuationFusion
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 1 + 1)
  · obtain ⟨p, rfl⟩ := hpow
    simp [add_mul]
  · simp [arithmeticOfPrimePowerColumn, hpow]

theorem primeValuationFusion_add_right (e f : ℕ)
    (A B C : ArithmeticFunction ℂ) :
    primeValuationFusion e f A (B + C) =
      primeValuationFusion e f A B + primeValuationFusion e f A C := by
  unfold primeValuationFusion
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 1 + 1)
  · obtain ⟨p, rfl⟩ := hpow
    simp [mul_add]
  · simp [arithmeticOfPrimePowerColumn, hpow]

theorem primeValuationFusion_smul_left (e f : ℕ)
    (z : ℂ) (A B : ArithmeticFunction ℂ) :
    primeValuationFusion e f (z • A) B =
      z • primeValuationFusion e f A B := by
  unfold primeValuationFusion
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 1 + 1)
  · obtain ⟨p, rfl⟩ := hpow
    simp [mul_assoc]
  · simp [arithmeticOfPrimePowerColumn, hpow]

theorem primeValuationFusion_comm (e f : ℕ)
    (A B : ArithmeticFunction ℂ) :
    primeValuationFusion e f A B = primeValuationFusion f e B A := by
  rw [primeValuationFusion]
  rw [primeValuationFusion]
  congr 1
  · omega
  · funext p
    exact mul_comm _ _

/-- Valuation fusion is associative when the degree labels are associated with their inputs. -/
theorem primeValuationFusion_assoc (e f g : ℕ)
    (A B C : ArithmeticFunction ℂ) :
    primeValuationFusion (e + f + 1) g
        (primeValuationFusion e f A B) C =
      primeValuationFusion e (f + g + 1) A
        (primeValuationFusion f g B C) := by
  rw [primeValuationFusion]
  rw [primeValuationFusion]
  congr 1
  · omega
  · funext p
    simp [primeValuationFusion_apply, mul_assoc]

/-- The rotated logarithmic derivation is a derivation for prime-valuation fusion. -/
theorem rotatedLogArithmetic_primeValuationFusion_leibniz
    (e f : ℕ) (A B : ArithmeticFunction ℂ) :
    Complex.I • logWeight (primeValuationFusion e f A B) =
      primeValuationFusion e f (Complex.I • logWeight A) B +
        primeValuationFusion e f A (Complex.I • logWeight B) := by
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 2)
  · obtain ⟨p, rfl⟩ := hpow
    simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply,
      primeValuationFusion_apply, ArithmeticFunction.add_apply]
    have he : Real.log ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ)) =
        ((e + 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
      rw [show ((((p : ℕ) ^ (e + 1) : ℕ) : ℝ)) =
          ((p : ℕ) : ℝ) ^ (e + 1) by norm_num, Real.log_pow]
    have hf : Real.log ((((p : ℕ) ^ (f + 1) : ℕ) : ℝ)) =
        ((f + 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
      rw [show ((((p : ℕ) ^ (f + 1) : ℕ) : ℝ)) =
          ((p : ℕ) : ℝ) ^ (f + 1) by norm_num, Real.log_pow]
    have hef : Real.log ((((p : ℕ) ^ (e + f + 2) : ℕ) : ℝ)) =
        ((e + f + 2 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
      rw [show ((((p : ℕ) ^ (e + f + 2) : ℕ) : ℝ)) =
          ((p : ℕ) : ℝ) ^ (e + f + 2) by norm_num, Real.log_pow]
    rw [he, hf, hef]
    push_cast
    ring
  · have hzero : primeValuationFusion e f A B n = 0 := by
      simp [primeValuationFusion, arithmeticOfPrimePowerColumn, hpow]
    have hzeroLeft :
        primeValuationFusion e f (Complex.I • logWeight A) B n = 0 := by
      simp [primeValuationFusion, arithmeticOfPrimePowerColumn, hpow]
    have hzeroRight :
        primeValuationFusion e f A (Complex.I • logWeight B) n = 0 := by
      simp [primeValuationFusion, arithmeticOfPrimePowerColumn, hpow]
    simp [ArithmeticFunction.smul_map, logWeight_apply, hzero, hzeroLeft, hzeroRight]

@[simp]
theorem primeShiftFactor_add (a b : ℂ) (p : Nat.Primes) :
    primeShiftFactor (a + b) p = primeShiftFactor a p * primeShiftFactor b p := by
  rw [primeShiftFactor, primeShiftFactor, primeShiftFactor]
  rw [show -(a + b) * primeLogClock p =
      -a * primeLogClock p + -b * primeLogClock p by ring]
  exact Complex.exp_add _ _

/-- **All-order shifted fusion law.**  The jet of a fused source product is the binomial
fusion of the jets of the factors.  Source degrees and shifts both add. -/
theorem primePowerCoefficientShiftedRotatedJet_fusion_binomial
    (e f : ℕ) (c d : Nat.Primes → ℂ) (a b : ℂ) (k : ℕ) :
    primePowerCoefficientShiftedRotatedJet (e + f + 1)
        (fun p => c p * d p) (a + b) k =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) •
          primeValuationFusion e f
            (primePowerCoefficientShiftedRotatedJet e c a i)
            (primePowerCoefficientShiftedRotatedJet f d b (k - i)) := by
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 2)
  · obtain ⟨p, rfl⟩ := hpow
    rw [primePowerCoefficientShiftedRotatedJet,
      arithmeticOfPrimePowerColumn_apply]
    let ev : ArithmeticFunction ℂ →+ ℂ :=
      { toFun := fun F => F ((p : ℕ) ^ (e + f + 2))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change _ = ev (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) •
        primeValuationFusion e f
          (primePowerCoefficientShiftedRotatedJet e c a i)
          (primePowerCoefficientShiftedRotatedJet f d b (k - i)))
    rw [map_sum]
    change _ = ∑ i ∈ Finset.range (k + 1),
      ((k.choose i : ℂ) •
        primeValuationFusion e f
          (primePowerCoefficientShiftedRotatedJet e c a i)
          (primePowerCoefficientShiftedRotatedJet f d b (k - i)))
        ((p : ℕ) ^ (e + f + 2))
    simp_rw [ArithmeticFunction.smul_map, primeValuationFusion_apply]
    simp only [primePowerCoefficientShiftedRotatedJet,
      smul_eq_mul, arithmeticOfPrimePowerColumn_apply, primeShiftFactor_add]
    have hclock :
        (((e + f + 2 : ℕ) : ℂ) * rotatedPrimeLogClock p) =
          (((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) +
            (((f + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) := by
      push_cast
      ring
    rw [hclock, add_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · have hleft :
        primePowerCoefficientShiftedRotatedJet (e + f + 1)
          (fun p => c p * d p) (a + b) k n = 0 := by
      have hpow' : ¬∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 1 + 1) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpow
      simp [primePowerCoefficientShiftedRotatedJet,
        arithmeticOfPrimePowerColumn, hpow']
    rw [hleft]
    let ev : ArithmeticFunction ℂ →+ ℂ :=
      { toFun := fun F => F n
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change 0 = ev (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) •
        primeValuationFusion e f
          (primePowerCoefficientShiftedRotatedJet e c a i)
          (primePowerCoefficientShiftedRotatedJet f d b (k - i)))
    rw [map_sum]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hterm :
        primeValuationFusion e f
          (primePowerCoefficientShiftedRotatedJet e c a i)
          (primePowerCoefficientShiftedRotatedJet f d b (k - i)) n = 0 := by
      have hpow' : ¬∃ p : Nat.Primes, n = (p : ℕ) ^ (e + f + 1 + 1) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpow
      simp [primeValuationFusion, arithmeticOfPrimePowerColumn, hpow']
    change ((k.choose i : ℂ) •
      primeValuationFusion e f
        (primePowerCoefficientShiftedRotatedJet e c a i)
        (primePowerCoefficientShiftedRotatedJet f d b (k - i))) n = 0
    rw [ArithmeticFunction.smul_map, hterm, smul_eq_mul, mul_zero]

/-- Multiplication of homogeneous observables. -/
def homogeneousObservableMul {σ : Type*} {m n : ℕ}
    (Q : homogeneousSubmodule σ ℂ m) (R : homogeneousSubmodule σ ℂ n) :
    homogeneousSubmodule σ ℂ (m + n) :=
  ⟨Q.1 * R.1, Q.2.mul R.2⟩

/-- Homogeneous source multiplication is represented literally by valuation fusion. -/
theorem homogeneousConstraintValuationCarrier_mul
    {σ : Type*} (x : Nat.Primes → σ → ℂ)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (Q : homogeneousSubmodule σ ℂ m)
    (R : homogeneousSubmodule σ ℂ n) :
    primeValuationFusion (m - 1) (n - 1)
        (homogeneousConstraintValuationCarrier x m Q)
        (homogeneousConstraintValuationCarrier x n R) =
      homogeneousConstraintValuationCarrier x (m + n)
        (homogeneousObservableMul Q R) := by
  rw [homogeneousConstraintValuationCarrier,
    homogeneousConstraintValuationCarrier,
    homogeneousConstraintValuationCarrier]
  rw [primeValuationFusion_columns]
  congr 1
  · omega
  · funext p
    simp [homogeneousObservableMul]

/-- **All-order homogeneous valuation-fusion law.**  Polynomial multiplication, addition of
prime valuations, addition of Dirichlet shifts, and the binomial differential Leibniz rule are
one exact identity. -/
theorem homogeneousConstraintValuationJet_mul_binomial
    {σ : Type*} (x : Nat.Primes → σ → ℂ)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (Q : homogeneousSubmodule σ ℂ m)
    (R : homogeneousSubmodule σ ℂ n)
    (a b : ℂ) (k : ℕ) :
    homogeneousConstraintValuationJet x (m + n)
        (homogeneousObservableMul Q R) (a + b) k =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) •
          primeValuationFusion (m - 1) (n - 1)
            (homogeneousConstraintValuationJet x m Q a i)
            (homogeneousConstraintValuationJet x n R b (k - i)) := by
  have h := primePowerCoefficientShiftedRotatedJet_fusion_binomial
    (m - 1) (n - 1)
    (fun p => eval (x p) Q.1) (fun p => eval (x p) R.1) a b k
  unfold homogeneousConstraintValuationJet
  have hindex : (m - 1) + (n - 1) + 1 = m + n - 1 := by omega
  rw [hindex] at h
  simpa only [homogeneousObservableMul, Subtype.coe_eta, eval_mul] using h

end

end GaloisForLFunctions.HTGeometry
