import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite-field quadratic counts

The product equation obtained from a difference of squares gives the quadratic
character sum needed for diagonal quadratic forms. All counts refer to actual
finite sets of solutions.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine difference-of-squares fibre. -/
def squareDifferencePairs (c : F) : Finset (F × F) :=
  univ.filter (fun p => p.1 ^ 2 - p.2 ^ 2 = c)

/-- A nonzero factor and its complementary factor give a difference-of-squares solution. -/
def squareDifferenceParam (c : F) (u : Fˣ) : F × F :=
  (((u : F) + c / u) / 2, (c / u - u) / 2)

omit [Fintype F] [DecidableEq F] in
theorem squareDifferenceParam_sub (h₂ : (2 : F) ≠ 0) (c : F) (u : Fˣ) :
    (squareDifferenceParam c u).1 - (squareDifferenceParam c u).2 = (u : F) := by
  dsimp [squareDifferenceParam]
  field_simp [h₂, u.ne_zero]
  ring

omit [Fintype F] [DecidableEq F] in
theorem squareDifferenceParam_value (h₂ : (2 : F) ≠ 0) (c : F) (u : Fˣ) :
    (squareDifferenceParam c u).1 ^ 2 - (squareDifferenceParam c u).2 ^ 2 = c := by
  dsimp [squareDifferenceParam]
  field_simp [h₂, u.ne_zero]
  ring

/-- A nonzero difference-of-squares fibre has exactly one point per nonzero factor. -/
theorem squareDifferencePairs_card (h₂ : (2 : F) ≠ 0) {c : F} (hc : c ≠ 0) :
    (squareDifferencePairs c).card = Fintype.card F - 1 := by
  calc
    (squareDifferencePairs c).card = (univ : Finset Fˣ).card := by
      symm
      apply card_bij (fun u _ => squareDifferenceParam c u)
      · intro u _
        exact mem_filter.mpr ⟨mem_univ _, squareDifferenceParam_value h₂ c u⟩
      · intro u _ v _ h
        apply Units.ext
        have hh := congrArg (fun p : F × F => p.1 - p.2) h
        simpa only [squareDifferenceParam_sub h₂] using hh
      · intro p hp
        have he := (mem_filter.mp hp).2
        have hu : p.1 - p.2 ≠ 0 := by
          intro hz
          apply hc
          calc c = p.1 ^ 2 - p.2 ^ 2 := he.symm
            _ = 0 := by rw [sub_eq_zero.mp hz, sub_self]
        have hprod : (p.1 - p.2) * (p.1 + p.2) = c := by
          linear_combination he
        have hdiv : c / (p.1 - p.2) = p.1 + p.2 := by
          apply (div_eq_iff hu).mpr
          rw [mul_comm]
          exact hprod.symm
        refine ⟨Units.mk0 (p.1 - p.2) hu, mem_univ _, ?_⟩
        apply Prod.ext
        · dsimp [squareDifferenceParam]
          rw [hdiv]
          field_simp [h₂]
          ring
        · dsimp [squareDifferenceParam]
          rw [hdiv]
          field_simp [h₂]
          ring
    _ = _ := by rw [card_univ, Fintype.card_units]

/-- The correction distinguishes the zero value from the other field values. -/
def quadraticZeroCorrection (t : F) : ℤ :=
  if t = 0 then Fintype.card F - 1 else -1

/-- Counting the second square groups the difference-of-squares fibre by its first coordinate. -/
theorem squareDifferencePairs_card_eq_sum (c : F) :
    ((squareDifferencePairs c).card : ℤ) =
      ∑ y : F, ((univ.filter (fun z : F => z ^ 2 = y ^ 2 - c)).card : ℤ) := by
  simp only [squareDifferencePairs, card_eq_sum_ones, Nat.cast_sum,
    sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  have he : y ^ 2 - z ^ 2 = c ↔ z ^ 2 = y ^ 2 - c := by
    constructor <;> intro h <;> linear_combination -h
  simp only [he]

/-- The quadratic-character sum follows from the actual product-fibre count. -/
theorem quadraticChar_sum_sq_sub (hF : ringChar F ≠ 2) (c : F) :
    (∑ y : F, quadraticChar F (y ^ 2 - c)) = quadraticZeroCorrection c := by
  by_cases hc : c = 0
  · subst c
    have hz := sum_erase_add univ (fun y : F => quadraticChar F (y ^ 2)) (mem_univ 0)
    simp only [zero_pow two_ne_zero, quadraticChar_zero, add_zero] at hz
    have he : (∑ y ∈ univ.erase (0 : F), quadraticChar F (y ^ 2)) =
        ((univ.erase (0 : F)).card : ℤ) := by
      rw [sum_congr rfl (fun y hy => quadraticChar_sq_one' (mem_erase.mp hy).1)]
      simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [quadraticZeroCorrection, if_pos rfl]
    simp only [sub_zero]
    rw [← hz, he, card_erase_of_mem (mem_univ 0), card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · have h := squareDifferencePairs_card_eq_sum (F := F) c
    have hroots (y : F) : ((univ.filter (fun z : F => z ^ 2 = y ^ 2 - c)).card : ℤ) =
        quadraticChar F (y ^ 2 - c) + 1 := by
      simpa only [Set.toFinset_setOf] using quadraticChar_card_sqrts hF (y ^ 2 - c)
    rw [squareDifferencePairs_card (Ring.two_ne_zero hF) hc,
      sum_congr rfl (fun y _ => hroots y), sum_add_distrib, sum_const, card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_sub Fintype.card_pos, Nat.cast_one] at h
    rw [quadraticZeroCorrection, if_neg hc]
    linear_combination -h

/-- The one-variable quadratic fibre. -/
def quadraticRoots (a t : F) : Finset F :=
  univ.filter (fun x => a * x ^ 2 = t)

/-- A nonzero coefficient changes the square-root count by its quadratic character. -/
theorem quadraticRoots_card (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) (t : F) :
    ((quadraticRoots a t).card : ℤ) = quadraticChar F (a * t) + 1 := by
  have he : quadraticRoots a t = univ.filter (fun x : F => x ^ 2 = t / a) := by
    ext x
    simp only [quadraticRoots, mem_filter, mem_univ, true_and]
    rw [eq_div_iff ha, mul_comm (x ^ 2)]
  have hp : (t / a) * a ^ 2 = a * t := by
    field_simp [ha]
  have hχ := congrArg (quadraticChar F) hp
  rw [map_mul, quadraticChar_sq_one' ha, mul_one] at hχ
  rw [he]
  simpa only [Set.toFinset_setOf, hχ] using quadraticChar_card_sqrts hF (t / a)

/-- A scaled quadratic phase has the same two-value character distribution. -/
theorem quadraticChar_sum_sub_mul_sq (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) (t : F) :
    (∑ y : F, quadraticChar F (t - a * y ^ 2)) =
      quadraticChar F (-a) * quadraticZeroCorrection t := by
  have he (y : F) : t - a * y ^ 2 = (-a) * (y ^ 2 - t / a) := by
    field_simp [ha]
    ring
  simp_rw [he, map_mul]
  rw [← mul_sum, quadraticChar_sum_sq_sub hF]
  by_cases ht : t = 0
  · simp only [ht, zero_div]
  · simp only [quadraticZeroCorrection, if_neg ht, if_neg (div_ne_zero ht ha)]

/-- Summing the zero-value correction recovers the complementary one-variable character. -/
theorem quadraticZeroCorrection_sum_sub_mul_sq (hF : ringChar F ≠ 2)
    {a : F} (ha : a ≠ 0) (t : F) :
    (∑ y : F, quadraticZeroCorrection (t - a * y ^ 2)) =
      (Fintype.card F : ℤ) * quadraticChar F (a * t) := by
  have hv (z : F) : quadraticZeroCorrection z =
      (Fintype.card F : ℤ) * (if z = 0 then 1 else 0) - 1 := by
    by_cases hz : z = 0 <;> simp [quadraticZeroCorrection, hz]
  have hroot : (∑ y : F, if t - a * y ^ 2 = 0 then (1 : ℤ) else 0) =
      ((quadraticRoots a t).card : ℤ) := by
    simp only [quadraticRoots, card_eq_sum_ones, Nat.cast_sum, sum_filter,
      sub_eq_zero]
    apply sum_congr rfl
    intro y _
    by_cases hy : a * y ^ 2 = t
    · simp only [hy, ite_true, Nat.cast_one]
    · simp only [if_neg hy, if_neg (Ne.symm hy), Nat.cast_zero]
  simp_rw [hv]
  rw [sum_sub_distrib, ← mul_sum, hroot, quadraticRoots_card hF ha, sum_const,
    card_univ, nsmul_eq_mul, mul_one]
  ring

/-- The value of a diagonal quadratic form. -/
def diagonalQuadraticValue {n : ℕ} (d x : Fin n → F) : F :=
  ∑ i, d i * x i ^ 2

/-- The integer cardinality of an actual affine quadratic fibre. -/
def diagonalQuadraticCount {n : ℕ} (d : Fin n → F) (t : F) : ℤ :=
  ((univ.filter (fun x : Fin n → F => diagonalQuadraticValue d x = t)).card : ℤ)

theorem diagonalQuadraticCount_eq_sum {n : ℕ} (d : Fin n → F) (t : F) :
    diagonalQuadraticCount d t =
      ∑ x : Fin n → F, if diagonalQuadraticValue d x = t then (1 : ℤ) else 0 := by
  simp only [diagonalQuadraticCount, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro x _
  split <;> rfl

omit [Fintype F] [DecidableEq F] in
theorem diagonalQuadraticValue_cons {n : ℕ} (d : Fin (n + 1) → F)
    (y : F) (x : Fin n → F) :
    diagonalQuadraticValue d (Fin.cons y x) =
      d 0 * y ^ 2 + diagonalQuadraticValue (fun i => d i.succ) x := by
  simp only [diagonalQuadraticValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Splitting the first coordinate gives the convolution recurrence for actual fibres. -/
theorem diagonalQuadraticCount_succ {n : ℕ} (d : Fin (n + 1) → F) (t : F) :
    diagonalQuadraticCount d t =
      ∑ y : F, diagonalQuadraticCount (fun i => d i.succ) (t - d 0 * y ^ 2) := by
  rw [diagonalQuadraticCount_eq_sum]
  have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => F))
    (fun p : F × (Fin n → F) =>
      if diagonalQuadraticValue d (Fin.cons p.1 p.2) = t then (1 : ℤ) else 0)
    (fun x => if diagonalQuadraticValue d x = t then (1 : ℤ) else 0)
    (fun _ => rfl)
  rw [← he, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro y _
  rw [diagonalQuadraticCount_eq_sum]
  apply sum_congr rfl
  intro x _
  rw [diagonalQuadraticValue_cons]
  have hh : d 0 * y ^ 2 + diagonalQuadraticValue (fun i => d i.succ) x = t ↔
      diagonalQuadraticValue (fun i => d i.succ) x = t - d 0 * y ^ 2 := by
    constructor <;> intro h <;> linear_combination h
  simp only [hh]

theorem diagonalQuadraticCount_zero (d : Fin 0 → F) (t : F) :
    diagonalQuadraticCount d t = if t = 0 then 1 else 0 := by
  simp [diagonalQuadraticCount_eq_sum, diagonalQuadraticValue, eq_comm]

/-- The initial one-dimensional distribution is the square-root formula. -/
theorem diagonalQuadraticCount_one (hF : ringChar F ≠ 2)
    (d : Fin 1 → F) (hd : d 0 ≠ 0) (t : F) :
    diagonalQuadraticCount d t = 1 + quadraticChar F (d 0 * t) := by
  rw [diagonalQuadraticCount_succ]
  simp_rw [diagonalQuadraticCount_zero]
  have he : (∑ y : F, if t - d 0 * y ^ 2 = 0 then (1 : ℤ) else 0) =
      ((quadraticRoots (d 0) t).card : ℤ) := by
    simp only [quadraticRoots, card_eq_sum_ones, Nat.cast_sum, sum_filter, sub_eq_zero]
    apply sum_congr rfl
    intro y _
    by_cases hy : d 0 * y ^ 2 = t
    · simp only [hy, ite_true, Nat.cast_one]
    · simp only [if_neg hy, if_neg (Ne.symm hy), Nat.cast_zero]
  rw [he, quadraticRoots_card hF hd, add_comm]

private theorem diagonalQuadraticCount_step_char (hF : ringChar F ≠ 2)
    {n : ℕ} (d : Fin (n + 1) → F) (hd : d 0 ≠ 0) (A B : ℤ)
    (h : ∀ t, diagonalQuadraticCount (fun i => d i.succ) t =
      A + B * quadraticChar F t) (t : F) :
    diagonalQuadraticCount d t = A * Fintype.card F +
      B * quadraticChar F (-d 0) * quadraticZeroCorrection t := by
  rw [diagonalQuadraticCount_succ]
  simp_rw [h]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
    quadraticChar_sum_sub_mul_sq hF hd]
  ring

private theorem diagonalQuadraticCount_step_zero (hF : ringChar F ≠ 2)
    {n : ℕ} (d : Fin (n + 1) → F) (hd : d 0 ≠ 0) (A B : ℤ)
    (h : ∀ t, diagonalQuadraticCount (fun i => d i.succ) t =
      A + B * quadraticZeroCorrection t) (t : F) :
    diagonalQuadraticCount d t = A * Fintype.card F +
      B * Fintype.card F * quadraticChar F (d 0 * t) := by
  rw [diagonalQuadraticCount_succ]
  simp_rw [h]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
    quadraticZeroCorrection_sum_sub_mul_sq hF hd]
  ring

/-- Odd and even dimensions have complementary character and zero-value corrections. -/
theorem diagonalQuadraticCount_distribution (hF : ringChar F ≠ 2) (k : ℕ) :
    (∀ (d : Fin (2 * k + 1) → F), (∀ i, d i ≠ 0) → ∀ t,
      diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * k) +
        quadraticChar F ((-1) ^ k * ∏ i, d i) * quadraticChar F t *
          (Fintype.card F : ℤ) ^ k) ∧
    (∀ (d : Fin (2 * k + 2) → F), (∀ i, d i ≠ 0) → ∀ t,
      diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * k + 1) +
        quadraticChar F ((-1) ^ (k + 1) * ∏ i, d i) * quadraticZeroCorrection t *
          (Fintype.card F : ℤ) ^ k) := by
  have even_step (j : ℕ)
      (ho : ∀ (d : Fin (2 * j + 1) → F), (∀ i, d i ≠ 0) → ∀ t,
        diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * j) +
          quadraticChar F ((-1) ^ j * ∏ i, d i) * quadraticChar F t *
            (Fintype.card F : ℤ) ^ j)
      (d : Fin (2 * j + 2) → F) (hd : ∀ i, d i ≠ 0) (t : F) :
      diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * j + 1) +
        quadraticChar F ((-1) ^ (j + 1) * ∏ i, d i) * quadraticZeroCorrection t *
          (Fintype.card F : ℤ) ^ j := by
    have ht (s : F) := ho (fun i : Fin (2 * j + 1) => d i.succ)
      (fun i => hd i.succ) s
    have hs (s : F) : diagonalQuadraticCount (fun i : Fin (2 * j + 1) => d i.succ) s =
        (Fintype.card F : ℤ) ^ (2 * j) +
          (quadraticChar F ((-1) ^ j * ∏ i : Fin (2 * j + 1), d i.succ) *
            (Fintype.card F : ℤ) ^ j) * quadraticChar F s := by
      rw [ht]
      ring
    rw [diagonalQuadraticCount_step_char hF d (hd 0) _ _ hs]
    have hc : quadraticChar F ((-1) ^ j * ∏ i : Fin (2 * j + 1), d i.succ) *
        quadraticChar F (-d 0) = quadraticChar F ((-1) ^ (j + 1) * ∏ i, d i) := by
      rw [← map_mul]
      congr 1
      rw [Fin.prod_univ_succ d, pow_succ]
      ring
    rw [pow_succ]
    linear_combination hc * quadraticZeroCorrection t * (Fintype.card F : ℤ) ^ j
  induction k with
  | zero =>
      have ho (d : Fin 1 → F) (hd : ∀ i, d i ≠ 0) (t : F) :
          diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * 0) +
            quadraticChar F ((-1) ^ 0 * ∏ i, d i) * quadraticChar F t *
              (Fintype.card F : ℤ) ^ 0 := by
        rw [diagonalQuadraticCount_one hF d (hd 0)]
        simp only [mul_zero, pow_zero, one_mul, mul_one, Fin.prod_univ_one, map_mul]
      exact ⟨ho, even_step 0 ho⟩
  | succ k ih =>
      have ho (d : Fin (2 * (k + 1) + 1) → F) (hd : ∀ i, d i ≠ 0) (t : F) :
          diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * (k + 1)) +
            quadraticChar F ((-1) ^ (k + 1) * ∏ i, d i) * quadraticChar F t *
              (Fintype.card F : ℤ) ^ (k + 1) := by
        have hs (s : F) : diagonalQuadraticCount (fun i : Fin (2 * k + 2) => d i.succ) s =
            (Fintype.card F : ℤ) ^ (2 * k + 1) +
              (quadraticChar F ((-1) ^ (k + 1) * ∏ i : Fin (2 * k + 2), d i.succ) *
                (Fintype.card F : ℤ) ^ k) * quadraticZeroCorrection s := by
          rw [ih.2 (fun i : Fin (2 * k + 2) => d i.succ) (fun i => hd i.succ)]
          ring
        rw [diagonalQuadraticCount_step_zero hF d (hd 0) _ _ hs]
        have hc : quadraticChar F ((-1) ^ (k + 1) * ∏ i : Fin (2 * k + 2), d i.succ) *
            quadraticChar F (d 0 * t) =
            quadraticChar F ((-1) ^ (k + 1) * ∏ i, d i) * quadraticChar F t := by
          rw [← map_mul, ← map_mul]
          congr 1
          rw [Fin.prod_univ_succ d]
          change ((-1 : F) ^ (k + 1) * (∏ i : Fin (2 * k + 2), d i.succ)) * (d 0 * t) =
            ((-1 : F) ^ (k + 1) * (d 0 * ∏ i : Fin (2 * k + 2), d i.succ)) * t
          ring
        have hp : (Fintype.card F : ℤ) ^ (2 * (k + 1)) =
            (Fintype.card F : ℤ) ^ (2 * k + 1) * (Fintype.card F : ℤ) := by
          rw [Nat.mul_succ, pow_succ]
        rw [hp, pow_succ (Fintype.card F : ℤ) k]
        linear_combination hc * (Fintype.card F : ℤ) ^ k * (Fintype.card F : ℤ)
      exact ⟨ho, even_step (k + 1) ho⟩

/-- Exact affine count in odd dimension, including every nonzero target value. -/
theorem diagonalQuadraticCount_odd (hF : ringChar F ≠ 2) (k : ℕ)
    (d : Fin (2 * k + 1) → F) (hd : ∀ i, d i ≠ 0) (t : F) :
    diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * k) +
      quadraticChar F ((-1) ^ k * (∏ i, d i) * t) * (Fintype.card F : ℤ) ^ k := by
  rw [map_mul]
  exact (diagonalQuadraticCount_distribution hF k).1 d hd t

/-- Exact affine count in positive even dimension. -/
theorem diagonalQuadraticCount_even (hF : ringChar F ≠ 2) (k : ℕ)
    (d : Fin (2 * k + 2) → F) (hd : ∀ i, d i ≠ 0) (t : F) :
    diagonalQuadraticCount d t = (Fintype.card F : ℤ) ^ (2 * k + 1) +
      quadraticChar F ((-1) ^ (k + 1) * ∏ i, d i) * quadraticZeroCorrection t *
        (Fintype.card F : ℤ) ^ k :=
  (diagonalQuadraticCount_distribution hF k).2 d hd t

/-- The zero fibre in odd dimension has no discriminant correction. -/
theorem diagonalQuadraticCount_odd_zero (hF : ringChar F ≠ 2) (k : ℕ)
    (d : Fin (2 * k + 1) → F) (hd : ∀ i, d i ≠ 0) :
    diagonalQuadraticCount d 0 = (Fintype.card F : ℤ) ^ (2 * k) := by
  rw [diagonalQuadraticCount_odd hF k d hd]
  simp only [mul_zero, quadraticChar_zero, zero_mul, add_zero]

/-- The even-dimensional zero fibre is determined by the signed discriminant. -/
theorem diagonalQuadraticCount_even_zero (hF : ringChar F ≠ 2) (k : ℕ)
    (d : Fin (2 * k + 2) → F) (hd : ∀ i, d i ≠ 0) :
    diagonalQuadraticCount d 0 = (Fintype.card F : ℤ) ^ (2 * k + 1) +
      quadraticChar F ((-1) ^ (k + 1) * ∏ i, d i) *
        (Fintype.card F - 1) * (Fintype.card F : ℤ) ^ k := by
  rw [diagonalQuadraticCount_even hF k d hd, quadraticZeroCorrection, if_pos rfl]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
