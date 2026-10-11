import GaloisForLFunctions.HTGeometry.MixedClassSliceVisibilityWindow
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Sharp detection order of an off-line pair against a real background

Let `f` be a real polynomial whose zeros are real except for an off-line pair `γ ± iδ` of
multiplicity `m ≥ 1`, and let `γ_i ≠ γ` be its real zeros.  Its slice at the ordinate `γ` is, in
`y = x²` (`offLinePairSliceProduct_eq_eval`),

  `f(γ + ix) f(γ − ix) = (δ² − y)^{2m} ∏ ((γ − γ_i)² + y)`.

**Theorem** (`exists_offLinePairSlice_coeff_neg`).  Some coefficient of order `j` with
`1 ≤ j ≤ δ² S + 1` is negative, where `S = Σ (γ − γ_i)^{−2}`.  The bound does not depend on `m`.

In normalized form (`exists_coeff_neg_one_sub_X_pow_mul_prod`): for `v_i ≥ 0` with `σ = Σ v_i`, the
polynomial `(1 − Y)^{2m} ∏ (1 + v_i Y)` has a negative coefficient of order `1 ≤ j ≤ max(1, ⌈σ⌉)`.

Proof.  Let `e_j` be the coefficients of `E = ∏ (1 + v_i Y)`.  Maclaurin's inequality
`(j + 1) e_{j+1} ≤ σ e_j` (`maclaurin_coeff_prod_one_add_C_mul_X`) follows by induction on the
factors.  The coefficients of `P` are the partial sums of those of `(1 − Y) P`.  So if the
coefficients of `(1 − Y)^{2m} E` are `≥ 0` up to order `J`, summing `2m − 1` times gives
`e_j − e_{j−1} ≥ 1` for `1 ≤ j ≤ J`.  Then `J e_J ≤ σ e_{J−1} ≤ σ (e_J − 1)`, which is impossible for
`J ≥ max(1, σ)`.

**Sharpness up to `√σ`** (`poisson_secondDifference_eq`).  For the Poisson profile `e_j = μ^j / j!`
(the limit of `(1 + μY/N)^N`; the slice of `e^{−cz²}(z² + δ²)` at `γ = 0`, `μ = 2cδ²`), the
coefficient of `Y^j` in `(1 − Y)² e^{μY}` is `μ^{j−2}((j − μ)² − j)/j!`.  It is `≥ 0` for every
`j ≤ μ − √μ` (`poisson_secondDifference_nonneg`), so the first negative order is at least
`μ − √μ`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficients of `P` are the partial sums of the coefficients of `(1 − X) P`. -/
theorem coeff_eq_sum_coeff_one_sub_X_mul (P : ℝ[X]) (j : ℕ) :
    P.coeff j = ∑ i ∈ range (j + 1), ((1 - X) * P).coeff i := by
  induction j with
  | zero => simp [sub_mul]
  | succ j ih =>
    rw [sum_range_succ, ← ih, sub_mul, one_mul, coeff_sub, coeff_X_mul]
    ring

theorem coeff_one_sub_X_pow_mul_zero (P : ℝ[X]) (k : ℕ) :
    ((1 - X) ^ k * P).coeff 0 = P.coeff 0 := by
  rw [mul_coeff_zero, coeff_zero_eq_eval_zero ((1 - X) ^ k)]
  simp

/-- If `(1 − X) P` has nonnegative coefficients up to order `J` and `P(0) = 1`, then the
coefficients of `P` up to order `J` are `≥ 1`. -/
theorem one_le_coeff_of_one_sub_X_mul_nonneg {P : ℝ[X]} (h0 : P.coeff 0 = 1) {J : ℕ}
    (h : ∀ j ≤ J, 0 ≤ ((1 - X) * P).coeff j) : ∀ j ≤ J, 1 ≤ P.coeff j := by
  intro j hj
  rw [coeff_eq_sum_coeff_one_sub_X_mul, sum_range_succ']
  have hfirst : ((1 - X) * P).coeff 0 = 1 := by
    rw [← pow_one (1 - X : ℝ[X]), coeff_one_sub_X_pow_mul_zero, h0]
  rw [hfirst]
  have : 0 ≤ ∑ i ∈ range j, ((1 - X) * P).coeff (i + 1) :=
    sum_nonneg fun i hi => h _ (by simp only [mem_range] at hi; omega)
  linarith

theorem coeff_nonneg_of_one_sub_X_pow_succ {E : ℝ[X]} (h0 : E.coeff 0 = 1) {J k : ℕ}
    (h : ∀ j ≤ J, 0 ≤ ((1 - X) ^ (k + 1) * E).coeff j) :
    ∀ j ≤ J, 0 ≤ ((1 - X) ^ k * E).coeff j := by
  intro j hj
  have := one_le_coeff_of_one_sub_X_mul_nonneg (P := (1 - X) ^ k * E)
    (by rw [coeff_one_sub_X_pow_mul_zero, h0])
    (fun i hi => by rw [← mul_assoc, ← pow_succ']; exact h i hi) j hj
  linarith

theorem coeff_two_nonneg_of_pow {E : ℝ[X]} (h0 : E.coeff 0 = 1) {J : ℕ} :
    ∀ k : ℕ, (∀ j ≤ J, 0 ≤ ((1 - X) ^ (k + 2) * E).coeff j) →
      ∀ j ≤ J, 0 ≤ ((1 - X) ^ 2 * E).coeff j
  | 0, h => h
  | k + 1, h => coeff_two_nonneg_of_pow h0 k (coeff_nonneg_of_one_sub_X_pow_succ h0 (k := k + 2) h)

theorem coeff_one_add_C_mul_X_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ ((1 : ℝ[X]) + C a * X).coeff n := by
  rcases n with _ | _ | n <;> simp [coeff_one, coeff_X]
  exact ha

theorem coeff_prod_one_add_C_mul_X_zero {ι : Type*} (s : Finset ι) (v : ι → ℝ) :
    (∏ i ∈ s, (1 + C (v i) * X)).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  simp

/-- **Maclaurin's inequality** `(j + 1) e_{j+1} ≤ σ e_j` for the coefficients of `∏ (1 + v_i X)`,
`v_i ≥ 0`, `σ = Σ v_i`. -/
theorem maclaurin_coeff_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (j : ℕ) :
    ((j : ℝ) + 1) * (∏ i ∈ s, (1 + C (v i) * X)).coeff (j + 1) ≤
      (∑ i ∈ s, v i) * (∏ i ∈ s, (1 + C (v i) * X)).coeff j := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have hva : 0 ≤ v a := hv a (mem_insert_self a s)
    have hv' : ∀ i ∈ s, 0 ≤ v i := fun i hi => hv i (mem_insert_of_mem hi)
    set E := ∏ i ∈ s, (1 + C (v i) * X) with hE
    have hnn : ∀ n, 0 ≤ E.coeff n :=
      coeff_prod_nonneg_of_forall s _ fun i hi n => coeff_one_add_C_mul_X_nonneg (hv' i hi) n
    have hcoeff : ∀ n, ((1 + C (v a) * X) * E).coeff (n + 1) = E.coeff (n + 1) + v a * E.coeff n := by
      intro n
      rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]
    have hcoeff0 : ((1 + C (v a) * X) * E).coeff 0 = E.coeff 0 := by
      rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero,
        add_zero]
    rw [hcoeff]
    rcases j with _ | j
    · rw [hcoeff0]
      have h1 := ih hv' 0
      push_cast at h1 ⊢
      nlinarith [mul_nonneg hva (hnn 0)]
    · rw [hcoeff]
      have h1 := ih hv' (j + 1)
      have h2 := ih hv' j
      push_cast at h1 h2 ⊢
      nlinarith [mul_le_mul_of_nonneg_left h2 hva, mul_nonneg (mul_nonneg hva hva) (hnn j),
        mul_nonneg hva (hnn (j + 1))]

/-- **Detection order, normalized form.**  For `v_i ≥ 0`, `σ = Σ v_i` and `m ≥ 1`, the polynomial
`(1 − X)^{2m} ∏ (1 + v_i X)` has a negative coefficient of some order `1 ≤ j ≤ max(1, ⌈σ⌉)`. -/
theorem exists_coeff_neg_one_sub_X_pow_mul_prod {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ max 1 ⌈∑ i ∈ s, v i⌉₊ ∧
      ((1 - X) ^ (2 * m) * ∏ i ∈ s, (1 + C (v i) * X)).coeff j < 0 := by
  set σ := ∑ i ∈ s, v i with hσ
  set E := ∏ i ∈ s, (1 + C (v i) * X) with hE
  set J := max 1 ⌈σ⌉₊ with hJ
  by_contra hcon
  push Not at hcon
  have h0 : E.coeff 0 = 1 := coeff_prod_one_add_C_mul_X_zero s v
  have hnn : ∀ n, 0 ≤ E.coeff n :=
    coeff_prod_nonneg_of_forall s _ fun i hi n => coeff_one_add_C_mul_X_nonneg (hv i hi) n
  have hall : ∀ j ≤ J, 0 ≤ ((1 - X) ^ (2 * m) * E).coeff j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [coeff_one_sub_X_pow_mul_zero, h0]
      norm_num
    · exact hcon j hjpos hj
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 2 := ⟨2 * m - 2, by omega⟩
  rw [hk] at hall
  have h2 := coeff_two_nonneg_of_pow h0 k hall
  have h1 := one_le_coeff_of_one_sub_X_mul_nonneg (P := (1 - X) * E)
    (by rw [← pow_one (1 - X : ℝ[X]), coeff_one_sub_X_pow_mul_zero, h0])
    (fun i hi => by rw [← mul_assoc, ← pow_two]; exact h2 i hi)
  have hJ1 : 1 ≤ J := le_max_left _ _
  obtain ⟨J', hJ'⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  have hdiff := h1 J le_rfl
  rw [hJ', sub_mul, one_mul, coeff_sub, coeff_X_mul] at hdiff
  have hmac := maclaurin_coeff_prod_one_add_C_mul_X s v hv J'
  have hσnn : 0 ≤ σ := sum_nonneg hv
  have hJσ : σ ≤ (J' : ℝ) + 1 := by
    have h := (Nat.le_ceil σ).trans (Nat.cast_le.mpr (le_max_right 1 ⌈σ⌉₊))
    rw [← hJ, hJ'] at h
    push_cast at h
    exact h
  have he1 : 1 ≤ E.coeff (J' + 1) := by linarith [hnn J']
  have hstep : ((J' : ℝ) + 1) * E.coeff (J' + 1) ≤ σ * (E.coeff (J' + 1) - 1) :=
    hmac.trans (mul_le_mul_of_nonneg_left (by linarith) hσnn)
  nlinarith [mul_nonneg (sub_nonneg.mpr hJσ) (sub_nonneg.mpr he1)]

/-- **Detection order, real form.**  Some coefficient of order `1 ≤ j ≤ σ + 1` of
`(1 − X)^{2m} ∏ (1 + v_i X)` is negative. -/
theorem exists_coeff_neg_le_mass_add_one {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ (∑ i ∈ s, v i) + 1 ∧
      ((1 - X) ^ (2 * m) * ∏ i ∈ s, (1 + C (v i) * X)).coeff j < 0 := by
  obtain ⟨j, hj1, hjJ, hneg⟩ := exists_coeff_neg_one_sub_X_pow_mul_prod s v hv hm
  refine ⟨j, hj1, ?_, hneg⟩
  have hσnn : 0 ≤ ∑ i ∈ s, v i := sum_nonneg hv
  have hceil := Nat.ceil_lt_add_one hσnn
  have hjJ' : (j : ℝ) ≤ ((max 1 ⌈∑ i ∈ s, v i⌉₊ : ℕ) : ℝ) := by exact_mod_cast hjJ
  rcases le_total 1 ⌈∑ i ∈ s, v i⌉₊ with h | h
  · rw [max_eq_right h] at hjJ'
    linarith
  · rw [max_eq_left h] at hjJ'
    push_cast at hjJ'
    linarith

/-- The slice of `((z − γ)² + δ²)^m ∏ (z − γ_i)` at the ordinate `γ`, in `y = x²`. -/
theorem offLinePairSliceProduct_eq_eval {ι : Type*} (s : Finset ι) (γ δ : ℝ) (g : ι → ℝ) (m : ℕ)
    (x : ℝ) :
    (((γ : ℂ) + x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m *
          (∏ i ∈ s, ((γ : ℂ) + x * Complex.I - g i)) *
        ((((γ : ℂ) - x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m *
          (∏ i ∈ s, ((γ : ℂ) - x * Complex.I - g i))) =
      ((((C (δ ^ 2) - X) ^ (2 * m) * ∏ i ∈ s, (X + C ((γ - g i) ^ 2))).eval (x ^ 2) : ℝ) : ℂ) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1 : (((γ : ℂ) + x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m *
      ((((γ : ℂ) - x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m) = (((δ ^ 2 - x ^ 2) ^ (2 * m) : ℝ) : ℂ) := by
    rw [← mul_pow, pow_mul, Complex.ofReal_pow]
    congr 1
    push_cast
    linear_combination (2 * (δ : ℂ) ^ 2 * (x : ℂ) ^ 2 - 2 * (x : ℂ) ^ 4 +
      (x : ℂ) ^ 4 * (Complex.I ^ 2 + 1)) * hI
  have h2 : ∀ i ∈ s, ((γ : ℂ) + x * Complex.I - g i) * ((γ : ℂ) - x * Complex.I - g i) =
      ((((γ - g i) ^ 2 + x ^ 2) : ℝ) : ℂ) := by
    intro i _
    push_cast
    linear_combination (-(x : ℂ) ^ 2) * hI
  calc _ = ((((γ : ℂ) + x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m *
          ((((γ : ℂ) - x * Complex.I - γ) ^ 2 + (δ : ℂ) ^ 2) ^ m)) *
        ∏ i ∈ s, (((γ : ℂ) + x * Complex.I - g i) * ((γ : ℂ) - x * Complex.I - g i)) := by
          rw [prod_mul_distrib]
          ring
    _ = _ := by
          rw [h1, prod_congr rfl h2, ← Complex.ofReal_prod, ← Complex.ofReal_mul]
          congr 1
          simp only [eval_mul, eval_pow, eval_sub, eval_C, eval_X, eval_prod, eval_add]
          congr 1
          refine prod_congr rfl fun i _ => ?_
          ring

/-- **Detection order of an off-line pair against a real background.**  Let `δ ≠ 0`, `m ≥ 1`
and let `γ_i ≠ γ` be real.  The slice `(δ² − y)^{2m} ∏ ((γ − γ_i)² + y)` of
`((z − γ)² + δ²)^m ∏ (z − γ_i)` at the ordinate `γ` has a negative coefficient of some order
`1 ≤ j ≤ δ² Σ (γ − γ_i)^{−2} + 1`. -/
theorem exists_offLinePairSlice_coeff_neg {ι : Type*} (s : Finset ι) (γ δ : ℝ) (g : ι → ℝ)
    (hδ : δ ≠ 0) (hg : ∀ i ∈ s, g i ≠ γ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ δ ^ 2 * (∑ i ∈ s, 1 / (γ - g i) ^ 2) + 1 ∧
      ((C (δ ^ 2) - X) ^ (2 * m) * ∏ i ∈ s, (X + C ((γ - g i) ^ 2))).coeff j < 0 := by
  set v : ι → ℝ := fun i => δ ^ 2 / (γ - g i) ^ 2 with hvdef
  set r : ℝ := 1 / δ ^ 2 with hr
  have hd : ∀ i ∈ s, (γ - g i) ^ 2 ≠ 0 := fun i hi =>
    pow_ne_zero 2 (sub_ne_zero.mpr (hg i hi).symm)
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ
  have hv : ∀ i ∈ s, 0 ≤ v i := fun i _ => by positivity
  set N := (1 - X) ^ (2 * m) * ∏ i ∈ s, (1 + C (v i) * X) with hN
  set κ : ℝ := (δ ^ 2) ^ (2 * m) * ∏ i ∈ s, (γ - g i) ^ 2 with hκ
  have hκpos : 0 < κ := by
    refine mul_pos (by positivity) (prod_pos fun i hi => ?_)
    exact lt_of_le_of_ne (sq_nonneg _) (hd i hi).symm
  have e1 : (C (δ ^ 2) - X : ℝ[X]) = C (δ ^ 2) * (1 - C r * X) := by
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, show δ ^ 2 * r = 1 by rw [hr]; field_simp, C_1,
      one_mul]
  have e2 : ∀ i ∈ s, (X + C ((γ - g i) ^ 2) : ℝ[X]) =
      C ((γ - g i) ^ 2) * (1 + C (v i) * (C r * X)) := by
    intro i hi
    have hgi : γ - g i ≠ 0 := sub_ne_zero.mpr (hg i hi).symm
    have hs : (γ - g i) ^ 2 * v i * r = 1 := by
      simp only [hvdef, hr]
      field_simp [hgi, hδ2]
    rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs, C_1, one_mul, add_comm]
  have hcomp : N.comp (C r * X) = (1 - C r * X) ^ (2 * m) * ∏ i ∈ s, (1 + C (v i) * (C r * X)) := by
    simp only [hN, mul_comp, pow_comp, sub_comp, one_comp, X_comp, Polynomial.prod_comp, add_comp,
      C_comp]
  have hQ : (C (δ ^ 2) - X) ^ (2 * m) * ∏ i ∈ s, (X + C ((γ - g i) ^ 2)) =
      C κ * N.comp (C r * X) := by
    rw [hcomp, e1, prod_congr rfl e2, mul_pow, prod_mul_distrib, hκ]
    simp only [map_mul, map_pow, map_prod]
    ring
  obtain ⟨j, hj1, hjle, hneg⟩ := exists_coeff_neg_le_mass_add_one s v hv hm
  refine ⟨j, hj1, ?_, ?_⟩
  · have : ∑ i ∈ s, v i = δ ^ 2 * ∑ i ∈ s, 1 / (γ - g i) ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [hvdef]
      ring
    rw [← this]
    exact hjle
  · rw [hQ, coeff_C_mul, comp_C_mul_X_coeff]
    have hrpos : 0 < r ^ j := by positivity
    have : N.coeff j * r ^ j < 0 := mul_neg_of_neg_of_pos hneg hrpos
    exact mul_neg_of_pos_of_neg hκpos this

/-- **Poisson profile.**  The second difference of `μ^j / j!`:
`μ^{j+2}/(j+2)! − 2μ^{j+1}/(j+1)! + μ^j/j! = μ^j/(j+2)! · ((j + 2 − μ)² − (j + 2))`. -/
theorem poisson_secondDifference_eq (μ : ℝ) (j : ℕ) :
    μ ^ (j + 2) / ((j + 2).factorial : ℝ) - 2 * (μ ^ (j + 1) / ((j + 1).factorial : ℝ)) +
        μ ^ j / (j.factorial : ℝ) =
      μ ^ j / ((j + 2).factorial : ℝ) * (((j : ℝ) + 2 - μ) ^ 2 - ((j : ℝ) + 2)) := by
  rw [show j + 2 = (j + 1) + 1 by ring, Nat.factorial_succ (j + 1), Nat.factorial_succ j]
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  push_cast
  field_simp
  ring

/-- For the Poisson profile every coefficient of order `j + 2 ≤ μ − √μ` of `(1 − Y)² e^{μY}` is
`≥ 0`. -/
theorem poisson_secondDifference_nonneg {μ : ℝ} (hμ : 0 ≤ μ) {j : ℕ}
    (hj : (j : ℝ) + 2 + Real.sqrt μ ≤ μ) :
    0 ≤ μ ^ (j + 2) / ((j + 2).factorial : ℝ) - 2 * (μ ^ (j + 1) / ((j + 1).factorial : ℝ)) +
      μ ^ j / (j.factorial : ℝ) := by
  rw [poisson_secondDifference_eq]
  refine mul_nonneg (by positivity) ?_
  have hs := Real.sqrt_nonneg μ
  have hsq := Real.sq_sqrt hμ
  have h1 : Real.sqrt μ ≤ μ - ((j : ℝ) + 2) := by linarith
  have h3 := mul_self_le_mul_self hs h1
  have h2 : μ ≤ (μ - ((j : ℝ) + 2)) ^ 2 := by nlinarith
  nlinarith

end

end GaloisForLFunctions.HTGeometry
