import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The fixed-depth Hermite contrast ladder

This module formalizes the exact limiting algebra in the constrained-prolate fixed-mode card.  It
defines the squared normalized Hermite values

`a_j^2 = sqrt(2) * choose(4j,2j) / 16^j`,

their partial sums and secular weights, and the finite-support contrast vectors selected by the
rank-one vanishing-integral constraint.  The vectors satisfy the constraint, are pairwise
orthogonal, and are orthogonal to all preceding raw CCM contrasts.  The first two secular weights
and the first adjacent-gap coefficient are evaluated exactly.

These are unconditional identities.  No Fuchs asymptotic, prolate-to-Hermite convergence, or Weil
comparison is assumed here.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The rational Hermite weight `q_j = choose(4j,2j)/16^j`. -/
def constrainedProlateHermiteWeight (j : ℕ) : ℝ :=
  (Nat.choose (4 * j) (2 * j) : ℝ) / (16 : ℝ) ^ j

theorem constrainedProlateHermiteWeight_pos (j : ℕ) :
    0 < constrainedProlateHermiteWeight j := by
  unfold constrainedProlateHermiteWeight
  exact div_pos (by exact_mod_cast Nat.choose_pos (by omega : 2 * j ≤ 4 * j)) (by positivity)

/-- Every positive-index constrained-prolate Hermite weight is at most one half. -/
theorem constrainedProlateHermiteWeight_le_half_of_pos {j : ℕ} (hj : 0 < j) :
    constrainedProlateHermiteWeight j ≤ 1 / 2 := by
  have hfour : 4 * j = (4 * j - 1) + 1 := by omega
  have hchoose := Nat.choose_succ_le_two_pow (4 * j - 1) (2 * j)
  rw [← hfour] at hchoose
  have hchooseReal :
      (Nat.choose (4 * j) (2 * j) : ℝ) ≤ (2 : ℝ) ^ (4 * j - 1) := by
    exact_mod_cast hchoose
  have hden : (16 : ℝ) ^ j = 2 * (2 : ℝ) ^ (4 * j - 1) := by
    calc
      (16 : ℝ) ^ j = (2 ^ 4 : ℝ) ^ j := by norm_num
      _ = (2 : ℝ) ^ (4 * j) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ ((4 * j - 1) + 1) := by rw [← hfour]
      _ = 2 * (2 : ℝ) ^ (4 * j - 1) := by rw [pow_succ]; ring
  rw [constrainedProlateHermiteWeight, hden]
  rw [div_le_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ (4 * j - 1))]
  calc
    (Nat.choose (4 * j) (2 * j) : ℝ) ≤ (2 : ℝ) ^ (4 * j - 1) := hchooseReal
    _ = (1 / 2) * (2 * (2 : ℝ) ^ (4 * j - 1)) := by ring

/-- The constrained-prolate Hermite weights form a physical occupation profile in `(0, 1]`. -/
theorem constrainedProlateHermiteWeight_le_one (j : ℕ) :
    constrainedProlateHermiteWeight j ≤ 1 := by
  by_cases hj : j = 0
  · subst j
    simp [constrainedProlateHermiteWeight]
  · exact (constrainedProlateHermiteWeight_le_half_of_pos
      (Nat.pos_of_ne_zero hj)).trans (by norm_num)

theorem constrainedProlateHermiteWeight_mem_Ioc (j : ℕ) :
    constrainedProlateHermiteWeight j ∈ Set.Ioc 0 1 :=
  ⟨constrainedProlateHermiteWeight_pos j, constrainedProlateHermiteWeight_le_one j⟩

/-- Away from the fully occupied ground mode, every constrained-prolate occupation is strict. -/
theorem constrainedProlateHermiteWeight_lt_one_of_pos {j : ℕ} (hj : 0 < j) :
    constrainedProlateHermiteWeight j < 1 :=
  (constrainedProlateHermiteWeight_le_half_of_pos hj).trans_lt (by norm_num)

/-- The positive normalized Hermite coordinate with square `sqrt(2) q_j`. -/
def constrainedProlateHermiteCoordinate (j : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt 2 * constrainedProlateHermiteWeight j)

theorem constrainedProlateHermiteCoordinate_pos (j : ℕ) :
    0 < constrainedProlateHermiteCoordinate j := by
  unfold constrainedProlateHermiteCoordinate
  exact Real.sqrt_pos.2
    (mul_pos (Real.sqrt_pos.2 (by norm_num)) (constrainedProlateHermiteWeight_pos j))

theorem constrainedProlateHermiteCoordinate_ne_zero (j : ℕ) :
    constrainedProlateHermiteCoordinate j ≠ 0 :=
  (constrainedProlateHermiteCoordinate_pos j).ne'

/-- Exact square of the normalized Hermite coordinate. -/
theorem constrainedProlateHermiteCoordinate_sq (j : ℕ) :
    constrainedProlateHermiteCoordinate j ^ 2 =
      Real.sqrt 2 * constrainedProlateHermiteWeight j := by
  rw [constrainedProlateHermiteCoordinate, Real.sq_sqrt]
  exact (mul_nonneg (Real.sqrt_nonneg _) (constrainedProlateHermiteWeight_pos j).le)

/-- `Q_k = sum_{j=0}^k q_j`. -/
def constrainedProlateHermiteWeightSum (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), constrainedProlateHermiteWeight j

theorem constrainedProlateHermiteWeightSum_pos (k : ℕ) :
    0 < constrainedProlateHermiteWeightSum k := by
  unfold constrainedProlateHermiteWeightSum
  exact Finset.sum_pos' (fun j _ => (constrainedProlateHermiteWeight_pos j).le)
    ⟨0, by simp, constrainedProlateHermiteWeight_pos 0⟩

/-- `S_k = sum_{j=0}^k a_j^2 = sqrt(2) Q_k`. -/
def constrainedProlateHermiteSquareSum (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), constrainedProlateHermiteCoordinate j ^ 2

theorem constrainedProlateHermiteSquareSum_eq (k : ℕ) :
    constrainedProlateHermiteSquareSum k =
      Real.sqrt 2 * constrainedProlateHermiteWeightSum k := by
  rw [constrainedProlateHermiteSquareSum, constrainedProlateHermiteWeightSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [constrainedProlateHermiteCoordinate_sq]

theorem constrainedProlateHermiteSquareSum_pos (k : ℕ) :
    0 < constrainedProlateHermiteSquareSum k := by
  rw [constrainedProlateHermiteSquareSum_eq]
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (constrainedProlateHermiteWeightSum_pos k)

/-- The limiting secular root `theta_k = Q_k/Q_{k+1}`. -/
def constrainedProlateHermiteTheta (k : ℕ) : ℝ :=
  constrainedProlateHermiteWeightSum k / constrainedProlateHermiteWeightSum (k + 1)

theorem constrainedProlateHermiteWeightSum_succ (k : ℕ) :
    constrainedProlateHermiteWeightSum (k + 1) =
      constrainedProlateHermiteWeightSum k + constrainedProlateHermiteWeight (k + 1) := by
  rw [constrainedProlateHermiteWeightSum, constrainedProlateHermiteWeightSum,
    show k + 1 + 1 = (k + 1) + 1 by omega, Finset.sum_range_succ]

theorem constrainedProlateHermiteTheta_mem_Ioo (k : ℕ) :
    constrainedProlateHermiteTheta k ∈ Set.Ioo 0 1 := by
  have hQ := constrainedProlateHermiteWeightSum_pos k
  have hnext := constrainedProlateHermiteWeight_pos (k + 1)
  rw [constrainedProlateHermiteTheta, constrainedProlateHermiteWeightSum_succ]
  exact ⟨div_pos hQ (add_pos hQ hnext), (div_lt_one (add_pos hQ hnext)).2 (by linarith)⟩

/-- The `k`-th limiting contrast coordinate sequence from the card. -/
def constrainedProlateHermiteContrast (k j : ℕ) : ℝ :=
  if j ≤ k then -constrainedProlateHermiteCoordinate j
  else if j = k + 1 then
    constrainedProlateHermiteSquareSum k / constrainedProlateHermiteCoordinate (k + 1)
  else 0

theorem constrainedProlateHermiteContrast_of_le {k j : ℕ} (hj : j ≤ k) :
    constrainedProlateHermiteContrast k j = -constrainedProlateHermiteCoordinate j := by
  simp [constrainedProlateHermiteContrast, hj]

theorem constrainedProlateHermiteContrast_succ (k : ℕ) :
    constrainedProlateHermiteContrast k (k + 1) =
      constrainedProlateHermiteSquareSum k / constrainedProlateHermiteCoordinate (k + 1) := by
  simp [constrainedProlateHermiteContrast]

theorem constrainedProlateHermiteContrast_eq_zero_of_succ_lt
    {k j : ℕ} (hj : k + 1 < j) :
    constrainedProlateHermiteContrast k j = 0 := by
  rw [constrainedProlateHermiteContrast, if_neg (by omega), if_neg (by omega)]

/-- Every contrast vector lies in the limiting vanishing-integral hyperplane. -/
theorem constrainedProlateHermiteContrast_constraint (k : ℕ) :
    (∑ j ∈ Finset.range (k + 2),
      constrainedProlateHermiteContrast k j * constrainedProlateHermiteCoordinate j) = 0 := by
  rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ]
  have hhead :
      (∑ j ∈ Finset.range (k + 1),
        constrainedProlateHermiteContrast k j * constrainedProlateHermiteCoordinate j) =
        -constrainedProlateHermiteSquareSum k := by
    rw [constrainedProlateHermiteSquareSum]
    calc
      (∑ j ∈ Finset.range (k + 1),
          constrainedProlateHermiteContrast k j * constrainedProlateHermiteCoordinate j) =
          ∑ j ∈ Finset.range (k + 1), -(constrainedProlateHermiteCoordinate j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j ≤ k := by
          simp only [Finset.mem_range] at hj
          omega
        rw [constrainedProlateHermiteContrast_of_le hjk]
        ring
      _ = -(∑ j ∈ Finset.range (k + 1),
          constrainedProlateHermiteCoordinate j ^ 2) := by
        rw [Finset.sum_neg_distrib]
  rw [hhead, constrainedProlateHermiteContrast_succ]
  rw [div_mul_cancel₀ _ (constrainedProlateHermiteCoordinate_ne_zero (k + 1))]
  ring

/-- Finite pairing used to compare the `m`-th and `k`-th contrast vectors. -/
def constrainedProlateHermiteContrastPairing (m k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (max m k + 2),
    constrainedProlateHermiteContrast m j * constrainedProlateHermiteContrast k j

/-- Distinct fixed-depth Hermite contrast vectors are mutually orthogonal. -/
theorem constrainedProlateHermiteContrastPairing_eq_zero {m k : ℕ} (hmk : m < k) :
    constrainedProlateHermiteContrastPairing m k = 0 := by
  rw [constrainedProlateHermiteContrastPairing, max_eq_right hmk.le]
  have hsupport :
      (∑ j ∈ Finset.range (k + 2),
        constrainedProlateHermiteContrast m j * constrainedProlateHermiteContrast k j) =
      ∑ j ∈ Finset.range (m + 2),
        constrainedProlateHermiteContrast m j * constrainedProlateHermiteContrast k j := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hjbig hjsmall
    have hj : m + 1 < j := by
      simp only [Finset.mem_range] at hjbig hjsmall
      omega
    rw [constrainedProlateHermiteContrast_eq_zero_of_succ_lt hj, zero_mul]
  rw [hsupport]
  have hkhead : ∀ j ∈ Finset.range (m + 2),
      constrainedProlateHermiteContrast k j = -constrainedProlateHermiteCoordinate j := by
    intro j hj
    apply constrainedProlateHermiteContrast_of_le
    simp only [Finset.mem_range] at hj
    omega
  calc
    (∑ j ∈ Finset.range (m + 2),
        constrainedProlateHermiteContrast m j * constrainedProlateHermiteContrast k j) =
      -(∑ j ∈ Finset.range (m + 2),
        constrainedProlateHermiteContrast m j * constrainedProlateHermiteCoordinate j) := by
      calc
        (∑ j ∈ Finset.range (m + 2),
            constrainedProlateHermiteContrast m j * constrainedProlateHermiteContrast k j) =
            ∑ j ∈ Finset.range (m + 2),
              -(constrainedProlateHermiteContrast m j *
                constrainedProlateHermiteCoordinate j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hkhead j hj]
          ring
        _ = -(∑ j ∈ Finset.range (m + 2),
            constrainedProlateHermiteContrast m j * constrainedProlateHermiteCoordinate j) :=
          by rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [constrainedProlateHermiteContrast_constraint, neg_zero]

/-- The raw CCM Hermite contrast `r_m = a_0 e_m - a_m e_0`. -/
def constrainedProlateRawHermiteContrast (m j : ℕ) : ℝ :=
  if j = m then constrainedProlateHermiteCoordinate 0
  else if j = 0 then -constrainedProlateHermiteCoordinate m
  else 0

/-- The `k`-th spectral contrast is orthogonal to every preceding raw CCM contrast. -/
theorem constrainedProlateHermiteContrast_raw_orthogonal
    {k m : ℕ} (hm0 : 0 < m) (hmk : m ≤ k) :
    (∑ j ∈ Finset.range (k + 2),
      constrainedProlateHermiteContrast k j * constrainedProlateRawHermiteContrast m j) = 0 := by
  have hmrange : m ∈ Finset.range (k + 2) := by simp only [Finset.mem_range]; omega
  have h0range : 0 ∈ Finset.range (k + 2) := by simp
  have hraw (j : ℕ) : constrainedProlateRawHermiteContrast m j =
      (if j = m then constrainedProlateHermiteCoordinate 0 else 0) +
      (if j = 0 then -constrainedProlateHermiteCoordinate m else 0) := by
    rw [constrainedProlateRawHermiteContrast]
    by_cases hjm : j = m
    · subst j
      simp [hm0.ne']
    · by_cases hj0 : j = 0
      · subst j
        simp [Nat.ne_of_lt hm0]
      · simp [hjm, hj0]
  simp_rw [hraw, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.range (k + 2)) m, if_pos hmrange,
    Finset.sum_ite_eq' (Finset.range (k + 2)) 0, if_pos h0range,
    constrainedProlateHermiteContrast_of_le hmk,
    constrainedProlateHermiteContrast_of_le (Nat.zero_le k)]
  ring

/-! ## Exact first constants -/

@[simp] theorem constrainedProlateHermiteWeight_zero :
    constrainedProlateHermiteWeight 0 = 1 := by
  norm_num [constrainedProlateHermiteWeight]

@[simp] theorem constrainedProlateHermiteWeight_one :
    constrainedProlateHermiteWeight 1 = 3 / 8 := by
  norm_num [constrainedProlateHermiteWeight, Nat.choose]

@[simp] theorem constrainedProlateHermiteWeight_two :
    constrainedProlateHermiteWeight 2 = 35 / 128 := by
  norm_num [constrainedProlateHermiteWeight, Nat.choose]

@[simp] theorem constrainedProlateHermiteWeightSum_zero :
    constrainedProlateHermiteWeightSum 0 = 1 := by
  norm_num [constrainedProlateHermiteWeightSum]

@[simp] theorem constrainedProlateHermiteWeightSum_one :
    constrainedProlateHermiteWeightSum 1 = 11 / 8 := by
  norm_num [constrainedProlateHermiteWeightSum, constrainedProlateHermiteWeight,
    Finset.sum_range_succ, Nat.choose]

@[simp] theorem constrainedProlateHermiteWeightSum_two :
    constrainedProlateHermiteWeightSum 2 = 211 / 128 := by
  norm_num [constrainedProlateHermiteWeightSum, constrainedProlateHermiteWeight,
    Finset.sum_range_succ, Nat.choose]

theorem constrainedProlateHermiteTheta_zero :
    constrainedProlateHermiteTheta 0 = 8 / 11 := by
  norm_num [constrainedProlateHermiteTheta]

theorem constrainedProlateHermiteTheta_one :
    constrainedProlateHermiteTheta 1 = 176 / 211 := by
  norm_num [constrainedProlateHermiteTheta]

/-- The first adjacent constrained-ladder coefficient
`Q_1^2/(Q_0 Q_2) = 242/211`. -/
theorem constrainedProlateHermiteFirstAdjacentCoefficient :
    constrainedProlateHermiteWeightSum 1 ^ 2 /
      (constrainedProlateHermiteWeightSum 0 * constrainedProlateHermiteWeightSum 2) =
      242 / 211 := by
  norm_num

end

end RHTower
