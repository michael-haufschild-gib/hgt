import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisChains
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBinaryExponent
import Mathlib.Data.Nat.Choose.Sum

/-!
# The multivariate chain exponent equals the proposed binomial sum

Adjoining an untouched variable takes a prefix sum of the binary-chain
exponents. Adjacent prefix sums satisfy the hockey-stick identity. This
gives a two-degree recurrence and identifies the exact chain exponent in
`r+2` variables with the proposed sum of binomial coefficients.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The sum of quarter-square powers among chains of one homogeneous degree. -/
def homogeneousAxisExponent (r d : ℕ) : ℕ :=
  ∑ a : HomogeneousChain r d, (chainDegree a + 1) ^ 2 / 4

/-- The chain exponent for all nonconstant moments through degree `k` in `r+2` variables. -/
def axisExponent (r k : ℕ) : ℕ :=
  ∑ d ∈ Finset.range k, homogeneousAxisExponent r (d + 1)

theorem homogeneousAxisExponent_zero (r : ℕ) : homogeneousAxisExponent r 0 = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hd : chainDegree a = 0 := by
    have h := sum_chainExponent_add_degree r 0 a
    omega
  rw [hd]
  norm_num

theorem axisExponent_zero (r : ℕ) : axisExponent r 0 = 0 := by
  simp only [axisExponent, Finset.range_zero, Finset.sum_empty]

/-- In two variables there is one chain per homogeneous degree. -/
theorem axisExponent_binary (k : ℕ) : axisExponent 0 k = binaryExponent k := by
  unfold axisExponent binaryExponent
  apply Finset.sum_congr rfl
  intro d _
  simp [homogeneousAxisExponent, HomogeneousChain, chainDegree, Nat.add_assoc]

/-- Choosing the exponent of one extra variable sums every remaining binary degree. -/
theorem homogeneousAxisExponent_succ (r d : ℕ) :
    homogeneousAxisExponent (r + 1) d = axisExponent r d := by
  change (∑ a : (Σ j : Fin (d + 1), HomogeneousChain r (d - j.val)),
    (chainDegree a.2 + 1) ^ 2 / 4) = _
  rw [Fintype.sum_sigma]
  change (∑ j : Fin (d + 1), homogeneousAxisExponent r (d - j.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => homogeneousAxisExponent r (d - j)) (d + 1)]
  have hreflect : (∑ j ∈ Finset.range (d + 1), homogeneousAxisExponent r (d - j)) =
      ∑ j ∈ Finset.range (d + 1), homogeneousAxisExponent r j := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (homogeneousAxisExponent r) (d + 1)
  rw [hreflect, Finset.sum_range_succ', homogeneousAxisExponent_zero, add_zero]
  rfl

/-- Every added untouched variable takes one prefix sum of the preceding exponent. -/
theorem axisExponent_succ (r k : ℕ) :
    axisExponent (r + 1) k = ∑ d ∈ Finset.range (k + 1), axisExponent r d := by
  conv_lhs => unfold axisExponent
  simp only [homogeneousAxisExponent_succ]
  rw [Finset.sum_range_succ', axisExponent_zero, add_zero]

theorem axisExponent_one (r : ℕ) : axisExponent r 1 = 1 := by
  induction r with
  | zero => rw [axisExponent_binary]; norm_num [binaryExponent]
  | succ r ih =>
    rw [axisExponent_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      axisExponent_zero, zero_add, ih]

private theorem binaryExponent_adjacent (k : ℕ) :
    binaryExponent k + binaryExponent (k + 1) = (k + 3).choose 3 := by
  induction k with
  | zero => norm_num [binaryExponent]
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by omega, binaryExponent_two_step]
    have hpascal := Nat.choose_succ_succ (k + 3) 2
    change (k + 4).choose 3 = (k + 3).choose 2 + (k + 3).choose 3 at hpascal
    omega

/-- Adjacent total-degree exponents form one binomial coefficient in every dimension. -/
theorem axisExponent_adjacent (r k : ℕ) :
    axisExponent r k + axisExponent r (k + 1) = (r + k + 3).choose (r + 3) := by
  induction r generalizing k with
  | zero => simpa only [axisExponent_binary, Nat.zero_add] using binaryExponent_adjacent k
  | succ r ih =>
    rw [axisExponent_succ, axisExponent_succ]
    rw [Finset.sum_range_succ' (axisExponent r) (k + 1), axisExponent_zero, add_zero,
      ← Finset.sum_add_distrib]
    simp only [ih]
    have hsum := Nat.sum_range_add_choose k (r + 3)
    have hterm (i : ℕ) : r + i + 3 = i + (r + 3) := by omega
    simp only [hterm]
    convert hsum using 1 <;> congr 1 <;> omega

/-- Two additional degrees contribute a single binomial coefficient. -/
theorem axisExponent_two_step (r k : ℕ) :
    axisExponent r (k + 2) = axisExponent r k + (r + k + 3).choose (r + 2) := by
  have h0 := axisExponent_adjacent r k
  have h1 := axisExponent_adjacent r (k + 1)
  have hp := Nat.choose_succ_succ (r + k + 3) (r + 2)
  change (r + k + 4).choose (r + 3) =
    (r + k + 3).choose (r + 2) + (r + k + 3).choose (r + 3) at hp
  have he : r + (k + 1) + 3 = r + k + 4 := by omega
  rw [he] at h1
  omega

private def axisBinomialSum (r k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2)

private theorem axisBinomialSum_two_step (r k : ℕ) :
    axisBinomialSum r (k + 2) = axisBinomialSum r k + (r + k + 3).choose (r + 2) := by
  rw [axisBinomialSum, show (k + 2 + 1) / 2 = (k + 1) / 2 + 1 by omega,
    Finset.sum_range_succ']
  have hterm (j : ℕ) : (r + (k + 2) + 1 - 2 * (j + 1)).choose (r + 2) =
      (r + k + 1 - 2 * j).choose (r + 2) := by
    congr 1
    omega
  simp only [hterm, Nat.mul_zero, Nat.sub_zero]
  rfl

/-- The exact chain exponent is the proposed `B_(r+2,k)` in every dimension and degree. -/
theorem axisExponent_eq_binomial_sum (r k : ℕ) :
    axisExponent r k =
      ∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) := by
  change axisExponent r k = axisBinomialSum r k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h0 : k = 0
    · subst k
      simp [axisExponent_zero, axisBinomialSum]
    by_cases h1 : k = 1
    · subst k
      simp [axisExponent_one, axisBinomialSum, Nat.add_assoc]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
    rw [axisExponent_two_step, axisBinomialSum_two_step, ih n (by omega)]

#print axioms axisExponent_binary
#print axioms homogeneousAxisExponent_succ
#print axioms axisExponent_succ
#print axioms axisExponent_adjacent
#print axioms axisExponent_two_step
#print axioms axisExponent_eq_binomial_sum

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
