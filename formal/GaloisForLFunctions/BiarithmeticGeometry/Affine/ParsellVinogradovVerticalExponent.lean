import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisExponent
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisFrames

/-!
# The anisotropic volume exponent of the full moment basis

Vertical dilation weights a monomial by its vertical exponent. In each
binary chain these exponents run from zero to the chain degree. Adjoining
an untouched variable takes a prefix sum, so the total weight through
degree `k` in `r+2` variables is `choose (r+k+2) (r+3)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Total vertical weight among the monomials of one homogeneous degree. -/
def homogeneousVerticalExponent (r d : ℕ) : ℕ :=
  ∑ a : HomogeneousChain r d, ∑ j : Fin (chainDegree a + 1), j.val

/-- Total vertical weight among all nonconstant monomials through degree `k`. -/
def verticalExponent (r k : ℕ) : ℕ :=
  ∑ d ∈ Finset.range k, homogeneousVerticalExponent r (d + 1)

theorem homogeneousVerticalExponent_zero (r : ℕ) : homogeneousVerticalExponent r 0 = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hd : chainDegree a = 0 := by
    have h := sum_chainExponent_add_degree r 0 a
    omega
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.isLt
  omega

theorem verticalExponent_zero (r : ℕ) : verticalExponent r 0 = 0 := by
  simp only [verticalExponent, Finset.range_zero, Finset.sum_empty]

private theorem sum_fin_values (d : ℕ) :
    (∑ j : Fin (d + 1), j.val) = (d + 1).choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (d + 1)]
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Nat.choose_succ_succ (d + 1) 1
    rw [Nat.choose_one_right] at h
    change (d + 1 + 1).choose 2 = d + 1 + (d + 1).choose 2 at h
    omega

/-- In two variables, a homogeneous chain contributes a triangular number. -/
theorem homogeneousVerticalExponent_binary (d : ℕ) :
    homogeneousVerticalExponent 0 d = (d + 1).choose 2 := by
  change (∑ _ : PUnit, ∑ j : Fin (d + 1), j.val) = (d + 1).choose 2
  simpa using sum_fin_values d

/-- Choosing one additional untouched exponent sums all remaining vertical weights. -/
theorem homogeneousVerticalExponent_succ (r d : ℕ) :
    homogeneousVerticalExponent (r + 1) d = verticalExponent r d := by
  change (∑ a : (Σ j : Fin (d + 1), HomogeneousChain r (d - j.val)),
    ∑ v : Fin (chainDegree a.2 + 1), v.val) = _
  rw [Fintype.sum_sigma]
  change (∑ j : Fin (d + 1), homogeneousVerticalExponent r (d - j.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => homogeneousVerticalExponent r (d - j)) (d + 1)]
  have hreflect : (∑ j ∈ Finset.range (d + 1), homogeneousVerticalExponent r (d - j)) =
      ∑ j ∈ Finset.range (d + 1), homogeneousVerticalExponent r j := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (homogeneousVerticalExponent r) (d + 1)
  rw [hreflect, Finset.sum_range_succ', homogeneousVerticalExponent_zero, add_zero]
  rfl

/-- Every additional untouched variable takes one prefix sum of the preceding total weight. -/
theorem verticalExponent_succ (r k : ℕ) :
    verticalExponent (r + 1) k = ∑ d ∈ Finset.range (k + 1), verticalExponent r d := by
  conv_lhs => unfold verticalExponent
  simp only [homogeneousVerticalExponent_succ]
  rw [Finset.sum_range_succ', verticalExponent_zero, add_zero]

/-- Summing binary triangular weights gives the cubic binomial coefficient. -/
theorem verticalExponent_binary (k : ℕ) : verticalExponent 0 k = (k + 2).choose 3 := by
  cases k with
  | zero => norm_num [verticalExponent]
  | succ k =>
    simpa only [verticalExponent, homogeneousVerticalExponent_binary, Nat.add_assoc] using
      Nat.sum_range_add_choose k 2

/-- The exact anisotropic volume exponent is `A_(r+2,k)`. -/
theorem verticalExponent_eq_binomial (r k : ℕ) :
    verticalExponent r k = (r + k + 2).choose (r + 3) := by
  induction r generalizing k with
  | zero => simpa only [Nat.zero_add] using verticalExponent_binary k
  | succ r ih =>
    cases k with
    | zero =>
        rw [verticalExponent_zero]
        simpa only [Nat.add_zero, Nat.add_assoc] using (Nat.choose_succ_self (r + 3)).symm
    | succ k =>
        rw [verticalExponent_succ, Finset.sum_range_succ', verticalExponent_zero, add_zero]
        simp only [ih]
        calc
          _ = ∑ d ∈ Finset.range (k + 1), (d + (r + 3)).choose (r + 3) := by
            apply Finset.sum_congr rfl
            intro d _
            congr 1
            omega
          _ = _ := by
            rw [Nat.sum_range_add_choose]
            congr 1
            omega

/-- The scalar monomial coordinates have exactly the recursively counted total vertical weight. -/
theorem sum_verticalAxisIndex (r k : ℕ) :
    (∑ a : AffineAxisIndex r k, a.2.2.val) = verticalExponent r k := by
  simp only [Fintype.sum_sigma]
  change (∑ d : Fin k, homogeneousVerticalExponent r (d.val + 1)) = verticalExponent r k
  exact Fin.sum_univ_eq_sum_range (fun d : ℕ => homogeneousVerticalExponent r (d + 1)) k

/-- The volume exponent is the sum of the sharp overlap exponents in two adjacent degrees. -/
theorem verticalExponent_eq_adjacent_axisExponent (r k : ℕ) :
    verticalExponent r (k + 1) = axisExponent r k + axisExponent r (k + 1) := by
  simpa only [verticalExponent_eq_binomial, Nat.add_assoc] using (axisExponent_adjacent r k).symm

theorem verticalExponent_one (r : ℕ) : verticalExponent r 1 = 1 := by
  simpa only [axisExponent_zero, axisExponent_one, zero_add] using
    verticalExponent_eq_adjacent_axisExponent r 0

/-- Adding degrees increases the total vertical weight. -/
theorem verticalExponent_monotone (r : ℕ) : Monotone (verticalExponent r) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (f := fun d => homogeneousVerticalExponent r (d + 1))
    (Finset.range_mono hab)

/-- Every positive degree includes the vertical linear monomial. -/
theorem verticalExponent_pos (r k : ℕ) : 0 < verticalExponent r (k + 1) := by
  have h := verticalExponent_monotone r (show 1 ≤ k + 1 by omega)
  rw [verticalExponent_one] at h
  omega

#print axioms homogeneousVerticalExponent_binary
#print axioms homogeneousVerticalExponent_succ
#print axioms verticalExponent_succ
#print axioms verticalExponent_binary
#print axioms verticalExponent_eq_binomial
#print axioms sum_verticalAxisIndex
#print axioms verticalExponent_eq_adjacent_axisExponent
#print axioms verticalExponent_one
#print axioms verticalExponent_monotone
#print axioms verticalExponent_pos

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
