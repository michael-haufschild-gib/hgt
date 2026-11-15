import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisTranslationColumns

/-!
# Transverse shear columns strictly lower the remaining binary degree

In `z ↦ z+η yᵢ`, replacing a vertical power by a `yᵢ` power increases one
fixed exponent and leaves the active horizontal exponent unchanged. Every
nonidentity term therefore moves to a chain of strictly smaller binary
degree. This is the second triangular filtration for general directions.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Increase one untouched-variable exponent by `q`. -/
def raiseChainExponent {r : ℕ} (β : Fin r → ℕ) (i : Fin r) (q : ℕ) : Fin r → ℕ :=
  fun j => β j + if j = i then q else 0

theorem sum_raiseChainExponent {r : ℕ} (β : Fin r → ℕ) (i : Fin r) (q : ℕ) :
    (∑ j, raiseChainExponent β i q j) = (∑ j, β j) + q := by
  unfold raiseChainExponent
  rw [Finset.sum_add_distrib]
  simp

theorem raiseChainExponent_zero {r : ℕ} (β : Fin r → ℕ) (i : Fin r) :
    raiseChainExponent β i 0 = β := by
  funext j
  simp only [raiseChainExponent, ite_self, add_zero]

/-- Increasing one exponent multiplies the monomial by the corresponding coordinate power. -/
theorem prod_raiseChainExponent {r : ℕ} (β : Fin r → ℕ) (i : Fin r) (q : ℕ) (y : Fin r → ℝ) :
    (∏ j, y j ^ raiseChainExponent β i q j) = (∏ j, y j ^ β j) * y i ^ q := by
  have hpoint (j : Fin r) : y j ^ raiseChainExponent β i q j =
      y j ^ β j * (if j = i then y i ^ q else 1) := by
    by_cases h : j = i
    · subst j
      simp only [raiseChainExponent, ite_true, pow_add]
    · simp only [raiseChainExponent, if_neg h, add_zero, mul_one]
  simp only [hpoint, Finset.prod_mul_distrib]
  simp

/-- A vertical-to-horizontal transfer stays within the same total-degree bound. -/
theorem raiseChainExponent_bound {r d : ℕ} (a : HomogeneousChain r d)
    (v : Fin (chainDegree a + 1)) (i : Fin r) (j : Fin (v.val + 1)) :
    ∑ l, raiseChainExponent (chainExponent a) i (v.val - j.val) l ≤ d := by
  rw [sum_raiseChainExponent]
  have h := sum_chainExponent_add_degree r d a
  have hv := v.isLt
  omega

/-- The monomial coordinate receiving the `j`-th vertical term of a transverse shear. -/
def tailShearColumn {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) : HomogeneousAxisIndex r d := by
  let b := (chainEquivBounded r d).symm
    ⟨raiseChainExponent (chainExponent a.1) i (a.2.val - j.val),
      raiseChainExponent_bound a.1 a.2 i j⟩
  have hb : chainExponent b = raiseChainExponent (chainExponent a.1) i (a.2.val - j.val) :=
    congrArg Subtype.val ((chainEquivBounded r d).apply_symm_apply
      ⟨_, raiseChainExponent_bound a.1 a.2 i j⟩)
  have h0 := sum_chainExponent_add_degree r d a.1
  have h1 := sum_chainExponent_add_degree r d b
  rw [hb, sum_raiseChainExponent] at h1
  have hv := a.2.isLt
  have hj := j.isLt
  exact ⟨b, ⟨j.val, by omega⟩⟩

theorem tailShearColumn_vertical {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) : (tailShearColumn a i j).2.val = j.val := rfl

theorem tailShearColumn_exponent {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) :
    chainExponent (tailShearColumn a i j).1 =
      raiseChainExponent (chainExponent a.1) i (a.2.val - j.val) :=
  congrArg Subtype.val ((chainEquivBounded r d).apply_symm_apply
    ⟨_, raiseChainExponent_bound a.1 a.2 i j⟩)

/-- Transferring vertical powers lowers the binary chain degree by exactly the transferred amount. -/
theorem tailShearColumn_degree {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) :
    chainDegree (tailShearColumn a i j).1 + (a.2.val - j.val) = chainDegree a.1 := by
  have h0 := sum_chainExponent_add_degree r d a.1
  have h1 := sum_chainExponent_add_degree r d (tailShearColumn a i j).1
  rw [tailShearColumn_exponent, sum_raiseChainExponent] at h1
  omega

/-- The distinguished horizontal exponent is unchanged. -/
theorem tailShearColumn_horizontal {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) :
    chainDegree (tailShearColumn a i j).1 - (tailShearColumn a i j).2.val =
      chainDegree a.1 - a.2.val := by
  have h := tailShearColumn_degree a i j
  have hv := tailShearColumn_vertical a i j
  have hj := j.isLt
  omega

theorem homogeneousAxisIndex_ext {r d : ℕ} {a b : HomogeneousAxisIndex r d}
    (hβ : chainExponent a.1 = chainExponent b.1) (hv : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  have hab : a = b := chainExponent_injective r d hβ
  subst b
  have hij : i = j := Fin.ext hv
  subst j
  rfl

/-- The untransferred binomial term is the original monomial. -/
theorem tailShearColumn_last {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r) :
    tailShearColumn a i (Fin.last a.2.val) = a := by
  apply homogeneousAxisIndex_ext
  · rw [tailShearColumn_exponent, Fin.val_last, Nat.sub_self, raiseChainExponent_zero]
  · rfl

/-- Every transverse-shear term is either the original coordinate or strictly lowers chain rank. -/
theorem tailShearColumn_eq_or_degree_lt {r d : ℕ} (a : HomogeneousAxisIndex r d) (i : Fin r)
    (j : Fin (a.2.val + 1)) :
    tailShearColumn a i j = a ∨ chainDegree (tailShearColumn a i j).1 < chainDegree a.1 := by
  by_cases h : j.val = a.2.val
  · have hj : j = Fin.last a.2.val := Fin.ext h
    subst j
    exact Or.inl (tailShearColumn_last a i)
  · right
    have hj := j.isLt
    have hd := tailShearColumn_degree a i j
    omega

/-- Scalar coordinates of all homogeneous monomials in the chosen chain ordering. -/
def homogeneousAxisMoment (r d : ℕ) (y : Fin r → ℝ) (x z : ℝ) : HomogeneousAxisIndex r d → ℝ :=
  fun a => chainMoment r d y x z a.1 a.2

/-- The receiving column has exactly the expected transferred-power monomial. -/
theorem homogeneousAxisMoment_tailShearColumn (r d : ℕ) (y : Fin r → ℝ) (x z : ℝ)
    (a : HomogeneousAxisIndex r d) (i : Fin r) (j : Fin (a.2.val + 1)) :
    homogeneousAxisMoment r d y x z (tailShearColumn a i j) =
      (∏ l, y l ^ chainExponent a.1 l) *
        (x ^ (chainDegree a.1 - a.2.val) * (y i ^ (a.2.val - j.val) * z ^ j.val)) := by
  change (∏ l, y l ^ chainExponent (tailShearColumn a i j).1 l) *
    (x ^ (chainDegree (tailShearColumn a i j).1 - (tailShearColumn a i j).2.val) *
      z ^ (tailShearColumn a i j).2.val) = _
  rw [tailShearColumn_exponent, prod_raiseChainExponent, tailShearColumn_horizontal,
    tailShearColumn_vertical]
  ring

#print axioms sum_raiseChainExponent
#print axioms prod_raiseChainExponent
#print axioms tailShearColumn_degree
#print axioms homogeneousAxisIndex_ext
#print axioms tailShearColumn_last
#print axioms tailShearColumn_eq_or_degree_lt
#print axioms homogeneousAxisMoment_tailShearColumn

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
