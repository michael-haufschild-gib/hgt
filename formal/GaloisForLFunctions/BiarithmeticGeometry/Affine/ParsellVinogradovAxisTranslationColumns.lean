import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisChains

/-!
# Translation columns for multivariate moment coordinates

Replacing a vertical exponent by a smaller one preserves every horizontal
exponent. The chain equivalence supplies the unique coordinate in the lower
total degree. These explicit columns give the binomial translation matrix
without a choice of polynomial basis or a coefficient-independence premise.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

instance homogeneousChainDecidableEq (r d : ℕ) : DecidableEq (HomogeneousChain r d) :=
  Classical.decEq _

/-- Move a fixed exponent tuple to another admissible total degree. -/
def regradeChain {r d : ℕ} (a : HomogeneousChain r d) (e : ℕ)
    (he : ∑ i, chainExponent a i ≤ e) : HomogeneousChain r e :=
  (chainEquivBounded r e).symm ⟨chainExponent a, he⟩

theorem regradeChain_exponent {r d : ℕ} (a : HomogeneousChain r d) (e : ℕ)
    (he : ∑ i, chainExponent a i ≤ e) :
    chainExponent (regradeChain a e he) = chainExponent a := by
  exact congrArg Subtype.val ((chainEquivBounded r e).apply_symm_apply ⟨chainExponent a, he⟩)

/-- Scalar coordinates for all monomials through degree `k`, including the constant. -/
abbrev HomogeneousAxisIndex (r d : ℕ) :=
  Σ a : HomogeneousChain r d, Fin (chainDegree a + 1)
abbrev FullAxisIndex (r k : ℕ) :=
  Σ d : Fin (k + 1), HomogeneousAxisIndex r d.val
abbrev FullAxisSpace (r k : ℕ) := FullAxisIndex r k → ℝ

/-- A monomial coordinate is determined by its total, fixed, and vertical exponents. -/
theorem fullAxisIndex_ext {r k : ℕ} {a b : FullAxisIndex r k}
    (hd : a.1.val = b.1.val) (hβ : chainExponent a.2.1 = chainExponent b.2.1)
    (hv : a.2.2.val = b.2.2.val) : a = b := by
  rcases a with ⟨d, a, i⟩
  rcases b with ⟨e, b, j⟩
  have hde : d = e := Fin.ext hd
  subst e
  have hab : a = b := chainExponent_injective r d.val hβ
  subst b
  have hij : i = j := Fin.ext hv
  subst j
  rfl

/-- The fixed, horizontal, and vertical exponents add to total degree. -/
theorem fullAxisIndex_degree (r k : ℕ) (a : FullAxisIndex r k) :
    (∑ i, chainExponent a.2.1 i) + (chainDegree a.2.1 - a.2.2.val) + a.2.2.val = a.1.val := by
  have h := sum_chainExponent_add_degree r a.1.val a.2.1
  have hv := a.2.2.isLt
  omega

/-- The actual polynomial moment vector in scalar coordinates. -/
def fullAxisMoment (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ) : FullAxisSpace r k :=
  fun a => (∏ i, y i ^ chainExponent a.2.1 i) *
    (x ^ (chainDegree a.2.1 - a.2.2.val) * z ^ a.2.2.val)

/-- Translation preserves horizontal exponents and replaces the vertical exponent by `j`. -/
def axisTranslationColumn {r k : ℕ} (a : FullAxisIndex r k) (j : Fin (a.2.2.val + 1)) :
    FullAxisIndex r k := by
  have hd := fullAxisIndex_degree r k a
  have hj := j.isLt
  have hk := a.1.isLt
  let e : Fin (k + 1) := ⟨a.1.val - a.2.2.val + j.val, by omega⟩
  have he : ∑ i, chainExponent a.2.1 i ≤ e.val := by dsimp only [e]; omega
  let b := regradeChain a.2.1 e.val he
  have hb : chainExponent b = chainExponent a.2.1 := regradeChain_exponent _ _ _
  have hbd := sum_chainExponent_add_degree r e.val b
  rw [hb] at hbd
  refine ⟨e, b, ⟨j.val, ?_⟩⟩
  dsimp only [e] at hbd
  omega

theorem axisTranslationColumn_total {r k : ℕ} (a : FullAxisIndex r k)
    (j : Fin (a.2.2.val + 1)) :
    (axisTranslationColumn a j).1.val = a.1.val - a.2.2.val + j.val := rfl

theorem axisTranslationColumn_vertical {r k : ℕ} (a : FullAxisIndex r k)
    (j : Fin (a.2.2.val + 1)) : (axisTranslationColumn a j).2.2.val = j.val := rfl

theorem axisTranslationColumn_exponent {r k : ℕ} (a : FullAxisIndex r k)
    (j : Fin (a.2.2.val + 1)) :
    chainExponent (axisTranslationColumn a j).2.1 = chainExponent a.2.1 :=
  regradeChain_exponent _ _ _

/-- The horizontal active exponent is unchanged by vertical translation. -/
theorem axisTranslationColumn_horizontal {r k : ℕ} (a : FullAxisIndex r k)
    (j : Fin (a.2.2.val + 1)) :
    chainDegree (axisTranslationColumn a j).2.1 - (axisTranslationColumn a j).2.2.val =
      chainDegree a.2.1 - a.2.2.val := by
  have h0 := fullAxisIndex_degree r k a
  have h1 := fullAxisIndex_degree r k (axisTranslationColumn a j)
  have ht := axisTranslationColumn_total a j
  have hv := axisTranslationColumn_vertical a j
  rw [axisTranslationColumn_exponent] at h1
  omega

/-- The last term of the binomial expansion is the original coordinate. -/
theorem axisTranslationColumn_last {r k : ℕ} (a : FullAxisIndex r k) :
    axisTranslationColumn a (Fin.last a.2.2.val) = a := by
  apply fullAxisIndex_ext
  · rw [axisTranslationColumn_total, Fin.val_last]
    have h := fullAxisIndex_degree r k a
    omega
  · exact axisTranslationColumn_exponent _ _
  · rfl

/-- Every translation column represents precisely its expected lower vertical monomial. -/
theorem fullAxisMoment_translationColumn (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ)
    (a : FullAxisIndex r k) (j : Fin (a.2.2.val + 1)) :
    fullAxisMoment r k y x z (axisTranslationColumn a j) =
      (∏ i, y i ^ chainExponent a.2.1 i) *
        (x ^ (chainDegree a.2.1 - a.2.2.val) * z ^ j.val) := by
  simp only [fullAxisMoment, axisTranslationColumn_exponent]
  rw [axisTranslationColumn_horizontal, axisTranslationColumn_vertical]

/-- On the diagonal, each homogeneous monomial is the corresponding power of the common value. -/
theorem fullAxisMoment_diagonal (r k : ℕ) (s : ℝ) (a : FullAxisIndex r k) :
    fullAxisMoment r k (fun _ => s) s s a = s ^ a.1.val := by
  unfold fullAxisMoment
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add]
  congr 1
  have h := fullAxisIndex_degree r k a
  omega

/-- Every degree-zero coordinate is the constant monomial. -/
theorem fullAxisMoment_degree_zero (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ)
    (a : FullAxisIndex r k) (ha : a.1.val = 0) : fullAxisMoment r k y x z a = 1 := by
  have h := fullAxisIndex_degree r k a
  have hs : (∑ i, chainExponent a.2.1 i) = 0 := by omega
  have hx : chainDegree a.2.1 - a.2.2.val = 0 := by omega
  have hz : a.2.2.val = 0 := by omega
  have hβ (i : Fin r) : chainExponent a.2.1 i = 0 := by
    have hi : chainExponent a.2.1 i ≤ ∑ j, chainExponent a.2.1 j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (chainExponent a.2.1 j)) (Finset.mem_univ i)
    omega
  simp only [fullAxisMoment, hβ]
  rw [hx, hz]
  simp only [pow_zero, Finset.prod_const_one, one_mul]

/-- Only the constant coordinate survives at the origin. -/
theorem fullAxisMoment_zero (r k : ℕ) (a : FullAxisIndex r k) :
    fullAxisMoment r k 0 0 0 a = if a.1.val = 0 then 1 else 0 := by
  change fullAxisMoment r k (fun _ => 0) 0 0 a = _
  rw [fullAxisMoment_diagonal]
  by_cases h : a.1.val = 0
  · rw [h, pow_zero, if_pos rfl]
  · rw [zero_pow h, if_neg h]

#print axioms fullAxisIndex_ext
#print axioms fullAxisIndex_degree
#print axioms axisTranslationColumn_horizontal
#print axioms axisTranslationColumn_last
#print axioms fullAxisMoment_translationColumn
#print axioms fullAxisMoment_diagonal
#print axioms fullAxisMoment_degree_zero
#print axioms fullAxisMoment_zero

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
