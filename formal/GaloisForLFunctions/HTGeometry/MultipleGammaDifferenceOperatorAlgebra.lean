import GaloisForLFunctions.HTGeometry.MultipleGammaMonomialCoefficients

/-!
# The difference-operator action is an algebra action

Multidegrees add exactly when their direction lists concatenate up to permutation, and iterated
structural differences depend only on the multiset of directions.  Hence the monomial action
composes: `x^(d + d')` acts as `x^d` after `x^d'`.

Together with linearity in the germ this makes the difference variables act as commuting
`ℂ`-linear operators, so a difference operator acts through its monomial expansion, and the unit
translation `1 + x_j` acts as the structural translation itself.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Multidegrees add by concatenation -/

omit [Fintype ι] in
theorem multiDegreeList_add_perm (d d' : ι →₀ ℕ) :
    (multiDegreeList (d + d')).Perm (multiDegreeList d ++ multiDegreeList d') := by
  classical
  rw [List.perm_iff_count]
  intro a
  rw [count_multiDegreeList, List.count_append, count_multiDegreeList, count_multiDegreeList]
  simp

omit [Fintype ι] in
/-- **Monomial composition.**  Adding multidegrees composes the corresponding iterated
differences. -/
theorem xMonomialApply_add (τ : ι → ℂ) (d d' : ι →₀ ℕ) (y : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ (d + d') y = xMonomialApply τ d (xMonomialApply τ d' y) := by
  rw [xMonomialApply, xMonomialApply, xMonomialApply,
    listShiftDiff_perm τ (multiDegreeList_add_perm d d'), listShiftDiff_append]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem xMonomialApply_zero (τ : ι → ℂ) (y : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ 0 y = y := by
  classical
  rw [xMonomialApply, multiDegreeList]
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem multiDegreeList_single (j : ι) : multiDegreeList (Finsupp.single j 1) = [j] := by
  classical
  have hsupp : (Finsupp.single j (1 : ℕ)).support = {j} := by
    simp
  rw [multiDegreeList, hsupp]
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem xMonomialApply_single (τ : ι → ℂ) (j : ι) (y : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ (Finsupp.single j 1) y = meroShiftDiff (τ j) y := by
  rw [xMonomialApply, multiDegreeList_single, listShiftDiff_cons, listShiftDiff_nil]

/-! ## Linearity in the germ -/

omit [Fintype ι] [DecidableEq ι] in
theorem meroShiftDiff_complexMul (q c : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    meroShiftDiff q (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * meroShiftDiff q y := by
  rw [meroShiftDiff, meroShiftDiff, map_mul, addTranslationMeroEquiv_algebraMap_complex, mul_sub]

omit [Fintype ι] [DecidableEq ι] in
theorem meroShiftDiff_add (q : ℂ) (y z : meroField (Set.univ : Set ℂ)) :
    meroShiftDiff q (y + z) = meroShiftDiff q y + meroShiftDiff q z := by
  rw [meroShiftDiff, meroShiftDiff, meroShiftDiff, map_add]
  abel

omit [Fintype ι] [DecidableEq ι] in
theorem listShiftDiff_complexMul (τ : ι → ℂ) (l : List ι) (c : ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ l (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * listShiftDiff τ l y := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [listShiftDiff_cons, ih, meroShiftDiff_complexMul, listShiftDiff_cons]

omit [Fintype ι] [DecidableEq ι] in
theorem listShiftDiff_add (τ : ι → ℂ) (l : List ι) (y z : meroField (Set.univ : Set ℂ)) :
    listShiftDiff τ l (y + z) = listShiftDiff τ l y + listShiftDiff τ l z := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [listShiftDiff_cons, ih, meroShiftDiff_add, listShiftDiff_cons,
      listShiftDiff_cons]

omit [Fintype ι] [DecidableEq ι] in
theorem xMonomialApply_complexMul (τ : ι → ℂ) (d : ι →₀ ℕ) (c : ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ d (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * xMonomialApply τ d y :=
  listShiftDiff_complexMul τ (multiDegreeList d) c y

omit [Fintype ι] [DecidableEq ι] in
theorem xMonomialApply_add_germ (τ : ι → ℂ) (d : ι →₀ ℕ)
    (y z : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ d (y + z) = xMonomialApply τ d y + xMonomialApply τ d z :=
  listShiftDiff_add τ (multiDegreeList d) y z

/-! ## The unit translation -/

omit [Fintype ι] [DecidableEq ι] in
/-- **`1 + x_j` acts as the structural translation.** -/
theorem xMonomialApply_single_add_self (τ : ι → ℂ) (j : ι)
    (y : meroField (Set.univ : Set ℂ)) :
    xMonomialApply τ (Finsupp.single j 1) y + y = addTranslationMeroEquiv (τ j) y := by
  rw [xMonomialApply_single, meroShiftDiff]
  abel

/-! ## The operator action is multiplicative -/

omit [Fintype ι] [DecidableEq ι] in
theorem xApply_eq_sum_of_subset (τ : ι → ℂ) (P : MvPolynomial ι ℂ)
    {s : Finset (ι →₀ ℕ)} (hs : P.support ⊆ s) (y : meroField (Set.univ : Set ℂ)) :
    xApply τ P y =
      ∑ d ∈ s, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
        xMonomialApply τ d y := by
  classical
  rw [xApply]
  refine (Finset.sum_subset (f := fun d =>
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
      xMonomialApply τ d y) hs ?_)
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul]

omit [Fintype ι] in
theorem xApply_add (τ : ι → ℂ) (P Q : MvPolynomial ι ℂ) (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (P + Q) y = xApply τ P y + xApply τ Q y := by
  classical
  have hP : P.support ⊆ P.support ∪ Q.support := Finset.subset_union_left
  have hQ : Q.support ⊆ P.support ∪ Q.support := Finset.subset_union_right
  have hPQ : (P + Q).support ⊆ P.support ∪ Q.support := MvPolynomial.support_add
  rw [xApply_eq_sum_of_subset τ _ hPQ, xApply_eq_sum_of_subset τ _ hP,
    xApply_eq_sum_of_subset τ _ hQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

omit [Fintype ι] in
theorem xApply_monomial (τ : ι → ℂ) (d : ι →₀ ℕ) (a : ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (MvPolynomial.monomial d a) y =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) a * xMonomialApply τ d y := by
  classical
  rw [xApply_eq_sum_of_subset τ _ (MvPolynomial.support_monomial_subset (s := d) (a := a))
    (s := {d})]
  rw [Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

omit [Fintype ι] in
theorem xApply_monomial_mul (τ : ι → ℂ) (d : ι →₀ ℕ) (a : ℂ) (Q : MvPolynomial ι ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (MvPolynomial.monomial d a * Q) y =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) a * xMonomialApply τ d (xApply τ Q y) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial e b =>
      rw [MvPolynomial.monomial_mul, xApply_monomial, xApply_monomial, xMonomialApply_add,
        xMonomialApply_complexMul, map_mul]
      rw [mul_assoc]
  | add Q R hQ hR =>
      rw [mul_add, xApply_add, hQ, hR, xApply_add, xMonomialApply_add_germ, mul_add]

omit [Fintype ι] in
/-- **Multiplicativity.**  Difference operators act by composition. -/
theorem xApply_mul (τ : ι → ℂ) (P Q : MvPolynomial ι ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (P * Q) y = xApply τ P (xApply τ Q y) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a => rw [xApply_monomial_mul, xApply_monomial]
  | add P R hP hR => rw [add_mul, xApply_add, hP, hR, xApply_add]

omit [Fintype ι] in
theorem xApply_one (τ : ι → ℂ) (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (1 : MvPolynomial ι ℂ) y = y := by
  have h1 : (1 : MvPolynomial ι ℂ) = MvPolynomial.monomial 0 1 := by
    simp [MvPolynomial.monomial_zero']
  rw [h1, xApply_monomial, xMonomialApply_zero, map_one, one_mul]

omit [Fintype ι] in
theorem xApply_X (τ : ι → ℂ) (j : ι) (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (MvPolynomial.X j) y = meroShiftDiff (τ j) y := by
  rw [MvPolynomial.X, xApply_monomial, xMonomialApply_single, map_one, one_mul]

omit [Fintype ι] in
/-- **The unit translation operator.**  `1 + x_j` acts as translation by `τ j`. -/
theorem xApply_one_add_X (τ : ι → ℂ) (j : ι) (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (1 + MvPolynomial.X j) y = addTranslationMeroEquiv (τ j) y := by
  rw [xApply_add, xApply_one, xApply_X, meroShiftDiff]
  abel

/-! ## Translation monomials -/

omit [DecidableEq ι] in
theorem natShift_add (τ : ι → ℂ) (m n : ι →₀ ℕ) :
    natShift τ (m + n) = natShift τ m + natShift τ n := by
  rw [natShift, natShift, natShift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finsupp.add_apply]
  push_cast
  ring

omit [DecidableEq ι] in
theorem natShift_single (τ : ι → ℂ) (j : ι) (b : ℕ) :
    natShift τ (Finsupp.single j b) = (b : ℂ) * τ j := by
  classical
  rw [natShift]
  have hterm : ∀ i : ι, ((Finsupp.single j b : ι →₀ ℕ) i : ℂ) * τ i =
      if i = j then (b : ℂ) * τ i else 0 := by
    intro i
    rw [Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Ne.symm hij, hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ j]
  simp

omit [Fintype ι] in
theorem xApply_one_add_X_pow (τ : ι → ℂ) (j : ι) (b : ℕ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ ((1 + MvPolynomial.X j) ^ b) y =
      addTranslationMeroEquiv ((b : ℂ) * τ j) y := by
  induction b generalizing y with
  | zero => simpa [addTranslationMeroEquiv_zero_apply] using xApply_one τ y
  | succ b ih =>
      rw [pow_succ, xApply_mul, xApply_one_add_X, ih, addTranslationMeroEquiv_add]
      congr 1
      push_cast
      ring

/-- The operator realizing the structural translation by an exponent vector. -/
def translationMonomial (n : ι →₀ ℕ) : MvPolynomial ι ℂ :=
  ∏ j ∈ n.support, (1 + MvPolynomial.X j) ^ (n j)

/-- **Translation monomials act as structural translations.** -/
theorem xApply_translationMonomial (τ : ι → ℂ) (n : ι →₀ ℕ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (translationMonomial n) y = addTranslationMeroEquiv (natShift τ n) y := by
  classical
  induction n using Finsupp.induction with
  | zero =>
      rw [translationMonomial]
      simp [xApply_one, natShift, addTranslationMeroEquiv_zero_apply]
  | single_add j b f hj hb ih =>
      have hsingle : (Finsupp.single j b).support = {j} := by simp [hb]
      have hsupp : (Finsupp.single j b + f).support = insert j f.support := by
        rw [Finsupp.support_add_eq (by rw [hsingle]; simpa using hj), hsingle]
        rfl
      have hexp : ∀ i ∈ f.support, (Finsupp.single j b + f) i = f i := by
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp [Ne.symm hij]
      have hj' : (Finsupp.single j b + f) j = b := by
        simp [Finsupp.notMem_support_iff.mp hj]
      rw [translationMonomial, hsupp, Finset.prod_insert hj, hj',
        Finset.prod_congr rfl (fun i hi => by rw [hexp i hi]), ← translationMonomial,
        xApply_mul, ih, xApply_one_add_X_pow, addTranslationMeroEquiv_add, natShift_add,
        natShift_single]

end

end GaloisForLFunctions
