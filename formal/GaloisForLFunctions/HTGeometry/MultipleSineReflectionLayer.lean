import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# Reflection removes exactly one face layer

The annihilator of the multiple sine is the squarefree Veronese ideal of width `N - 1`, that of the
Barnes multiple gamma the principal ideal of the full product, which is the squarefree Veronese
ideal of width `N`.  Comparing the two Stanley–Reisner face complexes: a squarefree monomial lies in
`I_r` exactly when its support has at least `r` elements, so the face complex of `I_{N-1}` is the
face complex of `I_N` with its maximal proper layer removed — reflection deletes exactly one layer.
-/

open scoped BigOperators
open MvPolynomial

namespace GaloisForLFunctions.VeroneseIdeal

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

/-- **A squarefree monomial lies in `I_r` exactly when it is wide enough.** -/
theorem prod_X_mem_veroneseIdeal_iff [Nontrivial R] (J : Finset σ) (r : ℕ) :
    (∏ j ∈ J, (X j : MvPolynomial σ R)) ∈ veroneseIdeal R σ r ↔ r ≤ J.card := by
  classical
  rw [prod_X_eq_monomial, mem_veroneseIdeal_iff]
  constructor
  · intro hw
    have hcoeff : MvPolynomial.coeff (∑ j ∈ J, Finsupp.single j 1)
        (monomial (∑ j ∈ J, Finsupp.single j (1 : ℕ)) (1 : R)) ≠ 0 := by
      rw [MvPolynomial.coeff_monomial, if_pos rfl]
      exact one_ne_zero
    have := hw _ hcoeff
    rwa [support_sum_single] at this
  · intro hcard d hd
    have hdeq : d = ∑ j ∈ J, Finsupp.single j (1 : ℕ) := by
      by_contra hne
      rw [MvPolynomial.coeff_monomial, if_neg (fun h => hne h.symm)] at hd
      exact hd rfl
    rw [hdeq, support_sum_single]
    exact hcard

/-- The face complex of the squarefree Veronese ideal: the index sets whose squarefree monomial is
not in the ideal. -/
def veroneseFaceComplex (R σ : Type*) [CommRing R] [DecidableEq σ] (r : ℕ) : Set (Finset σ) :=
  {J | (∏ j ∈ J, (X j : MvPolynomial σ R)) ∉ veroneseIdeal R σ r}

theorem mem_veroneseFaceComplex_iff [Nontrivial R] (r : ℕ) (J : Finset σ) :
    J ∈ veroneseFaceComplex R σ r ↔ J.card < r := by
  rw [veroneseFaceComplex, Set.mem_setOf_eq, prod_X_mem_veroneseIdeal_iff]
  omega

/-- **Reflection removes exactly one face layer.**  The face complex of the multiple-sine
annihilator `I_{N-1}` is the face complex of the multiple-gamma annihilator `I_N` with its maximal
layer deleted. -/
theorem veroneseFaceComplex_sub_one [Nontrivial R] {N : ℕ} (hN : 1 ≤ N) :
    veroneseFaceComplex R σ (N - 1)
      = veroneseFaceComplex R σ N \ {J : Finset σ | J.card = N - 1} := by
  ext J
  rw [Set.mem_sdiff, mem_veroneseFaceComplex_iff, mem_veroneseFaceComplex_iff,
    Set.mem_setOf_eq]
  omega

/-- The full squarefree product generates the width-`N` Veronese ideal when there are exactly `N`
variables. -/
theorem veroneseIdeal_le_sub_one [Nontrivial R] {N : ℕ} (hN : 1 ≤ N) :
    veroneseIdeal R σ N ≤ veroneseIdeal R σ (N - 1) := by
  intro P hP
  rw [mem_veroneseIdeal_iff] at hP ⊢
  intro d hd
  have := hP d hd
  omega

/-- **The inclusion is strict.**  With `N` variables the maximal proper layer separates the two
annihilators: a squarefree monomial on `N - 1` variables lies in `I_{N-1}` but not in `I_N`. -/
theorem veroneseIdeal_lt_sub_one [Nontrivial R] [Fintype σ] {N : ℕ} (hN : 1 ≤ N)
    (hcard : Fintype.card σ = N) :
    veroneseIdeal R σ N < veroneseIdeal R σ (N - 1) := by
  classical
  refine lt_of_le_of_ne (veroneseIdeal_le_sub_one hN) ?_
  intro heq
  obtain ⟨J, -, hJcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset σ)) (n := N - 1)
      (by rw [Finset.card_univ, hcard]; omega)
  have hmem : (∏ j ∈ J, (X j : MvPolynomial σ R)) ∈ veroneseIdeal R σ (N - 1) :=
    (prod_X_mem_veroneseIdeal_iff J (N - 1)).mpr (by omega)
  rw [← heq] at hmem
  have := (prod_X_mem_veroneseIdeal_iff J N).mp hmem
  omega

end GaloisForLFunctions.VeroneseIdeal
