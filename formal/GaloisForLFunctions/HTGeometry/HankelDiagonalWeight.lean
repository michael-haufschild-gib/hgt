import GaloisForLFunctions.HTGeometry.HankelStandardMonomials
import GaloisForLFunctions.HTGeometry.InitialIdealDegeneration

/-!
# The concave weight that degenerates the Hankel minors to their diagonals

```text
hankelWeight                              the weight `k ↦ -k²`
sum_mul_perm_lt                           ** the strict rearrangement inequality **
weight_diagonal_lt                        ** the diagonal is the unique term of least weight **
lowestForm_finiteHankelMaximalMinorOver   ** so the lowest form of a minor is its diagonal
                                             monomial **
finiteHankelChainIdeal_le_initialIdeal    ** and the chain ideal sits inside the initial ideal **
```

Every Leibniz term of a maximal Hankel minor uses the entries `x_{σ(j)+c_j}`, so all terms have the
same index sum and the concave weight `-k²` turns their weights into `const - 2·∑ c_j·σ(j)`.  The
rearrangement inequality makes that sum strictly largest at the identity, so the diagonal is the
unique term of least weight and the lowest form is its monomial.

The containment then follows from the corpus's combinatorial fact that every non-chain-reduced
exponent dominates the diagonal of some minor: such a monomial is a monomial multiple of that
diagonal, hence of a lowest form.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial RHTower

universe u

/-- The concave weight `k ↦ -k²` on the Hankel variables. -/
def hankelWeight (N : ℕ) : Fin N → ℤ := fun k => -((k : ℕ) : ℤ) ^ (2 : ℕ)

theorem hankelWeight_nonpos (N : ℕ) (k : Fin N) : hankelWeight N k ≤ 0 := by
  simp only [hankelWeight, neg_nonpos]
  positivity

theorem weight_hankelPermutationExponent {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (σ : Equiv.Perm (Fin n)) :
    Finsupp.weight (hankelWeight N) (hankelPermutationExponent c hbound σ)
      = ∑ j : Fin n, -(((σ j : ℕ) : ℤ) + (c j : ℤ)) ^ (2 : ℕ) := by
  rw [hankelPermutationExponent, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.weight_single]
  simp [hankelWeight, finiteHankelIndex]

/-- **The strict rearrangement inequality.**  A nonidentity permutation pairs a strictly increasing
sequence with the strictly increasing indices to a strictly smaller sum. -/
theorem sum_mul_perm_lt {n : ℕ} {c : Fin n → ℕ} (hc : StrictMono c) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ≠ 1) :
    ∑ j, (c j : ℤ) * ((σ j : ℕ) : ℤ) < ∑ j, (c j : ℤ) * ((j : ℕ) : ℤ) := by
  set f : Fin n → ℤ := fun j => (c j : ℤ) with hf
  set g : Fin n → ℤ := fun j => ((j : ℕ) : ℤ) with hg
  have hmono : MonovaryOn f g (Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    simp only [hg] at hij
    have hlt : i < j := by exact_mod_cast hij
    simp only [hf]
    exact_mod_cast (hc hlt).le
  have hsub : {x | σ x ≠ x} ⊆ (Finset.univ : Finset (Fin n)) := by intro x _; simp
  have hkey := (hmono.sum_smul_comp_perm_lt_sum_smul_iff hsub).mpr ?_
  · simpa [f, g, smul_eq_mul] using hkey
  · intro hcon
    apply hσ
    have hstrict : StrictMono (fun i => σ i) := by
      intro i j hij
      rcases lt_trichotomy (σ i) (σ j) with h | h | h
      · exact h
      · exact absurd (σ.injective h) (by exact ne_of_lt hij)
      · have hle := hcon (Finset.mem_univ j) (Finset.mem_univ i) (by
          simp only [Function.comp_apply, hg]
          exact_mod_cast h)
        simp only [hf] at hle
        have hji : j ≤ i := by
          by_contra hji
          push Not at hji
          exact absurd (hc hji) (by omega)
        omega
    have hall : ∀ i, σ i = i := by
      intro i
      set e := StrictMono.orderIsoOfSurjective (fun i => σ i) hstrict σ.surjective with he
      have heq : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
      have hi := congrArg (fun (u : Fin n ≃o Fin n) => u i) heq
      simpa [he] using hi
    exact Equiv.ext hall

/-- **The diagonal has strictly the smallest weight.**  For the concave weight the diagonal term of a
maximal Hankel minor is the unique term of least weight. -/
theorem weight_diagonal_lt {N n : ℕ} {c : Fin n → ℕ} (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    Finsupp.weight (hankelWeight N) (hankelDiagonalExponent c hbound)
      < Finsupp.weight (hankelWeight N) (hankelPermutationExponent c hbound σ) := by
  rw [hankelDiagonalExponent, weight_hankelPermutationExponent, weight_hankelPermutationExponent]
  have hsq : ∑ j : Fin n, (((σ j : ℕ) : ℤ)) ^ (2 : ℕ) = ∑ j : Fin n, (((j : ℕ) : ℤ)) ^ (2 : ℕ) :=
    Equiv.sum_comp σ (fun i : Fin n => (((i : ℕ) : ℤ)) ^ (2 : ℕ))
  have hexp : ∀ τ : Equiv.Perm (Fin n),
      ∑ j : Fin n, -(((τ j : ℕ) : ℤ) + (c j : ℤ)) ^ (2 : ℕ)
        = -(∑ j : Fin n, (((τ j : ℕ) : ℤ)) ^ (2 : ℕ)) - 2 * (∑ j, (c j : ℤ) * ((τ j : ℕ) : ℤ))
          - ∑ j : Fin n, ((c j : ℤ)) ^ (2 : ℕ) := by
    intro τ
    have hpt : ∀ j : Fin n, -(((τ j : ℕ) : ℤ) + (c j : ℤ)) ^ (2 : ℕ)
        = (-(((τ j : ℕ) : ℤ)) ^ (2 : ℕ)) - 2 * ((c j : ℤ) * ((τ j : ℕ) : ℤ)) - ((c j : ℤ)) ^ (2 : ℕ) := by
      intro j; ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hpt j), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hexp σ, hexp 1, hsq]
  have := sum_mul_perm_lt hc hσ
  simp only [Equiv.Perm.coe_one, id_eq]
  omega



/-- Every monomial of a maximal Hankel minor is the exponent of a Leibniz term. -/
theorem exists_perm_of_mem_support_minorOver {R : Type*} [CommRing R] {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) {e : Fin N →₀ ℕ}
    (he : e ∈ (finiteHankelMaximalMinorOver R c hbound).support) :
    ∃ σ : Equiv.Perm (Fin n), e = hankelPermutationExponent c hbound σ := by
  classical
  rw [← map_finiteHankelMaximalMinor (Int.castRingHom R)] at he
  have heZ := MvPolynomial.support_map_subset (Int.castRingHom R)
    (finiteHankelMaximalMinor c hbound) he
  rw [finiteHankelMaximalMinor_eq_sum_monomial] at heZ
  have hmem := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun σ : Equiv.Perm (Fin n) =>
      MvPolynomial.monomial (hankelPermutationExponent c hbound σ)
        (Equiv.Perm.sign σ : ℤ)) heZ
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨σ, -, heσ⟩ := hmem
  exact ⟨σ, Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset heσ)⟩

theorem finiteHankelMaximalMinorOver_ne_zero (K : Type u) [Field K] {N n : ℕ} {c : Fin n → ℕ}
    (hbound : ∀ j, n + c j ≤ N) (hc : StrictMono c) :
    finiteHankelMaximalMinorOver K c hbound ≠ 0 := by
  intro h
  have := finiteHankelMaximalMinorOver_coeff_diagonal (R := K) c hbound hc
  rw [h] at this
  simp at this

/-- **The least weight of a maximal Hankel minor is the weight of its diagonal.** -/
theorem minWeight_finiteHankelMaximalMinorOver (K : Type u) [Field K] {N n : ℕ} {c : Fin n → ℕ}
    (hbound : ∀ j, n + c j ≤ N) (hc : StrictMono c) :
    minWeight (hankelWeight N) (finiteHankelMaximalMinorOver K c hbound)
      = Finsupp.weight (hankelWeight N) (hankelDiagonalExponent c hbound) := by
  classical
  refine le_antisymm (minWeight_le ?_) (le_minWeight (finiteHankelMaximalMinorOver_ne_zero K hbound hc) ?_)
  · rw [MvPolynomial.mem_support_iff, finiteHankelMaximalMinorOver_coeff_diagonal c hbound hc]
    exact one_ne_zero
  · intro e he
    obtain ⟨σ, rfl⟩ := exists_perm_of_mem_support_minorOver c hbound he
    by_cases hσ : σ = 1
    · rw [hσ, ← hankelDiagonalExponent]
    · exact (weight_diagonal_lt hbound hc hσ).le

/-- **The lowest form of a maximal Hankel minor is its diagonal monomial.** -/
theorem lowestForm_finiteHankelMaximalMinorOver (K : Type u) [Field K] {N n : ℕ} {c : Fin n → ℕ}
    (hbound : ∀ j, n + c j ≤ N) (hc : StrictMono c) :
    lowestForm (hankelWeight N) (finiteHankelMaximalMinorOver K c hbound)
      = MvPolynomial.monomial (hankelDiagonalExponent c hbound) (1 : K) := by
  classical
  have hmin := minWeight_finiteHankelMaximalMinorOver K hbound hc
  ext e
  by_cases he : e = hankelDiagonalExponent c hbound
  · subst he
    rw [coeff_lowestForm_of_weight_eq (by rw [hmin]),
      finiteHankelMaximalMinorOver_coeff_diagonal c hbound hc, MvPolynomial.coeff_monomial,
      if_pos rfl]
  · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm he)]
    by_cases hw : Finsupp.weight (hankelWeight N) e
        = minWeight (hankelWeight N) (finiteHankelMaximalMinorOver K c hbound)
    · rw [coeff_lowestForm_of_weight_eq hw]
      by_contra hcon
      obtain ⟨σ, rfl⟩ := exists_perm_of_mem_support_minorOver c hbound
        (MvPolynomial.mem_support_iff.mpr hcon)
      have hσ : σ ≠ 1 := by
        intro h
        exact he (by rw [h, ← hankelDiagonalExponent])
      have hlt := weight_diagonal_lt hbound hc hσ
      rw [hw, hmin] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact coeff_lowestForm_of_weight_ne hw

/-- **The chain ideal is contained in the initial ideal of the concave degeneration.**  Each
non-chain-reduced monomial is a multiple of the diagonal of some maximal minor, and that diagonal is
the minor's lowest form. -/
theorem finiteHankelChainIdeal_le_initialIdeal (K : Type u) [Field K] (N r : ℕ) :
    finiteHankelChainIdeal K N r
      ≤ initialIdeal (hankelWeight N) (finiteHankelSecantIdeal K N r) := by
  classical
  rw [finiteHankelChainIdeal, Ideal.span_le]
  rintro p ⟨e, he, rfl⟩
  obtain ⟨c, hbound, hc, hle⟩ := exists_finiteHankelMinor_diagonal_le_of_not_chainReduced he
  have hmem : finiteHankelMaximalMinorOver K c hbound ∈ finiteHankelSecantIdeal K N r :=
    Ideal.subset_span ⟨c, hbound, hc, rfl⟩
  have hdiag : MvPolynomial.monomial (hankelDiagonalExponent c hbound) (1 : K)
      ∈ initialIdeal (hankelWeight N) (finiteHankelSecantIdeal K N r) := by
    rw [← lowestForm_finiteHankelMaximalMinorOver K hbound hc]
    exact Submodule.subset_span
      (lowestForm_mem_initialFormSet hmem (finiteHankelMaximalMinorOver_ne_zero K hbound hc))
  have hsplit : (MvPolynomial.monomial e (1 : K))
      = MvPolynomial.monomial (e - hankelDiagonalExponent c hbound) (1 : K)
        * MvPolynomial.monomial (hankelDiagonalExponent c hbound) (1 : K) := by
    rw [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hle]
  show MvPolynomial.monomial e (1 : K)
    ∈ initialIdeal (hankelWeight N) (finiteHankelSecantIdeal K N r)
  rw [hsplit]
  exact Ideal.mul_mem_left _ _ hdiag

end GaloisForLFunctions.HTGeometry
