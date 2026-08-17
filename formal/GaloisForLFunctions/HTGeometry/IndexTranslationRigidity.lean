import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport

/-!
# Rigidity of variable support under an index translation

A rational function field whose variables are indexed by an abelian group carries the translation
action `X λ ↦ X (λ + μ)`.  A rational function uses only finitely many variables, and the
translation moves that finite set by `μ`; when `μ` has infinite order no nonempty finite set is
invariant, so the only invariant rational functions are the constants.

The support of a rational function is intrinsic because divisibility in a multivariable polynomial
domain cannot remove a variable: a numerator and denominator with no common nonunit factor are each
carried to an associate of themselves, hence to a polynomial with exactly the same variables.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {Λ : Type*} [AddCommGroup Λ] {K : Type*} [Field K]

/-! ### Infinite-order translations move every nonempty finite set -/

theorem nsmul_injective_of_infiniteOrder {μ : Λ} (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) :
    Function.Injective (fun n : ℕ => n • μ) := by
  have key : ∀ n m : ℕ, n ≤ m → n • μ = m • μ → n = m := by
    intro n m hnm h
    by_contra hne
    have hlt : n < m := lt_of_le_of_ne hnm hne
    have hmn : m - n + n = m := by omega
    have hsplit : (m - n) • μ + n • μ = n • μ := by
      rw [← add_nsmul, hmn, ← h]
    have hz : (m - n) • μ + n • μ = 0 + n • μ := by rw [zero_add, hsplit]
    exact hμ (m - n) (by omega) (add_right_cancel hz)
  intro n m h
  simp only at h
  rcases le_total n m with hle | hle
  · exact key n m hle h
  · exact (key m n hle h.symm).symm

/-- **A finite set invariant under an infinite-order translation is empty.** -/
theorem eq_empty_of_image_add_eq [DecidableEq Λ] {μ : Λ} (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0)
    {V : Finset Λ} (hV : V.image (· + μ) = V) : V = ∅ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hne
  have hmem : ∀ n : ℕ, v + n • μ ∈ V := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
        have hstep : v + (n + 1) • μ = (v + n • μ) + μ := by
          rw [succ_nsmul]
          abel
        rw [hstep, ← hV]
        exact Finset.mem_image.mpr ⟨v + n • μ, ih, rfl⟩
  have hinj : Function.Injective fun n : ℕ => v + n • μ := by
    intro n m h
    simp only at h
    exact nsmul_injective_of_infiniteOrder hμ (add_left_cancel h)
  exact (V.finite_toSet).not_infinite (Set.infinite_of_injective_forall_mem hinj hmem)

/-! ### The index translation -/

/-- The automorphism of the polynomial ring induced by translating the index group. -/
noncomputable def indexTranslation (μ : Λ) : MvPolynomial Λ K ≃ₐ[K] MvPolynomial Λ K :=
  MvPolynomial.renameEquiv K (Equiv.addRight μ)

omit [AddCommGroup Λ] in
theorem vars_renameEquiv [DecidableEq Λ] {Λ' : Type*} [DecidableEq Λ'] (e : Λ ≃ Λ')
    (P : MvPolynomial Λ K) :
    (MvPolynomial.renameEquiv K e P).vars = P.vars.image e := by
  refine le_antisymm (MvPolynomial.vars_rename e P) ?_
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hback : P = MvPolynomial.rename e.symm (MvPolynomial.renameEquiv K e P) := by
    simp
  have hsub : P.vars ⊆ ((MvPolynomial.renameEquiv K e P).vars).image e.symm := by
    conv_lhs => rw [hback]
    exact MvPolynomial.vars_rename e.symm _
  obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp (hsub hj)
  have hkj : k = e j := by
    rw [← hke]
    simp
  rwa [hkj] at hk

theorem vars_indexTranslation [DecidableEq Λ] (μ : Λ) (P : MvPolynomial Λ K) :
    (indexTranslation (K := K) μ P).vars = P.vars.image (· + μ) :=
  vars_renameEquiv (Equiv.addRight μ) P

theorem isRelPrime_indexTranslation {μ : Λ} {P Q : MvPolynomial Λ K} (h : IsRelPrime P Q) :
    IsRelPrime (indexTranslation (K := K) μ P) (indexTranslation (K := K) μ Q) := by
  intro D hDP hDQ
  have hsymm : ∀ {A : MvPolynomial Λ K}, D ∣ indexTranslation (K := K) μ A →
      (indexTranslation (K := K) μ).symm D ∣ A := by
    intro A hA
    obtain ⟨T, hT⟩ := hA
    refine ⟨(indexTranslation (K := K) μ).symm T, ?_⟩
    have := congrArg (indexTranslation (K := K) μ).symm hT
    simpa using this
  have hunit := h (hsymm (A := P) hDP) (hsymm (A := Q) hDQ)
  have hmap := hunit.map (indexTranslation (K := K) μ).toAlgHom.toRingHom
  rwa [show ((indexTranslation (K := K) μ).toAlgHom.toRingHom
    ((indexTranslation (K := K) μ).symm D)) = D from by simp] at hmap

/-! ### Rigidity -/

/-- **A polynomial fixed up to divisibility by an infinite-order index translation is constant.** -/
theorem vars_eq_empty_of_dvd_indexTranslation [DecidableEq Λ] {μ : Λ}
    (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) {P : MvPolynomial Λ K} (hP : P ≠ 0)
    (h₁ : P ∣ indexTranslation (K := K) μ P) (h₂ : indexTranslation (K := K) μ P ∣ P) :
    P.vars = ∅ := by
  have hP' : indexTranslation (K := K) μ P ≠ 0 := by
    intro hzero
    exact hP (by simpa using congrArg (indexTranslation (K := K) μ).symm hzero)
  have hsub₁ : P.vars ⊆ (indexTranslation (K := K) μ P).vars :=
    mvPolynomial_vars_subset_of_dvd h₁ hP'
  have hsub₂ : (indexTranslation (K := K) μ P).vars ⊆ P.vars :=
    mvPolynomial_vars_subset_of_dvd h₂ hP
  have heq : (indexTranslation (K := K) μ P).vars = P.vars := le_antisymm hsub₂ hsub₁
  rw [vars_indexTranslation] at heq
  exact eq_empty_of_image_add_eq hμ heq

/-- **The index-translation fixed field is the constants.**  A ratio of two polynomials with no
common nonunit factor, invariant under the index translation by an element of infinite order, has
constant numerator and denominator. -/
theorem vars_eq_empty_of_indexTranslation_invariant [DecidableEq Λ] {μ : Λ}
    (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) {P Q : MvPolynomial Λ K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q)
    (h : indexTranslation (K := K) μ P * Q = P * indexTranslation (K := K) μ Q) :
    P.vars = ∅ ∧ Q.vars = ∅ := by
  have hrel' := isRelPrime_indexTranslation (μ := μ) hrel
  have hPdvd : P ∣ indexTranslation (K := K) μ P := by
    refine hrel.dvd_of_dvd_mul_right ?_
    exact ⟨indexTranslation (K := K) μ Q, h⟩
  have hσPdvd : indexTranslation (K := K) μ P ∣ P := by
    refine hrel'.dvd_of_dvd_mul_right ?_
    exact ⟨Q, h.symm⟩
  have hQdvd : Q ∣ indexTranslation (K := K) μ Q := by
    refine hrel.symm.dvd_of_dvd_mul_right ?_
    exact ⟨indexTranslation (K := K) μ P, by linear_combination -h⟩
  have hσQdvd : indexTranslation (K := K) μ Q ∣ Q := by
    refine hrel'.symm.dvd_of_dvd_mul_right ?_
    exact ⟨P, by linear_combination h⟩
  exact ⟨vars_eq_empty_of_dvd_indexTranslation hμ hP hPdvd hσPdvd,
    vars_eq_empty_of_dvd_indexTranslation hμ hQ hQdvd hσQdvd⟩

/-- The constant form of the rigidity statement. -/
theorem eq_C_of_indexTranslation_invariant [DecidableEq Λ] {μ : Λ}
    (hμ : ∀ n : ℕ, 0 < n → n • μ ≠ 0) {P Q : MvPolynomial Λ K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : IsRelPrime P Q)
    (h : indexTranslation (K := K) μ P * Q = P * indexTranslation (K := K) μ Q) :
    P = MvPolynomial.C (P.coeff 0) ∧ Q = MvPolynomial.C (Q.coeff 0) := by
  obtain ⟨hPv, hQv⟩ := vars_eq_empty_of_indexTranslation_invariant hμ hP hQ hrel h
  exact ⟨MvPolynomial.vars_eq_empty_iff_eq_C.mp hPv,
    MvPolynomial.vars_eq_empty_iff_eq_C.mp hQv⟩

end GaloisForLFunctions.HTGeometry
