import GaloisForLFunctions.HTGeometry.DifferentialSeparant

/-!
# Order bounds and the iterated separant decomposition

Differentiating raises the order by at most one, and the separant of every proper derivative of `A`
is again the separant of `A`: for each `k`,

`δ^{k+1} A = S_A · y_{n+k+1} + (order at most n+k)`.

This is what makes Ritt's reduction lower the order of an arbitrary differential polynomial against
a fixed one: pseudo-division by `δ^{k} A` in the top jet costs only powers of `S_A`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions

noncomputable section

/-- Differentiating a monomial does not introduce new variables. -/
theorem vars_pderiv_subset {σ R : Type*} [CommRing R] (i : σ) (p : MvPolynomial σ R) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  classical
  intro x hx
  have hrep : ∑ s ∈ p.support, MvPolynomial.monomial s (MvPolynomial.coeff s p) = p :=
    MvPolynomial.support_sum_monomial_coeff p
  have hsum : MvPolynomial.pderiv i p
      = ∑ s ∈ p.support,
          MvPolynomial.pderiv i (MvPolynomial.monomial s (MvPolynomial.coeff s p)) := by
    conv_lhs => rw [← hrep]
    exact map_sum _ _ _
  rw [hsum] at hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hx)
  rw [MvPolynomial.pderiv_monomial] at hxs
  have hxsupp : x ∈ (s - Finsupp.single i 1).support := by
    by_cases hc : MvPolynomial.coeff s p * (s i : R) = 0
    · rw [hc] at hxs
      simp at hxs
    · rw [MvPolynomial.vars_monomial hc] at hxs
      exact hxs
  have hxs' : x ∈ s.support := Finsupp.support_tsub hxsupp
  exact MvPolynomial.mem_vars_iff_mem_support _ |>.mpr ⟨s, hs, hxs'⟩

variable {K : Type*} [CommRing K] [Differential K]

omit [Differential K] in
theorem vars_le_scalarOrder (A : DifferentialPolynomial Unit K) :
    ∀ p ∈ A.vars, p.2 ≤ scalarDifferentialPolynomialOrder A :=
  fun _ hp => Finset.le_sup (f := fun j : Unit × ℕ => j.2) hp

omit [Differential K] in
theorem scalarOrder_le {A : DifferentialPolynomial Unit K} {n : ℕ}
    (h : ∀ p ∈ A.vars, p.2 ≤ n) : scalarDifferentialPolynomialOrder A ≤ n :=
  Finset.sup_le h

omit [Differential K] in
theorem scalarOrder_separant_le (A : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialOrder (scalarSeparant A)
      ≤ scalarDifferentialPolynomialOrder A :=
  scalarOrder_le fun p hp => vars_le_scalarOrder A p (vars_pderiv_subset _ A hp)

/-- Differentiating raises the order by at most one. -/
theorem scalarOrder_deriv_le (A : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialOrder (differentialPolynomialOverDerivation Unit K A)
      ≤ scalarDifferentialPolynomialOrder A + 1 := by
  classical
  obtain ⟨B, hB, hEq⟩ := exists_separant_decomposition A
  refine scalarOrder_le ?_
  intro p hp
  rw [hEq] at hp
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hp) with h | h
  · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
    · exact le_trans (le_trans (vars_le_scalarOrder _ p h') (scalarOrder_separant_le A))
        (Nat.le_succ _)
    · have := mvPolynomial_vars_X_subset (R := K) ((), scalarDifferentialPolynomialOrder A + 1) h'
      simp only [Finset.mem_singleton] at this
      subst this
      exact le_rfl
  · exact le_trans (hB p h) (Nat.le_succ _)

/-- **The iterated separant decomposition.**  Every proper derivative of `A` is linear in its top
jet with the same coefficient, the separant of `A`. -/
theorem exists_iterated_separant_decomposition (A : DifferentialPolynomial Unit K) (k : ℕ) :
    ∃ B : DifferentialPolynomial Unit K,
      (∀ p ∈ B.vars, p.2 ≤ scalarDifferentialPolynomialOrder A + k) ∧
      (⇑(differentialPolynomialOverDerivation Unit K))^[k + 1] A
        = scalarSeparant A
            * MvPolynomial.X ((), scalarDifferentialPolynomialOrder A + k + 1) + B := by
  classical
  induction k with
  | zero =>
      obtain ⟨B, hB, hEq⟩ := exists_separant_decomposition A
      exact ⟨B, by simpa using hB, by simpa using hEq⟩
  | succ k ih =>
      obtain ⟨B, hB, hEq⟩ := ih
      set n := scalarDifferentialPolynomialOrder A with hn
      refine ⟨differentialPolynomialOverDerivation Unit K B
          + MvPolynomial.X ((), n + k + 1)
            * differentialPolynomialOverDerivation Unit K (scalarSeparant A), ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hp) with h | h
        · have hBord : scalarDifferentialPolynomialOrder B ≤ n + k := scalarOrder_le hB
          have := vars_le_scalarOrder _ p h
          have hle := scalarOrder_deriv_le B
          omega
        · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h) with h' | h'
          · have := mvPolynomial_vars_X_subset (R := K) ((), n + k + 1) h'
            simp only [Finset.mem_singleton] at this
            subst this
            omega
          · have hSord : scalarDifferentialPolynomialOrder (scalarSeparant A) ≤ n :=
              scalarOrder_separant_le A
            have := vars_le_scalarOrder _ p h'
            have hle := scalarOrder_deriv_le (scalarSeparant A)
            omega
      · have hiter : (⇑(differentialPolynomialOverDerivation Unit K))^[k + 1 + 1] A
            = differentialPolynomialOverDerivation Unit K
                ((⇑(differentialPolynomialOverDerivation Unit K))^[k + 1] A) := by
          rw [Function.iterate_succ_apply']
        rw [hiter, hEq, map_add, Derivation.leibniz]
        simp only [smul_eq_mul, differentialPolynomialOverDerivation_X]
        have harith : n + k + 1 + 1 = n + (k + 1) + 1 := by omega
        rw [harith]
        ring

end

end GaloisForLFunctions.HTGeometry
