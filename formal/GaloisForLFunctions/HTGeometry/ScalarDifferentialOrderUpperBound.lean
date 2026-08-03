import GaloisForLFunctions.HTGeometry.ScalarDifferentialOrderLowerBound

/-!
# A bounded state field forces a low-order algebraic differential equation

The companion of the jet-independence lower bound.  If the jets `x, x', ..., x^(n)` all live inside
an intermediate field of transcendence degree at most `n`, then `n+1` elements sit in a field of
transcendence degree `n`, so they are algebraically dependent: a nonzero scalar differential
polynomial of order at most `n` annihilates `x`.

Together with the lower bound this pins the minimal order exactly.  If the first `m+1` jets are
algebraically independent and every jet lies in a field of transcendence degree at most `m+1`, then
the least order of a nonzero algebraic differential equation for `x` is exactly `m+1` — one state,
one differential order.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A family strictly larger than the transcendence degree is algebraically dependent. -/
theorem not_algebraicIndependent_of_trdeg_le
    {K M : Type*} [Field K] [Field M] [Algebra K M] {n : ℕ}
    (h : Algebra.trdeg K M ≤ (n : Cardinal)) (y : Fin (n + 1) → M) :
    ¬ AlgebraicIndependent K y := by
  intro hy
  have hle := AlgebraicIndependent.lift_cardinalMk_le_trdeg hy
  rw [Cardinal.mk_fin, Cardinal.lift_natCast] at hle
  have h2 : Cardinal.lift.{0} (Algebra.trdeg K M) ≤ Cardinal.lift.{0} ((n : ℕ) : Cardinal) :=
    Cardinal.lift_le.mpr h
  rw [Cardinal.lift_natCast] at h2
  have hcast : ((n + 1 : ℕ) : Cardinal) ≤ ((n : ℕ) : Cardinal) := le_trans hle h2
  rw [Nat.cast_le] at hcast
  omega

/-- The renamed jet polynomial has order at most `n`. -/
theorem scalarDifferentialPolynomialOrder_rename_le
    {K : Type*} [CommSemiring K] {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) K) :
    scalarDifferentialPolynomialOrder
        (MvPolynomial.rename (fun i : Fin (n + 1) => ((), (i : ℕ))) Q) ≤ n := by
  classical
  refine Finset.sup_le fun p hp => ?_
  have hsub := MvPolynomial.vars_rename (fun i : Fin (n + 1) => ((), (i : ℕ))) Q
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hsub hp)
  exact Nat.lt_succ_iff.mp i.isLt

/-- **The order upper bound.**  If the first `n+1` jets of `x` lie in an intermediate field of
transcendence degree at most `n`, then a nonzero scalar differential polynomial of order at most `n`
annihilates `x`. -/
theorem exists_scalarDifferentialRelation_of_trdeg_le
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (M : IntermediateField K L) {x : L} {n : ℕ}
    (htr : Algebra.trdeg K M ≤ (n : Cardinal))
    (hjets : ∀ i : Fin (n + 1), differentialJet (i : ℕ) x ∈ M) :
    ∃ P : DifferentialPolynomial Unit K, P ≠ 0 ∧
      scalarDifferentialPolynomialOrder P ≤ n ∧
      differentialPolynomialEvalOver (K := K) (fun _ : Unit => x) P = 0 := by
  classical
  set y : Fin (n + 1) → M := fun i => ⟨differentialJet (i : ℕ) x, hjets i⟩ with hy
  have hdep : ¬ AlgebraicIndependent K y := not_algebraicIndependent_of_trdeg_le htr y
  rw [algebraicIndependent_iff_injective_aeval] at hdep
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q : MvPolynomial (Fin (n + 1)) K, Q ≠ 0 ∧
      MvPolynomial.aeval y Q = 0 := by
    obtain ⟨Q₁, Q₂, hEq, hne⟩ := Function.not_injective_iff.mp hdep
    exact ⟨Q₁ - Q₂, sub_ne_zero.mpr hne, by rw [map_sub, hEq, sub_self]⟩
  refine ⟨MvPolynomial.rename (fun i : Fin (n + 1) => ((), (i : ℕ))) Q, ?_,
    scalarDifferentialPolynomialOrder_rename_le Q, ?_⟩
  · intro hzero
    exact hQ0 (MvPolynomial.rename_injective _
      (fun i j hij => Fin.ext (congrArg Prod.snd hij)) (by rw [hzero, map_zero]))
  · have hpush : MvPolynomial.aeval (fun i : Fin (n + 1) => differentialJet (i : ℕ) x) Q = 0 := by
      have h := MvPolynomial.comp_aeval_apply y M.val Q
      rw [hQ, map_zero] at h
      exact h.symm
    rw [differentialPolynomialEvalOver, MvPolynomial.aeval_rename]
    exact hpush

/-- **Exact minimal order.**  Algebraic independence of the first `m+1` jets and a state field of
transcendence degree at most `m+1` pin the least order of a nonzero algebraic differential equation
for `x` to exactly `m+1`. -/
theorem isLeast_scalarDifferentialOrder
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
    (M : IntermediateField K L) {x : L} {m : ℕ}
    (hind : AlgebraicIndependent K (fun i : Fin (m + 1) => differentialJet (i : ℕ) x))
    (htr : Algebra.trdeg K M ≤ ((m + 1 : ℕ) : Cardinal))
    (hjets : ∀ i : Fin (m + 2), differentialJet (i : ℕ) x ∈ M) :
    IsLeast {k : ℕ | ∃ P : DifferentialPolynomial Unit K, P ≠ 0 ∧
        scalarDifferentialPolynomialOrder P = k ∧
        differentialPolynomialEvalOver (K := K) (fun _ : Unit => x) P = 0} (m + 1) := by
  have hlow : ∀ (P : DifferentialPolynomial Unit K), P ≠ 0 →
      scalarDifferentialPolynomialOrder P ≤ m →
      differentialPolynomialEvalOver (K := K) (fun _ : Unit => x) P ≠ 0 :=
    fun P hP hord =>
      differentialPolynomialEvalOver_ne_zero_of_algebraicIndependent_jets hind hP hord
  obtain ⟨P, hP0, hPord, hPeval⟩ :=
    exists_scalarDifferentialRelation_of_trdeg_le M (n := m + 1) htr hjets
  have hPeq : scalarDifferentialPolynomialOrder P = m + 1 := by
    rcases Nat.lt_or_ge (scalarDifferentialPolynomialOrder P) (m + 1) with hlt | hge
    · exact absurd hPeval (hlow P hP0 (Nat.lt_succ_iff.mp hlt))
    · omega
  refine ⟨⟨P, hP0, hPeq, hPeval⟩, ?_⟩
  rintro k ⟨R, hR0, hRord, hReval⟩
  by_contra hk
  exact hlow R hR0 (by omega) hReval

end

end GaloisForLFunctions
