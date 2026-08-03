import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# Expanding a family jet relation

Evaluating a differential relation of a finite family at a point separates into a power of the
spectral variable and a monomial in the jet variables: the jet index of a family is a sum type, and a
product over a sum type splits.

This is the shape in which a relation meets an expanded evaluation matrix, whose columns are exactly
pairs (jet monomial, power of the spectral variable).
-/

open BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The jet variables of a family, without the spectral variable. -/
abbrev FamilyJetVariables (m n : ℕ) : Type := Fin m × Fin (n + 1)

/-- **Evaluating a family jet relation splits the spectral variable from the jet monomial.** -/
theorem eval_familySplit_eq_sum {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ) (z : ℂ)
    (y : FamilyJetVariables m n → ℂ) :
    MvPolynomial.eval (Sum.elim (fun _ => z) y) P
      = ∑ s ∈ P.support, P.coeff s * (z ^ s (Sum.inl ()) * ∏ k, y k ^ s (Sum.inr k)) := by
  classical
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [Fintype.prod_sum_type]
  congr 1
  simp

/-- The evaluation of a relation at a jet vector of a family, in split form. -/
theorem eval_familyJetVec_eq_sum {m n : ℕ} (P : MvPolynomial (FamilyJetIndex m n) ℂ)
    (g : Fin m → ℂ → ℂ) (z : ℂ) :
    MvPolynomial.eval (familyJetVec (n := n) g z) P
      = ∑ s ∈ P.support, P.coeff s *
          (z ^ s (Sum.inl ()) *
            ∏ k : FamilyJetVariables m n, iteratedDeriv (k.2 : ℕ) (g k.1) z ^ s (Sum.inr k)) := by
  have hvec : familyJetVec (n := n) g z
      = Sum.elim (fun _ => z) fun k : FamilyJetVariables m n =>
        iteratedDeriv (k.2 : ℕ) (g k.1) z := by
    funext s
    cases s with
    | inl a => cases a; rfl
    | inr k => rfl
  rw [hvec, eval_familySplit_eq_sum]

/-! ## Splitting and reassembling a monomial -/

/-- The jet part of a family jet monomial. -/
def jetPart {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) : FamilyJetVariables m n →₀ ℕ :=
  s.comapDomain Sum.inr Sum.inr_injective.injOn

@[simp]
theorem jetPart_apply {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) (k : FamilyJetVariables m n) :
    jetPart s k = s (Sum.inr k) := rfl

/-- Reassembling a family jet monomial from its spectral degree and its jet part. -/
def combineMonomial {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ) :
    FamilyJetIndex m n →₀ ℕ :=
  Finsupp.single (Sum.inl ()) d + a.embDomain ⟨Sum.inr, Sum.inr_injective⟩

@[simp]
theorem combineMonomial_inl {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ) :
    combineMonomial d a (Sum.inl ()) = d := by
  rw [combineMonomial, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.embDomain_notin_range]
  · rw [add_zero]
  · rintro ⟨k, hk⟩
    exact Sum.noConfusion hk

@[simp]
theorem combineMonomial_inr {m n : ℕ} (d : ℕ) (a : FamilyJetVariables m n →₀ ℕ)
    (k : FamilyJetVariables m n) : combineMonomial d a (Sum.inr k) = a k := by
  rw [combineMonomial, Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp)]
  rw [zero_add]
  exact Finsupp.embDomain_apply ⟨Sum.inr, Sum.inr_injective⟩ a k

/-- A family jet monomial is determined by its spectral degree and its jet part. -/
theorem combineMonomial_jetPart {m n : ℕ} (s : FamilyJetIndex m n →₀ ℕ) :
    combineMonomial (s (Sum.inl ())) (jetPart s) = s := by
  ext t
  cases t with
  | inl a =>
      cases a
      rw [combineMonomial_inl]
  | inr k =>
      rw [combineMonomial_inr, jetPart_apply]

/-- The split is injective. -/
theorem familyMonomial_injective {m n : ℕ} {s s' : FamilyJetIndex m n →₀ ℕ}
    (hspec : s (Sum.inl ()) = s' (Sum.inl ())) (hjet : jetPart s = jetPart s') : s = s' := by
  rw [← combineMonomial_jetPart s, ← combineMonomial_jetPart s', hspec, hjet]

end

end GaloisForLFunctions.HTGeometry
