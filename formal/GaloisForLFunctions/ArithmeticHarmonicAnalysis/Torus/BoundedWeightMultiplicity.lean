import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedWeightNormalForm
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Tactic

/-!
# Exact bounded monomial and torus-weight multiplicities

Adding one padding variable identifies monomials of degree at most `D` with
multisets of size `D`. Their cardinality is therefore a binomial coefficient.
For paired torus weights, the minimal monomial consumes the slack and each
neutral factor consumes one further unit of cut degree. The resulting
slack-shifted binomial is the dimension of the actual bounded weight subspace.

These are the polynomial counting mechanisms in §6.1 of Brown,
*Equivariant Quantisation of Hypertoric Varieties via Symplectic Cuts*.
No geometric quotient or cohomological vanishing is assumed here.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {ι : Type*} [Fintype ι]

private def boundedCompositionEquiv (D : ℕ) :
    {s : ι → ℕ // ∑ i, s i ≤ D} ≃ {t : Option ι → ℕ // ∑ i, t i = D} where
  toFun s := ⟨fun i => i.elim (D - ∑ j, s.1 j) s.1, by
    rw [Fintype.sum_option]
    change (D - ∑ j, s.1 j) + ∑ j, s.1 j = D
    omega⟩
  invFun t := ⟨fun i => t.1 (some i), by
    have ht := t.2
    rw [Fintype.sum_option] at ht
    change (∑ i, t.1 (some i)) ≤ D
    omega⟩
  left_inv s := by apply Subtype.ext; rfl
  right_inv t := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have ht := t.2
      rw [Fintype.sum_option] at ht
      change D - ∑ j, t.1 (some j) = t.1 none
      omega
    | some i => rfl

private def compositionSymEquiv (D : ℕ) :
    {s : ι → ℕ // ∑ i, s i = D} ≃ Sym ι D := by
  classical
  refine {
    toFun := fun s => ⟨(Finsupp.equivFunOnFinite.symm s.1).toMultiset, ?_⟩
    invFun := fun t => ⟨fun i => t.1.count i, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by intro i; rfl)]
    simpa using s.2
  · have h := Multiset.toFinsupp_sum_eq t.1
    rw [Finsupp.sum_fintype _ _ (by intro i; rfl)] at h
    exact h.trans t.2
  · intro s
    apply Subtype.ext
    funext i
    simp
  · intro t
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro i
    simp

/-- Weak compositions with bounded sum are counted by one extra padding coordinate. -/
theorem card_bounded_compositions (D : ℕ) :
    Nat.card {s : ι → ℕ // ∑ i, s i ≤ D} = (Fintype.card ι + D).choose D := by
  classical
  rw [Nat.card_congr ((boundedCompositionEquiv (ι := ι) D).trans
    (compositionSymEquiv D)), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  congr 1
  simp only [Fintype.card_option]
  omega

private def supportedExponentEquiv {α : Type*} (S : Finset α) :
    {m : α →₀ ℕ // m.support ⊆ S} ≃ (S → ℕ) :=
  (Finsupp.supportedEquivFinsupp (R := ℕ) (M := ℕ) (S : Set α)).toEquiv.trans
    Finsupp.equivFunOnFinite

private theorem supportedExponentEquiv_sum {α : Type*} (S : Finset α)
    (m : {m : α →₀ ℕ // m.support ⊆ S}) :
    (∑ i, supportedExponentEquiv S m i) = m.1.sum (fun _ n => n) := by
  change (∑ i : S, m.1 i) = _
  have h := Finsupp.sum_subtypeDomain_index
    (v := m.1) (h := fun _ (n : ℕ) => n) m.2
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)] at h
  exact h

private def boundedSupportedExponentEquiv {α : Type*} (S : Finset α) (D : ℕ) :
    {m : α →₀ ℕ // m.support ⊆ S ∧ m.sum (fun _ n => n) ≤ D} ≃
      {s : S → ℕ // ∑ i, s i ≤ D} where
  toFun m := ⟨supportedExponentEquiv S ⟨m.1, m.2.1⟩, by
    rw [supportedExponentEquiv_sum]
    exact m.2.2⟩
  invFun s := ⟨((supportedExponentEquiv S).symm s.1).1,
    ((supportedExponentEquiv S).symm s.1).2, by
      have h := supportedExponentEquiv_sum S ((supportedExponentEquiv S).symm s.1)
      rw [Equiv.apply_symm_apply] at h
      rw [← h]
      exact s.2⟩
  left_inv m := by
    apply Subtype.ext
    exact congrArg (fun x : {m : α →₀ ℕ // m.support ⊆ S} => x.1)
      ((supportedExponentEquiv S).symm_apply_apply ⟨m.1, m.2.1⟩)
  right_inv s := by
    apply Subtype.ext
    exact (supportedExponentEquiv S).apply_symm_apply s.1

/-- Exact number of bounded-degree monomials on any finite set of variables. -/
theorem card_bounded_supported_exponents {α : Type*} (S : Finset α) (D : ℕ) :
    Nat.card {m : α →₀ ℕ // m.support ⊆ S ∧ m.sum (fun _ n => n) ≤ D} =
      (S.card + D).choose D := by
  rw [Nat.card_congr (boundedSupportedExponentEquiv S D), card_bounded_compositions,
    Fintype.card_coe]

private def cutWeightExponentEquiv (q : ι → ℤ) (D : ℕ) :
    {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q ∧ cutDegree d ≤ weightSlack q + D} ≃
      {s : ι → ℕ // ∑ i, s i ≤ D} where
  toFun d := ⟨(weightExponentEquiv q).symm ⟨d.1, d.2.1⟩, by
    have hd := cutDegree_normalWeightExponent q
      ((weightExponentEquiv q).symm ⟨d.1, d.2.1⟩)
    have he : normalWeightExponent q ((weightExponentEquiv q).symm ⟨d.1, d.2.1⟩) = d.1 :=
      congrArg (fun x : {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q} => x.1)
        ((weightExponentEquiv q).apply_symm_apply ⟨d.1, d.2.1⟩)
    rw [he] at hd
    have hb := d.2.2
    omega⟩
  invFun s := ⟨normalWeightExponent q s.1, pairedWeight_normal q s.1, by
    rw [cutDegree_normalWeightExponent]
    exact Nat.add_le_add_left s.2 _⟩
  left_inv d := by
    apply Subtype.ext
    exact congrArg (fun x : {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q} => x.1)
      ((weightExponentEquiv q).apply_symm_apply ⟨d.1, d.2.1⟩)
  right_inv s := by
    apply Subtype.ext
    exact (weightExponentEquiv q).symm_apply_apply s.1

/-- At slack plus `D`, the weight multiplicity is the number of neutral monomials of degree at most `D`. -/
theorem card_weight_exponents_at_slack (q : ι → ℤ) (D : ℕ) :
    Nat.card {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q ∧
      cutDegree d ≤ weightSlack q + D} = (Fintype.card ι + D).choose D := by
  rw [Nat.card_congr (cutWeightExponentEquiv q D), card_bounded_compositions]

/-- Exact cut multiplicity, with zero below the first admissible degree. -/
theorem card_bounded_weight_exponents (q : ι → ℤ) (D : ℕ) :
    Nat.card {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q ∧ cutDegree d ≤ D} =
      if weightSlack q ≤ D then (Fintype.card ι + (D - weightSlack q)).choose
        (D - weightSlack q) else 0 := by
  by_cases h : weightSlack q ≤ D
  · rw [if_pos h]
    have he : weightSlack q + (D - weightSlack q) = D := Nat.add_sub_of_le h
    simpa only [he] using card_weight_exponents_at_slack q (D - weightSlack q)
  · rw [if_neg h]
    haveI : IsEmpty {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q ∧ cutDegree d ≤ D} :=
      ⟨by
        intro d
        have hd := weightSlack_le_cutDegree d.1
        rw [d.2.1] at hd
        exact h (hd.trans d.2.2)⟩
    simp

/-- Polynomials of one torus character whose cut degree is at most `D`. -/
def boundedPairedWeightSpace (K : Type*) [Field K] (q : ι → ℤ) (D : ℕ) :
    Submodule K (MvPolynomial (ι ⊕ ι) K) :=
  MvPolynomial.restrictSupport K {d | pairedWeight d = q ∧ cutDegree d ≤ D}

/-- The actual polynomial weight subspace has the slack-shifted binomial dimension. -/
theorem finrank_boundedPairedWeightSpace (K : Type*) [Field K] (q : ι → ℤ) (D : ℕ) :
    Module.finrank K (boundedPairedWeightSpace K q D) =
      if weightSlack q ≤ D then (Fintype.card ι + (D - weightSlack q)).choose
        (D - weightSlack q) else 0 := by
  calc
    Module.finrank K (boundedPairedWeightSpace K q D) =
        Nat.card {d : (ι ⊕ ι) →₀ ℕ // pairedWeight d = q ∧ cutDegree d ≤ D} :=
      Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)
    _ = _ := card_bounded_weight_exponents q D

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_bounded_supported_exponents
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_bounded_weight_exponents
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.finrank_boundedPairedWeightSpace
