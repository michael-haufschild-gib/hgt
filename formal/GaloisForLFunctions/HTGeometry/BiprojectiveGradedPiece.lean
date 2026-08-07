import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Bigraded pieces of a biprojective coordinate ring

The polynomial coordinate ring of `P^m × P^n` has `m + 1` variables of weight `(1, 0)` and
`n + 1` variables of weight `(0, 1)`.  This module constructs an explicit monomial basis of every
bigraded piece and computes its dimension:

```text
dim_K R_(p,q) = choose (p + m) m * choose (q + n) n.
```

This is the denominator term in the bigraded Hilbert-series proof of multihomogeneous Bezout.  The
basis is indexed by a pair of weak compositions, one in each projective block; no Hilbert-series or
intersection-theory statement is assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Variables in the two homogeneous blocks of `P^m × P^n`. -/
abbrev BiprojVar (m n : ℕ) := Fin (m + 1) ⊕ Fin (n + 1)

/-- The standard bigrading: first-block variables have weight `(1, 0)` and second-block variables
have weight `(0, 1)`. -/
def biprojectiveWeight {m n : ℕ} : BiprojVar m n → ℕ × ℕ
  | Sum.inl _ => (1, 0)
  | Sum.inr _ => (0, 1)

/-- The bidegree of a monomial is the pair of total exponents in its two variable blocks. -/
theorem weight_biprojectiveWeight {m n : ℕ} (d : BiprojVar m n →₀ ℕ) :
    Finsupp.weight biprojectiveWeight d =
      ((Finsupp.sumFinsuppEquivProdFinsupp d).1.sum fun _ e => e,
       (Finsupp.sumFinsuppEquivProdFinsupp d).2.sum fun _ e => e) := by
  classical
  rw [Finsupp.weight]
  change d.sum (fun x e => e • biprojectiveWeight x) = _
  rw [Finsupp.sum, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
  apply Prod.ext <;>
    simp [biprojectiveWeight, Finsupp.comapDomain, Finsupp.sum, Prod.fst_sum, Prod.snd_sum]

/-- Exponents of bidegree `(p, q)` are exactly pairs of weak compositions of `p` and `q` in the
two variable blocks. -/
noncomputable def biprojExponentEquiv (m n p q : ℕ) :
    {d : BiprojVar m n →₀ ℕ // Finsupp.weight biprojectiveWeight d = (p, q)} ≃
      ((Finset.univ : Finset (Fin (m + 1))).finsuppAntidiag p ×
       (Finset.univ : Finset (Fin (n + 1))).finsuppAntidiag q) where
  toFun d :=
    let e := Finsupp.sumFinsuppEquivProdFinsupp d.1
    (⟨e.1, Finset.mem_finsuppAntidiag'.2 ⟨by
        have h := d.2
        rw [weight_biprojectiveWeight] at h
        exact congrArg Prod.fst h, by simp⟩⟩,
     ⟨e.2, Finset.mem_finsuppAntidiag'.2 ⟨by
        have h := d.2
        rw [weight_biprojectiveWeight] at h
        exact congrArg Prod.snd h, by simp⟩⟩)
  invFun e := ⟨Finsupp.sumFinsuppEquivProdFinsupp.symm (e.1.1, e.2.1), by
    rw [weight_biprojectiveWeight]
    apply Prod.ext
    · simpa using (Finset.mem_finsuppAntidiag'.1 e.1.2).1
    · simpa using (Finset.mem_finsuppAntidiag'.1 e.2.2).1⟩
  left_inv d := by
    apply Subtype.ext
    exact Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply d.1
  right_inv e := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.1, e.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd
        (Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (e.1.1, e.2.1))

/-- The `(p, q)`-bigraded piece of the biprojective polynomial ring. -/
abbrev BiprojectivePiece (K : Type*) [Field K] (m n p q : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule K
    (biprojectiveWeight : BiprojVar m n → ℕ × ℕ) (p, q)

/-- Raw monomial basis, indexed by exponent vectors of bidegree `(p, q)`. -/
noncomputable def biprojectiveMonomialBasisRaw (K : Type*) [Field K] (m n p q : ℕ) :
    Module.Basis
      {d : BiprojVar m n →₀ ℕ // Finsupp.weight biprojectiveWeight d = (p, q)} K
      (BiprojectivePiece K m n p q) := by
  rw [BiprojectivePiece,
    MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact MvPolynomial.basisRestrictSupport K _

/-- Monomial basis indexed by the pair of weak compositions in the two variable blocks. -/
noncomputable def biprojectiveMonomialBasis (K : Type*) [Field K] (m n p q : ℕ) :
    Module.Basis
      ((Finset.univ : Finset (Fin (m + 1))).finsuppAntidiag p ×
       (Finset.univ : Finset (Fin (n + 1))).finsuppAntidiag q) K
      (BiprojectivePiece K m n p q) :=
  (biprojectiveMonomialBasisRaw K m n p q).reindex (biprojExponentEquiv m n p q)

/-- **Dimension of a biprojective graded piece.**  Monomials of bidegree `(p, q)` are counted by
independent stars-and-bars choices in the two homogeneous blocks. -/
theorem finrank_biprojectivePiece (K : Type*) [Field K] (m n p q : ℕ) :
    Module.finrank K (BiprojectivePiece K m n p q) =
      (p + m).choose m * (q + n).choose n := by
  rw [Module.finrank_eq_card_basis (biprojectiveMonomialBasis K m n p q),
    Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show m + 1 + p - 1 = p + m by omega,
    show n + 1 + q - 1 = q + n by omega,
    Nat.choose_symm_add, Nat.choose_symm_add]

end GaloisForLFunctions.HTGeometry
