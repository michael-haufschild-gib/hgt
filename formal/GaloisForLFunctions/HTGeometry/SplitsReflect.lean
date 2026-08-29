import Mathlib

/-!
# Reversing the coefficient order preserves splitting

If `f` splits over a field `K` and `N` bounds its degree, then the reflected polynomial
`Polynomial.reflect N f` splits as well: each linear factor `X - a` becomes `1 - a·X`, and the
degree deficiency `N - deg f` is absorbed into a power of `X`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- The reflection of a monic split product of linear factors splits. -/
theorem splits_reflect_multiset_prod (s : Multiset K) :
    (Polynomial.reflect (Multiset.card s) ((s.map fun a => X - C a).prod)).Splits := by
  classical
  refine Multiset.induction_on s ?_ ?_
  · simp only [Multiset.card_zero, Multiset.map_zero, Multiset.prod_zero]
    rw [Polynomial.reflect_one]
    exact (Polynomial.Splits.X (R := K)).pow 0
  · intro a t ih
    have hprod : (((a ::ₘ t).map fun b => X - C b).prod : K[X])
        = (X - C a) * ((t.map fun b => X - C b).prod) := by
      simp
    have hcard : Multiset.card (a ::ₘ t) = 1 + Multiset.card t := by
      rw [Multiset.card_cons, Nat.add_comm]
    rw [hprod, hcard,
      Polynomial.reflect_mul _ _ (le_of_eq (natDegree_X_sub_C a))
        (le_of_eq (natDegree_multiset_prod_X_sub_C_eq_card t))]
    refine Polynomial.Splits.mul ?_ ih
    refine Polynomial.Splits.of_natDegree_le_one ?_
    refine le_trans Polynomial.natDegree_reflect_le ?_
    simp

/-- **Reflection preserves splitting.** -/
theorem Splits.reflect {f : K[X]} (hf : f.Splits) {N : ℕ} (hN : f.natDegree ≤ N) :
    (Polynomial.reflect N f).Splits := by
  classical
  have hroots : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.1 hf
  have hfac := hf.eq_prod_roots
  have hsplit : Polynomial.reflect N f
      = Polynomial.reflect (N - Multiset.card f.roots) (C f.leadingCoeff)
        * Polynomial.reflect (Multiset.card f.roots)
            ((f.roots.map fun a => X - C a).prod) := by
    conv_lhs => rw [hfac]
    rw [← Polynomial.reflect_mul _ _ (by simp)
      (le_of_eq (natDegree_multiset_prod_X_sub_C_eq_card _))]
    congr 1
    omega
  rw [hsplit]
  refine Polynomial.Splits.mul ?_ (splits_reflect_multiset_prod _)
  rw [Polynomial.reflect_C]
  exact (Polynomial.Splits.C _).mul (Polynomial.Splits.X.pow _)

end GaloisForLFunctions.HTGeometry
