import GaloisForLFunctions.HilbertMetric.PolynomialMomentCancellation
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# Symmetric polynomial Fock kernel

The degree-`n` power of the Euclidean inner-product sum is the Gram kernel of distinct
degree-`n` monomial features with their exact multinomial weights.  Grading these homogeneous
multi-indices through degree `M` gives an injective exponent family, hence distinct unisolvent
nodes and exact cross-degree moment cancellation.

This replaces the redundant ordered-word expansion by a minimal symmetric feature index.  The
result is the finite polynomial Fock model needed to turn the degree-five collision jet into a
matrix jet without assuming a basis of coherent vectors.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Multi-indices of exact total degree `n` on `d` coordinates. -/
abbrev HomogeneousMultiIndex (d n : ℕ) :=
  ↥(Finset.piAntidiag (Finset.univ : Finset (Fin d)) n)

/-- The minimal degree-`n` symmetric feature space has the stars-and-bars dimension. -/
theorem homogeneousMultiIndex_card (d n : ℕ) :
    Fintype.card (HomogeneousMultiIndex d n) = Nat.choose (d + n - 1) n := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose
    (s := (Finset.univ : Finset (Fin d))) n
  simpa only [HomogeneousMultiIndex, Finset.finsuppAntidiag, Finset.card_map,
    Finset.card_attach, Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using h

/-- A homogeneous multi-index as a finitely supported exponent vector. -/
def HomogeneousMultiIndex.exponent {d n : ℕ} (q : HomogeneousMultiIndex d n) :
    Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm q.1

/-- The exponent representation of homogeneous multi-indices is injective. -/
theorem HomogeneousMultiIndex.exponent_injective {d n : ℕ} :
    Function.Injective (HomogeneousMultiIndex.exponent (d := d) (n := n)) := by
  intro q r h
  apply Subtype.ext
  funext i
  exact DFunLike.congr_fun h i

/-- A homogeneous monomial feature is the corresponding coordinate product. -/
theorem monomialFeature_homogeneous_eq_prod {d n : ℕ}
    (q : HomogeneousMultiIndex d n) (x : Fin d → ℝ) :
    monomialFeature HomogeneousMultiIndex.exponent q x =
      ∏ i, x i ^ q.1 i := by
  rw [monomialFeature, MvPolynomial.eval_monomial, one_mul]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

/-- **Symmetric polynomial Fock law.**  The degree-`n` power kernel is the weighted Gram
kernel of the minimal homogeneous monomial family. -/
theorem innerPower_eq_sum_homogeneousMonomial (d n : ℕ) (x y : Fin d → ℝ) :
    (∑ i, x i * y i) ^ n =
      ∑ q : HomogeneousMultiIndex d n,
        (Nat.multinomial Finset.univ q.1 : ℝ) *
          monomialFeature HomogeneousMultiIndex.exponent q x *
            monomialFeature HomogeneousMultiIndex.exponent q y := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro q hq
  rw [monomialFeature_homogeneous_eq_prod, monomialFeature_homogeneous_eq_prod]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  ring

/-- Homogeneous multi-indices, graded through degree `M`. -/
abbrev GradedMultiIndex (d M : ℕ) :=
  Σ n : Fin (M + 1), HomogeneousMultiIndex d n

/-- The exponent vector of a graded multi-index. -/
def GradedMultiIndex.exponent {d M : ℕ} (q : GradedMultiIndex d M) : Fin d →₀ ℕ :=
  q.2.exponent

/-- The coordinate sum of a homogeneous multi-index is its grading degree. -/
theorem HomogeneousMultiIndex.sum_eq_degree {d n : ℕ} (q : HomogeneousMultiIndex d n) :
    ∑ i, q.1 i = n := by
  exact (Finset.mem_piAntidiag.mp q.2).1

/-- The exponent vector remembers both the monomial and its degree in the graded index. -/
theorem GradedMultiIndex.exponent_injective {d M : ℕ} :
    Function.Injective (GradedMultiIndex.exponent (d := d) (M := M)) := by
  intro q r h
  have hdegree : q.1 = r.1 := by
    apply Fin.ext
    rw [← q.2.sum_eq_degree, ← r.2.sum_eq_degree]
    apply Finset.sum_congr rfl
    intro i hi
    exact DFunLike.congr_fun h i
  cases q with
  | mk qn qa =>
      cases r with
      | mk rn ra =>
          dsimp at hdegree
          subst rn
          apply congrArg (fun z : HomogeneousMultiIndex d qn =>
            (⟨qn, z⟩ : GradedMultiIndex d M))
          apply HomogeneousMultiIndex.exponent_injective
          exact h

/-- **Graded polynomial cancellation law.**  The minimal symmetric Fock features through degree
`M` admit pairwise distinct Euclidean nodes and exact cross-degree delta moments. -/
theorem exists_gradedMonomial_unisolvent_delta (d M : ℕ) :
    ∃ (nodes : GradedMultiIndex d M → (Fin d → ℝ))
      (coefficient : GradedMultiIndex d M → GradedMultiIndex d M → ℝ),
      Function.Injective nodes ∧
      ∀ q r, ∑ i, coefficient q i *
          monomialFeature GradedMultiIndex.exponent r (nodes i) =
        if q = r then 1 else 0 :=
  exists_injective_nodes_monomial_delta _ GradedMultiIndex.exponent_injective

end

end GaloisForLFunctions.HilbertMetric
