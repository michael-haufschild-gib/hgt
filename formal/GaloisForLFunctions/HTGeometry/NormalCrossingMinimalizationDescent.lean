import GaloisForLFunctions.HTGeometry.MinimalConstraintPresentation

/-!
# Normal-crossing minimalization descent

Restricting one source direction in the normal-crossing hierarchy turns the full product into a
redundant generator of the lower-rank coface ideal.  It has one source-labelled elimination through
each coface.  Differences between these eliminations are exactly the nontrivial star classes of the
derived critical Koszul complex.

This identifies the exterior coherence classes with transition data for minimal presentations,
not merely static homology of one chosen generator sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.VeroneseIdeal
open MvPolynomial Finset

noncomputable section

variable {F : Type*} [Field F]

/-- The coface presentation augmented by the full normal-crossing product.  The `none` coordinate
is the terminal full-product generator. -/
def augmentedCofaceGenerator (r : ℕ) :
    Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F
  | none => normalCrossingPolynomial r
  | some i => cofaceMonomial r i

/-- The ideal presented by the cofaces together with the terminal full product. -/
noncomputable def augmentedCofaceIdeal (r : ℕ) :
    Ideal (MvPolynomial (Fin (r + 1)) F) :=
  presentedIdeal (augmentedCofaceGenerator (F := F) r)

/-- **Classical descent invariance.**  Adding the terminal full product to the lower-rank gradient
presentation does not change the critical ideal. -/
theorem augmentedCofaceIdeal_eq_veroneseIdeal (r : ℕ) :
    augmentedCofaceIdeal (F := F) r =
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [← normalCrossingJacobianIdeal_eq_veroneseIdeal]
  apply le_antisymm
  · rw [augmentedCofaceIdeal, presentedIdeal]
    refine Ideal.span_le.2 ?_
    rintro P ⟨i, rfl⟩
    cases i with
    | some i =>
        rw [augmentedCofaceGenerator, ← pderiv_normalCrossingPolynomial]
        exact Ideal.subset_span ⟨i, rfl⟩
    | none =>
        change normalCrossingPolynomial (F := F) r ∈
          normalCrossingJacobianIdeal r
        rw [normalCrossingPolynomial, ← X_mul_cofaceMonomial r 0,
          ← pderiv_normalCrossingPolynomial]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)
  · rw [normalCrossingJacobianIdeal]
    refine Ideal.span_le.2 ?_
    rintro P ⟨i, rfl⟩
    change pderiv i (normalCrossingPolynomial (F := F) r) ∈
      augmentedCofaceIdeal r
    rw [pderiv_normalCrossingPolynomial]
    apply Ideal.subset_span
    exact ⟨some i, rfl⟩

/-- The relation map of the augmented presentation. -/
def augmentedCofaceRelation (r : ℕ)
    (a : Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) :
    MvPolynomial (Fin (r + 1)) F :=
  a none * normalCrossingPolynomial r +
    ∑ i, a (some i) * cofaceMonomial r i

/-- Eliminate the terminal full product through the `i`th coface factorization
`f = X_i m_i`. -/
def cofaceElimination (r : ℕ) (i : Fin (r + 1)) :
    Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F
  | none => 1
  | some j => if j = i then -X i else 0

/-- Every source-labelled coface factorization is a genuine elimination relation for the terminal
generator. -/
theorem augmentedCofaceRelation_elimination (r : ℕ) (i : Fin (r + 1)) :
    augmentedCofaceRelation r (cofaceElimination (F := F) r i) = 0 := by
  rw [augmentedCofaceRelation]
  simp only [cofaceElimination, one_mul]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, neg_mul, X_mul_cofaceMonomial]
    exact add_neg_cancel _
  · intro j hj hji
    rw [if_neg hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The lower-rank coefficient difference between two eliminations. -/
def cofaceEliminationDifference (r : ℕ) (i k : Fin (r + 1)) :
    Fin (r + 1) → MvPolynomial (Fin (r + 1)) F :=
  fun j => cofaceElimination r i (some j) - cofaceElimination r k (some j)

/-- **Minimalization/star identification.**  Relative to the zeroth elimination, the difference
of the `i+1`st elimination is exactly the canonical star syzygy. -/
theorem cofaceEliminationDifference_zero_succ (r : ℕ) (i : Fin r) :
    cofaceEliminationDifference (F := F) r 0 i.succ =
      cofaceStarSyzygy r i := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have hzero : (0 : Fin (r + 1)) ≠ i.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [cofaceEliminationDifference, cofaceElimination,
      cofaceStarSyzygy, cofaceBoundary, hzero]
  · by_cases hki : k = i
    · subst k
      simp [cofaceEliminationDifference, cofaceElimination,
        cofaceStarSyzygy, cofaceBoundary]
    · have hsucc : k.succ ≠ i.succ := by simpa using hki
      simp [cofaceEliminationDifference, cofaceElimination,
        cofaceStarSyzygy, cofaceBoundary, hki, hsucc]

/-- Differences of source-labelled minimalizations are genuine coface cycles. -/
theorem cofaceRelation_eliminationDifference_zero_succ
    (r : ℕ) (i : Fin r) :
    cofaceRelation r (cofaceEliminationDifference (F := F) r 0 i.succ) = 0 := by
  rw [cofaceEliminationDifference_zero_succ]
  exact cofaceRelation_starSyzygy r i

/-- **Relative-minimalization defect theorem.**  From three lower-rank source coordinates onward,
two source-labelled eliminations of the terminal generator differ by a nontrivial derived class;
their difference is not even in the coordinatewise envelope containing every genuine degree-two
Koszul boundary. -/
theorem cofaceEliminationDifference_not_boundary
    {r : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    ¬ ∃ b : Fin (r + 1) → Fin (r + 1) →
        MvPolynomial (Fin (r + 1)) F,
      cofaceKoszulBoundaryEnvelope r b =
        cofaceEliminationDifference r 0 i.succ := by
  rw [cofaceEliminationDifference_zero_succ]
  exact cofaceStarSyzygy_not_koszulBoundaryEnvelope hr i

/-- The polynomial coefficient carried by a finite family of source-labelled minimalization
directions.  In the normal-crossing model, a `p`-fold coherence is labelled by the squarefree
product of the corresponding `p` structural coordinates. -/
def relativeMinimalizationCoherenceCoefficient (r : ℕ)
    (J : Finset (Fin (r + 1))) : MvPolynomial (Fin (r + 1)) F :=
  ∏ j ∈ J, X j

/-- **Normal-crossing diagonal purity.**  The polynomial degree of a coherence coefficient is
exactly the number of source-labelled minimalization directions which create it.  Thus the source
depth and algebraic degree filtrations agree on every squarefree coherence label. -/
theorem relativeMinimalizationCoherenceCoefficient_totalDegree (r : ℕ)
    (J : Finset (Fin (r + 1))) :
    MvPolynomial.totalDegree
        (relativeMinimalizationCoherenceCoefficient (F := F) r J) = J.card := by
  rw [relativeMinimalizationCoherenceCoefficient, prod_X_eq_monomial,
    totalDegree_monomial _ one_ne_zero]
  simp [Finsupp.sum, support_sum_single]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

/-- The distinguished coefficient of a two-fold minimalization coherence has pure degree two.
This is the first nontrivial case of diagonal purity which is already realized by the star-wedge
Koszul class. -/
theorem cofaceStarWedge_distinguished_totalDegree
    (r : ℕ) (i k : Fin r) (hik : i ≠ k) :
    MvPolynomial.totalDegree
        (cofaceStarWedge (F := F) r i k i.succ k.succ) = 2 := by
  rw [cofaceStarWedge_succ_succ r hik]
  rw [show X i.succ * X k.succ =
      relativeMinimalizationCoherenceCoefficient (F := F) r {i.succ, k.succ} by
        simp [relativeMinimalizationCoherenceCoefficient, hik]]
  rw [relativeMinimalizationCoherenceCoefficient_totalDegree]
  simp [hik]

end

end GaloisForLFunctions.HTGeometry
