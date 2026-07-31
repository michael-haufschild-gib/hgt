import GaloisForLFunctions.HTGeometry.ProjectiveHorizonObserverLieAlgebra
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFrameCodimension

/-!
# The Jacobian of the observer Lie algebra on the reduced block

The observer Lie algebra of a covector span of rank `r` has dimension `rN-1`, matching the reduced
block of jet coordinates.  A basis of it is indexed by the reduced block itself: an off-diagonal
index gives an elementary transvection, and a diagonal index gives the traceless diagonal pairing
that direction with the omitted one.

Applying those infinitesimal observers to the reduced block gives a square matrix over the jet
field, whose entries are entries of the jet frame of the span.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Infinitesimal observers on jet coordinates -/

omit [DecidableEq n] in
theorem jetDerivation_neg (M : Matrix n n K) : jetDerivation (-M) = -jetDerivation M := by
  have h : (-M : Matrix n n K) = (-1 : K) • M := by rw [neg_smul, one_smul]
  rw [h, jetDerivation_smul, neg_smul, one_smul]

omit [DecidableEq n] in
theorem jetDerivation_sub (M M' : Matrix n n K) :
    jetDerivation (M - M') = jetDerivation M - jetDerivation M' := by
  rw [sub_eq_add_neg, jetDerivation_add, jetDerivation_neg, ← sub_eq_add_neg]

/-- An elementary infinitesimal transvection moves the jet coordinate of its row to the jet
coordinate of its column. -/
theorem jetDerivation_single_freeCoordinate (a b : n) (k : n) (l : ℕ) :
    jetDerivation (Matrix.single a b (1 : K)) (freeCoordinate K (n × ℕ) (k, l)) =
      (if a = k then freeCoordinate K (n × ℕ) (b, l) else 0) := by
  rw [jetDerivation_freeCoordinate]
  by_cases hak : a = k
  · rw [if_pos hak, Finset.sum_eq_single b]
    · rw [Matrix.single_apply, if_pos ⟨hak, rfl⟩, map_one, one_mul]
    · intro m _ hm
      rw [Matrix.single_apply, if_neg fun h => hm h.2.symm, map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ b) hcon
  · rw [if_neg hak]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hak h.1, map_zero, zero_mul]

/-! ## The basis of the observer Lie algebra indexed by the reduced block -/

/-- The infinitesimal observer attached to an index of the reduced block: an elementary
transvection off the diagonal, and the traceless diagonal pairing with the omitted index on it. -/
def reducedGen (t : Finset n) (m₀ : ↥t) (p : n × ↥t) : Matrix n n K :=
  if p.1 = (p.2 : n) then
    Matrix.single (p.2 : n) (p.2 : n) (1 : K) - Matrix.single (m₀ : n) (m₀ : n) (1 : K)
  else Matrix.single p.1 (p.2 : n) (1 : K)

theorem reducedGen_mem_span (t : Finset n) (m₀ : ↥t) {p : n × ↥t}
    (hp : p ≠ ((m₀ : n), m₀)) :
    reducedGen t m₀ p ∈ Submodule.span K (observerGenerators (↑t : Set n) K) := by
  rw [reducedGen]
  by_cases hd : p.1 = (p.2 : n)
  · rw [if_pos hd]
    have hne : (p.2 : n) ≠ (m₀ : n) := by
      intro hcon
      exact hp (Prod.ext (hd.trans hcon) (Subtype.ext hcon))
    exact Submodule.subset_span
      (diag_mem_observerGenerators (Finset.mem_coe.2 p.2.2) (Finset.mem_coe.2 m₀.2) hne)
  · rw [if_neg hd]
    exact Submodule.subset_span
      (single_mem_observerGenerators (Finset.mem_coe.2 p.2.2) hd)

/-- The infinitesimal observer of a reduced block index applied to a jet coordinate. -/
theorem jetDerivation_reducedGen_freeCoordinate (t : Finset n) (m₀ : ↥t) (p : n × ↥t)
    (k : n) (l : ℕ) :
    jetDerivation (reducedGen (K := K) t m₀ p) (freeCoordinate K (n × ℕ) (k, l)) =
      (if p.1 = k then freeCoordinate K (n × ℕ) ((p.2 : n), l) else 0) -
        (if p.1 = (p.2 : n) then
          (if (m₀ : n) = k then freeCoordinate K (n × ℕ) ((m₀ : n), l) else 0) else 0) := by
  rw [reducedGen]
  by_cases hd : p.1 = (p.2 : n)
  · rw [if_pos hd, if_pos hd, jetDerivation_sub, Derivation.sub_apply,
      jetDerivation_single_freeCoordinate, jetDerivation_single_freeCoordinate, hd]
  · rw [if_neg hd, if_neg hd, jetDerivation_single_freeCoordinate, sub_zero]

/-! ## The Jacobian -/

/-- The index set of the reduced block of a span. -/
abbrev ReducedIndex (t : Finset n) (m₀ : ↥t) := {p : n × ↥t // p ≠ ((m₀ : n), m₀)}

/-- The reduced block, as a family indexed by its own index set. -/
def reducedFamily (t : Finset n) (m₀ : ↥t) (q : ReducedIndex t m₀) : HomogeneousJetField n K :=
  freeCoordinate K (n × ℕ) ((q : n × ↥t).1, jetOrder t (q : n × ↥t).2)

/-- **The observer Jacobian.**  The infinitesimal observers of a span, indexed by the reduced
block, applied to the reduced block. -/
def observerJacobian (t : Finset n) (m₀ : ↥t) :
    Matrix (ReducedIndex t m₀) (ReducedIndex t m₀) (HomogeneousJetField n K) :=
  Matrix.of fun p q =>
    jetDerivation (reducedGen t m₀ (p : n × ↥t)) (reducedFamily (K := K) t m₀ q)

/-- The entries of the observer Jacobian are entries of the jet frame of the span. -/
theorem observerJacobian_apply (t : Finset n) (m₀ : ↥t) (p q : ReducedIndex t m₀) :
    observerJacobian (K := K) t m₀ p q =
      (if (p : n × ↥t).1 = (q : n × ↥t).1 then
        jetFrame (K := K) t (p : n × ↥t).2 (q : n × ↥t).2 else 0) -
      (if (p : n × ↥t).1 = ((p : n × ↥t).2 : n) then
        (if (m₀ : n) = (q : n × ↥t).1 then jetFrame (K := K) t m₀ (q : n × ↥t).2 else 0)
        else 0) :=
  jetDerivation_reducedGen_freeCoordinate t m₀ _ _ _

end

end GaloisForLFunctions.HTGeometry
