import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame

/-!
# Closed graph of the canonical inverse-Cholesky factor

Strict positivity of the triangular diagonal appears non-closed.  On the inverse-Cholesky locus,
however, singular diagonal entries are impossible because the determinant identity equals one.
Consequently the canonical positive-diagonal normalization is equivalent to a closed
nonnegative-diagonal condition.  This module proves that equivalence and the resulting closed
graph over the positive-definite cone.  Compact-range control is the only remaining topological
ingredient needed to promote this closed graph to continuity.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder Topology BigOperators

noncomputable section

variable {N : ℕ}

/-- Closed version of the canonical inverse-Cholesky conditions: the diagonal is real and
nonnegative rather than strictly positive. -/
def IsClosedCanonicalInverseCholeskyFrame
    (C G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsInverseCholeskyFrame C G ∧
    C.BlockTriangular (fun i : Fin N => OrderDual.toDual i) ∧
      ∀ i, (C i i).im = 0 ∧ 0 ≤ (C i i).re

/-- The determinant of any inverse-Cholesky frame is nonzero. -/
theorem inverseCholesky_det_ne_zero
    (C G : Matrix (Fin N) (Fin N) ℂ) (h : IsInverseCholeskyFrame C G) :
    C.det ≠ 0 := by
  intro hzero
  have hid := det_identity_of_inverseCholesky C G h
  rw [hzero, zero_mul, zero_mul] at hid
  exact zero_ne_one hid

/-- On the inverse-Cholesky locus, a real nonnegative triangular diagonal is automatically
strictly positive. -/
theorem closedCanonicalInverseCholesky_iff_canonical
    (C G : Matrix (Fin N) (Fin N) ℂ) :
    IsClosedCanonicalInverseCholeskyFrame C G ↔
      IsCanonicalInverseCholeskyFrame C G := by
  constructor
  · rintro ⟨hinv, htri, hdiag⟩
    refine ⟨hinv, htri, ?_⟩
    intro i
    refine ⟨(hdiag i).1, lt_of_le_of_ne (hdiag i).2 ?_⟩
    intro hre
    have hentry : C i i = 0 := by
      apply Complex.ext
      · simpa using hre.symm
      · simpa using (hdiag i).1
    have hdetzero : C.det = 0 := by
      rw [Matrix.det_of_lowerTriangular C htri]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hentry
    exact inverseCholesky_det_ne_zero C G hinv hdetzero
  · rintro ⟨hinv, htri, hdiag⟩
    exact ⟨hinv, htri, fun i => ⟨(hdiag i).1, (hdiag i).2.le⟩⟩

/-- Positive-definite Gram matrices as a topological subtype. -/
abbrev PositiveDefiniteGram (N : ℕ) :=
  {G : Matrix (Fin N) (Fin N) ℂ // G.PosDef}

/-- Graph of the canonical positive-diagonal inverse-Cholesky factor over the positive-definite
cone. -/
def canonicalInverseCholeskyGraph (N : ℕ) :
    Set (PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ) :=
  {p | IsCanonicalInverseCholeskyFrame p.2 p.1.1}

/-- The canonical inverse-Cholesky graph is closed over the positive-definite cone. -/
theorem isClosed_canonicalInverseCholeskyGraph (N : ℕ) :
    IsClosed (canonicalInverseCholeskyGraph N) := by
  have hinv : IsClosed {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
      IsInverseCholeskyFrame p.2 p.1.1} := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  have htri : IsClosed {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
      p.2.BlockTriangular (fun i : Fin N => OrderDual.toDual i)} := by
    rw [show {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          p.2.BlockTriangular (fun i : Fin N => OrderDual.toDual i)} =
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_h : OrderDual.toDual j < OrderDual.toDual i),
          {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ | p.2 i j = 0} by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rfl]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hij
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have him : IsClosed
      {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
        ∀ i : Fin N, (p.2 i i).im = 0} := by
    rw [show {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          ∀ i : Fin N, (p.2 i i).im = 0} =
        ⋂ i : Fin N,
          {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
            (p.2 i i).im = 0} by ext p; simp]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hre : IsClosed
      {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
        ∀ i : Fin N, 0 ≤ (p.2 i i).re} := by
    rw [show {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          ∀ i : Fin N, 0 ≤ (p.2 i i).re} =
        ⋂ i : Fin N,
          {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
            0 ≤ (p.2 i i).re} by ext p; simp]
    apply isClosed_iInter
    intro i
    exact isClosed_le (by fun_prop) (by fun_prop)
  rw [show canonicalInverseCholeskyGraph N =
      {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
        IsInverseCholeskyFrame p.2 p.1.1} ∩
        ({p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          p.2.BlockTriangular (fun i : Fin N => OrderDual.toDual i)} ∩
        ({p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          ∀ i : Fin N, (p.2 i i).im = 0} ∩
        {p : PositiveDefiniteGram N × Matrix (Fin N) (Fin N) ℂ |
          ∀ i : Fin N, 0 ≤ (p.2 i i).re})) by
    ext p
    simp only [canonicalInverseCholeskyGraph, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [← closedCanonicalInverseCholesky_iff_canonical]
    simp only [IsClosedCanonicalInverseCholeskyFrame, forall_and]]
  exact hinv.inter (htri.inter (him.inter hre))

end

end GaloisForLFunctions.HTGeometry
