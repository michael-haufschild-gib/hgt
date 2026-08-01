import GaloisForLFunctions.RHTower.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact

/-!
# Multiplier operators along a Hilbert basis

A bounded multiplier sequence `lam : ℕ → ℂ` defines a diagonal operator on `ℓ²`.  Transporting it
through the coordinate isometry of a Hilbert basis produces an operator on any complex Hilbert
space carrying a countable Hilbert basis, with the basis vectors as eigenvectors and `lam` as the
eigenvalues.

The transported operator inherits everything proved of the diagonal model: it is compact when the
multiplier tends to zero, and symmetric — hence self-adjoint — when the multiplier is real.  This
is the bridge that turns a known matrix of an operator in some orthonormal basis into the operator
itself, without re-proving any spectral theory on the target space.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology _root_.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The coordinate isometry of a Hilbert basis, as a continuous linear equivalence. -/
def basisCoordEquiv (b : HilbertBasis ℕ ℂ E) : E ≃L[ℂ] _root_.RHTower.EllTwo :=
  b.repr.toContinuousLinearEquiv

/-- The multiplier operator attached to a Hilbert basis and a bounded multiplier sequence. -/
def basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, ‖lam n‖ ≤ C) : E →L[ℂ] E :=
  conjugateOperator (basisCoordEquiv b) (diagonalOperator lam hC)

omit [CompleteSpace E] in
/-- The multiplier operator acts by passing to coordinates, multiplying, and coming back. -/
theorem basisMultiplierOperator_apply (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, ‖lam n‖ ≤ C) (x : E) :
    basisMultiplierOperator b lam hC x
      = b.repr.symm (diagonalOperator lam hC (b.repr x)) := rfl

omit [CompleteSpace E] in
/-- The basis vectors are eigenvectors, with the multiplier entries as eigenvalues. -/
theorem basisMultiplierOperator_apply_basis (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, ‖lam n‖ ≤ C) (n : ℕ) :
    basisMultiplierOperator b lam hC (b n) = lam n • b n := by
  have hdiag : diagonalOperator lam hC (lp.single 2 n (1 : ℂ))
      = lam n • lp.single 2 n (1 : ℂ) := by
    have h := diagonalOperator_lpBasis lam hC n
    rwa [HilbertSchmidt.lpBasis_apply] at h
  rw [basisMultiplierOperator_apply, b.repr_self, hdiag, map_smul]
  congr 1
  rw [← b.repr_self, b.repr.symm_apply_apply]

omit [CompleteSpace E] in
/-- A multiplier tending to zero gives a compact operator on the target space. -/
theorem isCompactOperator_basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ) {C : ℝ}
    (hC : ∀ n, ‖lam n‖ ≤ C) (hlim : Tendsto (fun n => ‖lam n‖) atTop (𝓝 0)) :
    IsCompactOperator (basisMultiplierOperator b lam hC) :=
  (isCompactOperator_conjugateOperator_iff (basisCoordEquiv b) (diagonalOperator lam hC)).mpr
    (isCompactOperator_diagonalOperator lam hC hlim)

omit [CompleteSpace E] in
/-- Symmetry transports through the coordinate isometry: a real multiplier gives a symmetric
operator on the target space. -/
theorem isSymmetric_basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) :
    ((basisMultiplierOperator b (fun n => (r n : ℂ)) hC : E →L[ℂ] E) :
      E →ₗ[ℂ] E).IsSymmetric := by
  intro x y
  show inner ℂ (basisMultiplierOperator b (fun n => (r n : ℂ)) hC x) y
      = inner ℂ x (basisMultiplierOperator b (fun n => (r n : ℂ)) hC y)
  rw [basisMultiplierOperator_apply, basisMultiplierOperator_apply,
    ← b.repr.inner_map_map (b.repr.symm
      (diagonalOperator (fun n => (r n : ℂ)) hC (b.repr x))) y,
    ← b.repr.inner_map_map x (b.repr.symm
      (diagonalOperator (fun n => (r n : ℂ)) hC (b.repr y))),
    b.repr.apply_symm_apply, b.repr.apply_symm_apply]
  exact isSymmetric_diagonalOperator_ofReal r hC (b.repr x) (b.repr y)

/-- A real multiplier gives a self-adjoint operator on the target space. -/
theorem isSelfAdjoint_basisMultiplierOperator (b : HilbertBasis ℕ ℂ E) (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) :
    IsSelfAdjoint (basisMultiplierOperator b (fun n => (r n : ℂ)) hC) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_basisMultiplierOperator b r hC)

/-! ## Bases indexed by other countable types

The diagonal model is indexed by `ℕ`, but the orthonormal bases that occur in practice are often
indexed by `ℤ`.  Reindexing a Hilbert basis along an equivalence from `ℕ` removes that restriction:
the reindexed family is still orthonormal, and its range — hence its closed span — is unchanged. -/

section Reindex

variable {ι : Type*}

/-- Reindex a Hilbert basis along an equivalence from `ℕ`. -/
def hilbertBasisReindex (b : HilbertBasis ι ℂ E) (e : ℕ ≃ ι) : HilbertBasis ℕ ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective)
    (by
      have hrange : Set.range (⇑b ∘ e) = Set.range ⇑b := by
        rw [Set.range_comp, e.range_eq_univ, Set.image_univ]
      rw [hrange, b.dense_span])

@[simp] theorem hilbertBasisReindex_apply (b : HilbertBasis ι ℂ E) (e : ℕ ≃ ι) (n : ℕ) :
    hilbertBasisReindex b e n = b (e n) := by
  have h := HilbertBasis.coe_mk (b.orthonormal.comp e e.injective)
    (v := ⇑b ∘ e)
    (by
      have hrange : Set.range (⇑b ∘ e) = Set.range ⇑b := by
        rw [Set.range_comp, e.range_eq_univ, Set.image_univ]
      rw [hrange, b.dense_span])
  exact congrFun h n

omit [CompleteSpace E] in
/-- A multiplier vanishing along the cofinite filter of the original index set vanishes along
`atTop` after reindexing. -/
theorem tendsto_reindex_atTop_of_tendsto_cofinite {lam : ι → ℂ} (e : ℕ ≃ ι)
    (h : Filter.Tendsto (fun i => ‖lam i‖) Filter.cofinite (𝓝 0)) :
    Filter.Tendsto (fun n => ‖lam (e n)‖) atTop (𝓝 0) := by
  have he : Filter.Tendsto e Filter.cofinite Filter.cofinite := e.injective.tendsto_cofinite
  rw [← Nat.cofinite_eq_atTop]
  exact h.comp he

/-- **Compactness for a basis indexed by any countable type.**  A multiplier vanishing along the
cofinite filter gives a compact operator on a space with a Hilbert basis indexed by `ι`. -/
theorem isCompactOperator_basisMultiplierOperator_reindex (b : HilbertBasis ι ℂ E) (e : ℕ ≃ ι)
    (lam : ι → ℂ) {C : ℝ} (hC : ∀ n : ℕ, ‖lam (e n)‖ ≤ C)
    (hlim : Filter.Tendsto (fun i => ‖lam i‖) Filter.cofinite (𝓝 0)) :
    IsCompactOperator
      (basisMultiplierOperator (hilbertBasisReindex b e) (fun n => lam (e n)) hC) :=
  isCompactOperator_basisMultiplierOperator _ _ hC
    (tendsto_reindex_atTop_of_tendsto_cofinite e hlim)

/-- The original basis vectors remain eigenvectors after reindexing. -/
theorem basisMultiplierOperator_reindex_apply_basis (b : HilbertBasis ι ℂ E) (e : ℕ ≃ ι)
    (lam : ι → ℂ) {C : ℝ} (hC : ∀ n : ℕ, ‖lam (e n)‖ ≤ C) (n : ℕ) :
    basisMultiplierOperator (hilbertBasisReindex b e) (fun n => lam (e n)) hC (b (e n))
      = lam (e n) • b (e n) := by
  have h := basisMultiplierOperator_apply_basis (hilbertBasisReindex b e)
    (fun n => lam (e n)) hC n
  rwa [hilbertBasisReindex_apply] at h

end Reindex

end GaloisForLFunctions.RHTower
