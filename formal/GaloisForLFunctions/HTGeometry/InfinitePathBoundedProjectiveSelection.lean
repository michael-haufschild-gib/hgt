import GaloisForLFunctions.HTGeometry.BoundedAmbientRestrictedGenericSelection
import GaloisForLFunctions.HTGeometry.PathShellProjectiveGenericity

/-!
# One bounded infinite path field with projective-generic finite prefixes

The explicit onsite-plus-edge Pauli coordinates of every finite open path embed compatibly into one
countable path-label type.  Applying bounded residual selection produces one coefficient field,
arbitrarily close coordinatewise to any prescribed background, whose every path prefix of at least
three qubits has maximally projective generic chain coefficients.

Unlike a per-size genericity theorem, no finite prefix reselects its coefficients.
-/

open Set Topology MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Three onsite Pauli coordinates per site and nine Pauli-pair coordinates per bond on the
countable open path. -/
abbrev InfinitePathLabel :=
  (ℕ × Fin 3) ⊕ (ℕ × (Fin 3 × Fin 3))

/-- Literal inclusion of the `(k+3)`-qubit path labels into the countable path labels. -/
def pathLabelToInfinite (k : ℕ) : PathLabel (k + 1) → InfinitePathLabel
  | Sum.inl sq => Sum.inl (sq.1.val, sq.2)
  | Sum.inr eab => Sum.inr (eab.1.val, eab.2)

theorem pathLabelToInfinite_injective (k : ℕ) :
    Function.Injective (pathLabelToInfinite k) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          simp only [pathLabelToInfinite, Sum.inl.injEq, Prod.mk.injEq] at h
          exact congrArg Sum.inl (Prod.ext (Fin.ext h.1) h.2)
      | inr b => simp [pathLabelToInfinite] at h
  | inr a =>
      cases b with
      | inl b => simp [pathLabelToInfinite] at h
      | inr b =>
          simp only [pathLabelToInfinite, Sum.inr.injEq, Prod.mk.injEq] at h
          exact congrArg Sum.inr (Prod.ext (Fin.ext h.1) h.2)

/-- Numbered chain coordinates included into the single countable path field. -/
def numberedPathToInfinite (k : ℕ) :
    Fin (Fintype.card (ChainLabel (k + 3))) → InfinitePathLabel :=
  fun i => pathLabelToInfinite k (pathCoeffEquiv (k + 1) i)

theorem numberedPathToInfinite_injective (k : ℕ) :
    Function.Injective (numberedPathToInfinite k) :=
  (pathLabelToInfinite_injective k).comp (pathCoeffEquiv (k + 1)).injective

/-- Projective-generic coefficient locus for the numbered `(k+3)`-qubit path family. -/
def chainProjectiveGood (k : ℕ) :
    Set (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) :=
  polynomialMatrixProjectiveGenericSet
    (spectralGenericMatrix (chainPauliFin (k + 3)))

theorem chainProjectiveGood_residual (k : ℕ) :
    chainProjectiveGood k ∈
      residual (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ) := by
  obtain ⟨theta0, htheta0⟩ := exists_chainShell_maximallyProjective_witness k
  exact (polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (spectralGenericMatrix (chainPauliFin (k + 3))) theta0
    (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3)) theta0).eigenvalues
    htheta0 htheta0.injective (fun i => by
      show (Matrix.scalar _ (((isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) theta0).eigenvalues i : ℝ) : ℂ)
          - (spectralGenericMatrix (chainPauliFin (k + 3))).map
            (MvPolynomial.eval₂Hom (RingHom.id ℂ)
              (fun t => ((theta0 t : ℝ) : ℂ)))).det = 0
      rw [map_spectralGenericMatrix_eq theta0]
      exact charpolyRelation_eigenvalues
        (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) theta0) i)).2.1

/-- **One-field all-prefix projective selection law.**  One countable coefficient field lies
inside every prescribed coordinate box and is projective-generic on every literal finite prefix. -/
theorem exists_bounded_infinitePath_allPrefixes_projective
    (center radius : InfinitePathLabel → ℝ)
    (hradius : ∀ i, 0 < radius i) :
    ∃ p : InfinitePathLabel → ℝ,
      (∀ i, |p i - center i| < radius i) ∧
      ∀ k, coefficientRestrict (numberedPathToInfinite k) p ∈ chainProjectiveGood k := by
  exact exists_bounded_ambientRestrictedGood chainProjectiveGood numberedPathToInfinite
    numberedPathToInfinite_injective center radius hradius chainProjectiveGood_residual

end

end GaloisForLFunctions.HTGeometry
