import GaloisForLFunctions.HTGeometry.SiteSupportedLocalHamiltonian
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity

/-!
# Spectrum of a site-supported operator

An operator supported on a site packet acts as the identity on the spectator
factors, so its spectrum is exactly the spectrum of its local block, each
eigenvalue repeated once per spectator configuration.  Rational gap geometry
only sees the *set* of eigenvalues, so a lifted operator and its block have the
same anchored gap module and the same temporal rank.

The proof is determinantal: reindexing configurations into inside/outside
coordinates turns the lift into `B ⊗ I`, and the determinant of a Kronecker
product with an identity factor is a power of the determinant of the block.
-/

open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real number is an eigenvalue of a Hermitian matrix exactly when it is a
root of the characteristic relation. -/
theorem mem_range_hermitianEigenvalues_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {M : Matrix I I ℂ} (hM : M.IsHermitian) (μ : ℝ) :
    μ ∈ Set.range hM.eigenvalues ↔ (Matrix.scalar I (μ : ℂ) - M).det = 0 := by
  rw [← Matrix.eval_charpoly, hM.charpoly_eq, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ i, by simp⟩
  · rintro ⟨i, -, hi⟩
    exact ⟨i, Complex.ofReal_inj.mp (sub_eq_zero.mp hi).symm⟩

/-- The anchored gap module only sees the set of energies. -/
theorem anchoredGapSubspace_eq_of_range_eq
    {I J : Type*} [Fintype I] [Fintype J]
    {e₁ : I → ℝ} {e₂ : J → ℝ} (hrange : Set.range e₁ = Set.range e₂)
    (r₁ : I) (r₂ : J) (hr : e₁ r₁ = e₂ r₂) :
    anchoredGapSubspace e₁ r₁ = anchoredGapSubspace e₂ r₂ := by
  unfold anchoredGapSubspace
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ : e₁ i ∈ Set.range e₂ := by
      rw [← hrange]; exact ⟨i, rfl⟩
    exact ⟨j, by rw [hj, hr]⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ : e₂ j ∈ Set.range e₁ := by
      rw [hrange]; exact ⟨j, rfl⟩
    exact ⟨i, by rw [hi, hr]⟩

theorem anchoredTemporalRank_eq_of_range_eq
    {I J : Type*} [Fintype I] [Fintype J]
    {e₁ : I → ℝ} {e₂ : J → ℝ} (hrange : Set.range e₁ = Set.range e₂)
    (r₁ : I) (r₂ : J) (hr : e₁ r₁ = e₂ r₂) :
    anchoredTemporalRank e₁ r₁ = anchoredTemporalRank e₂ r₂ := by
  unfold anchoredTemporalRank
  rw [anchoredGapSubspace_eq_of_range_eq hrange r₁ r₂ hr]

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

theorem conjTranspose_liftLocalMatrix (S : Finset V)
    (B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) :
    (liftLocalMatrix S B)ᴴ = liftLocalMatrix S Bᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, liftLocalMatrix]
  by_cases h : restrictOutsideConfiguration S x = restrictOutsideConfiguration S y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem isHermitian_liftLocalMatrix (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : B.IsHermitian) : (liftLocalMatrix S B).IsHermitian := by
  show (liftLocalMatrix S B)ᴴ = _
  rw [conjTranspose_liftLocalMatrix, hB]

/-- Reindexing into inside/outside coordinates turns a shifted lift into a
Kronecker product with an identity spectator factor. -/
theorem reindex_scalarSub_liftLocalMatrix (S : Finset V)
    (B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) (μ : ℂ) :
    Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
        (Matrix.scalar (∀ v, A v) μ - liftLocalMatrix S B) =
      (Matrix.scalar (LocalConfiguration A S) μ - B) ⊗ₖ
        (1 : Matrix (OutsideConfiguration A S)
          (OutsideConfiguration A S) ℂ) := by
  classical
  have hsplit :
      Matrix.reindex (configurationSplitEquiv A S) (configurationSplitEquiv A S)
          (Matrix.scalar (∀ v, A v) μ - liftLocalMatrix S B) =
        Matrix.reindex (configurationSplitEquiv A S)
            (configurationSplitEquiv A S) (Matrix.scalar (∀ v, A v) μ) -
          Matrix.reindex (configurationSplitEquiv A S)
            (configurationSplitEquiv A S) (liftLocalMatrix S B) := rfl
  rw [hsplit, reindex_liftLocalMatrix_eq_kronecker_one]
  ext x y
  have hscalar :
      Matrix.reindex (configurationSplitEquiv A S)
          (configurationSplitEquiv A S) (Matrix.scalar (∀ v, A v) μ) x y =
        if x = y then μ else 0 := by
    show Matrix.scalar (∀ v, A v) μ
        ((configurationSplitEquiv A S).symm x)
        ((configurationSplitEquiv A S).symm y) = _
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply,
      (configurationSplitEquiv A S).symm.injective.eq_iff]
  rw [Matrix.sub_apply, hscalar]
  by_cases h₂ : x.2 = y.2
  · by_cases h₁ : x.1 = y.1 <;>
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.sub_apply,
        Matrix.scalar_apply, h₁, h₂, Prod.ext_iff]
  · simp [Matrix.kroneckerMap_apply, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, h₂, Prod.ext_iff]

/-- **The spectrum of a lift is the spectrum of its block.** -/
theorem range_eigenvalues_liftLocalMatrix [∀ v, Nonempty (A v)] (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : B.IsHermitian) :
    Set.range (isHermitian_liftLocalMatrix S hB).eigenvalues =
      Set.range hB.eigenvalues := by
  classical
  have hcard : Fintype.card (OutsideConfiguration A S) ≠ 0 :=
    Fintype.card_ne_zero
  ext μ
  rw [mem_range_hermitianEigenvalues_iff, mem_range_hermitianEigenvalues_iff]
  have hdet :
      (Matrix.scalar (∀ v, A v) (μ : ℂ) - liftLocalMatrix S B).det =
        ((Matrix.scalar (LocalConfiguration A S) (μ : ℂ) - B).det) ^
          Fintype.card (OutsideConfiguration A S) := by
    rw [← Matrix.det_submatrix_equiv_self
      (configurationSplitEquiv A S).symm
      (Matrix.scalar (∀ v, A v) (μ : ℂ) - liftLocalMatrix S B)]
    rw [show (Matrix.scalar (∀ v, A v) (μ : ℂ) -
          liftLocalMatrix S B).submatrix
            (⇑(configurationSplitEquiv A S).symm)
            (⇑(configurationSplitEquiv A S).symm) =
        Matrix.reindex (configurationSplitEquiv A S)
          (configurationSplitEquiv A S)
          (Matrix.scalar (∀ v, A v) (μ : ℂ) - liftLocalMatrix S B) from rfl]
    rw [reindex_scalarSub_liftLocalMatrix, Matrix.det_kronecker, Matrix.det_one,
      one_pow, mul_one]
  rw [hdet, pow_eq_zero_iff hcard]

/-- **Lifting preserves temporal rank.**  A site-supported operator and its
local block have the same anchored gap module, hence the same rational
temporal rank. -/
theorem anchoredTemporalRank_liftLocalMatrix [∀ v, Nonempty (A v)]
    (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : B.IsHermitian)
    (r : ∀ v, A v) (r' : LocalConfiguration A S)
    (hr : (isHermitian_liftLocalMatrix S hB).eigenvalues r =
      hB.eigenvalues r') :
    anchoredTemporalRank (isHermitian_liftLocalMatrix S hB).eigenvalues r =
      anchoredTemporalRank hB.eigenvalues r' :=
  anchoredTemporalRank_eq_of_range_eq
    (range_eigenvalues_liftLocalMatrix S hB) r r' hr

/-- Every reference level of a lift is matched by a reference level of its
block. -/
theorem exists_reference_eigenvalues_liftLocalMatrix [∀ v, Nonempty (A v)]
    (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : B.IsHermitian) (r : ∀ v, A v) :
    ∃ r' : LocalConfiguration A S,
      (isHermitian_liftLocalMatrix S hB).eigenvalues r =
        hB.eigenvalues r' := by
  have hmem : (isHermitian_liftLocalMatrix S hB).eigenvalues r ∈
      Set.range hB.eigenvalues := by
    rw [← range_eigenvalues_liftLocalMatrix S hB]
    exact ⟨r, rfl⟩
  obtain ⟨r', hr'⟩ := hmem
  exact ⟨r', hr'.symm⟩

end

end GaloisForLFunctions.HTGeometry
