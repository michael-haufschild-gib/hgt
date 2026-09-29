import Mathlib

/-!
# Hilbert eigenbasis of an injective compact self-adjoint operator

For a compact operator `T` on a complex Hilbert space the nonzero eigenspaces are
finite-dimensional.  Choosing an orthonormal basis of each and collecting them gives an
orthonormal family; when `T` is symmetric and injective its closed span is everything, by the
spectral theorem `orthogonalComplement_iSup_eigenspaces_eq_bot`.  The result is a `HilbertBasis`
indexed by pairs (nonzero eigenvalue, basis index) whose vectors are eigenvectors with real
eigenvalues.
-/

open Module End Submodule

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The nonzero eigenspaces of a compact operator. -/
abbrev nonzeroEigenspace (T : E →L[ℂ] E) (μ : {μ : ℂ // μ ≠ 0}) : Submodule ℂ E :=
  eigenspace (T : E →ₗ[ℂ] E) μ.1

instance nonzeroEigenspace_finiteDimensional {T : E →L[ℂ] E} [hT : Fact (IsCompactOperator T)]
    (μ : {μ : ℂ // μ ≠ 0}) : FiniteDimensional ℂ (nonzeroEigenspace T μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hT.out μ.1 μ.2

/-- Index set of the eigenbasis: a nonzero eigenvalue and an index into an orthonormal basis of its
eigenspace. -/
abbrev EigenIndex (T : E →L[ℂ] E) [Fact (IsCompactOperator T)] : Type _ :=
  Σ μ : {μ : ℂ // μ ≠ 0}, Fin (Module.finrank ℂ (nonzeroEigenspace T μ))

/-- The eigenvectors: orthonormal bases of the nonzero eigenspaces, collected. -/
def eigenVec (T : E →L[ℂ] E) [Fact (IsCompactOperator T)] (i : EigenIndex T) : E :=
  (stdOrthonormalBasis ℂ (nonzeroEigenspace T i.1) i.2 : E)

theorem eigenVec_mem (T : E →L[ℂ] E) [Fact (IsCompactOperator T)] (i : EigenIndex T) :
    eigenVec T i ∈ nonzeroEigenspace T i.1 :=
  (stdOrthonormalBasis ℂ (nonzeroEigenspace T i.1) i.2).2

theorem apply_eigenVec (T : E →L[ℂ] E) [Fact (IsCompactOperator T)] (i : EigenIndex T) :
    T (eigenVec T i) = i.1.1 • eigenVec T i :=
  mem_eigenspace_iff.1 (eigenVec_mem T i)

theorem orthonormal_eigenVec {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (hsym : (T : E →ₗ[ℂ] E).IsSymmetric) : Orthonormal ℂ (eigenVec T) := by
  have hfam : OrthogonalFamily ℂ (fun μ : {μ : ℂ // μ ≠ 0} => nonzeroEigenspace T μ)
      (fun μ => (nonzeroEigenspace T μ).subtypeₗᵢ) :=
    hsym.orthogonalFamily_eigenspaces.comp Subtype.val_injective
  exact hfam.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℂ (nonzeroEigenspace T μ)).orthonormal)

theorem mem_span_eigenVec {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (μ : {μ : ℂ // μ ≠ 0}) (x : E) (hx : x ∈ nonzeroEigenspace T μ) :
    x ∈ span ℂ (Set.range (eigenVec T)) := by
  have hsum := (stdOrthonormalBasis ℂ (nonzeroEigenspace T μ)).sum_repr ⟨x, hx⟩
  have hx' : x = ∑ k, ((stdOrthonormalBasis ℂ (nonzeroEigenspace T μ)).repr ⟨x, hx⟩ k) •
      ((stdOrthonormalBasis ℂ (nonzeroEigenspace T μ) k : nonzeroEigenspace T μ) : E) := by
    have := congrArg (fun y : nonzeroEigenspace T μ => (y : E)) hsum
    simpa using this.symm
  rw [hx']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨⟨μ, k⟩, rfl⟩)

theorem eigenspace_le_span_eigenVec {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (hker : ∀ v, T v = 0 → v = 0) (μ : ℂ) :
    eigenspace (T : E →ₗ[ℂ] E) μ ≤ span ℂ (Set.range (eigenVec T)) := by
  by_cases hμ : μ = 0
  · subst hμ
    intro x hx
    have : x = 0 := hker x (by simpa [mem_eigenspace_iff] using hx)
    simp [this]
  · exact fun x hx => mem_span_eigenVec ⟨μ, hμ⟩ x hx

/-- **Spectral theorem for injective compact self-adjoint operators**: the collected eigenvectors of
the nonzero eigenvalues form a Hilbert basis. -/
def eigenHilbertBasis {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (hsym : (T : E →ₗ[ℂ] E).IsSymmetric) (hker : ∀ v, T v = 0 → v = 0) :
    HilbertBasis (EigenIndex T) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eigenVec hsym) (by
    have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      (Fact.out : IsCompactOperator T) hsym
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← hbot]
    exact Submodule.orthogonal_le (iSup_le fun μ => eigenspace_le_span_eigenVec hker μ) hx)

theorem eigenHilbertBasis_apply {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (hsym : (T : E →ₗ[ℂ] E).IsSymmetric) (hker : ∀ v, T v = 0 → v = 0) (i : EigenIndex T) :
    (eigenHilbertBasis hsym hker i : E) = eigenVec T i := by
  unfold eigenHilbertBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The eigenvalues of a symmetric operator are real. -/
theorem eigenValue_real {T : E →L[ℂ] E} [Fact (IsCompactOperator T)]
    (hsym : (T : E →ₗ[ℂ] E).IsSymmetric) (i : EigenIndex T) :
    ((i.1.1.re : ℝ) : ℂ) = i.1.1 := by
  have hne : eigenVec T i ≠ 0 := (orthonormal_eigenVec hsym).ne_zero i
  have hev : HasEigenvalue (T : E →ₗ[ℂ] E) i.1.1 :=
    hasEigenvalue_of_hasEigenvector ⟨eigenVec_mem T i, hne⟩
  have hc := hsym.conj_eigenvalue_eq_self hev
  exact (Complex.conj_eq_iff_re.1 hc)

end

end GaloisForLFunctions.HTGeometry
