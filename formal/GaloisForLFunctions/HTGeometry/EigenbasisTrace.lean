import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# The diagonal of an operator in an eigenbasis is its eigenvalue list

The operator trace is the diagonal sum `∑ᵢ ⟨eᵢ, T eᵢ⟩` over a Hilbert basis.  When the basis
consists of eigenvectors, each diagonal entry is the corresponding eigenvalue, so the diagonal sum
is literally the sum of the eigenvalues repeated with their multiplicities.

This is the shape of the trace formula for a smoothed flow: the eigenvalues of the smoothing are
the values of the weight's transform at the spectral points, and the multiplicity of a spectral
point is the number of basis vectors carrying it.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A diagonal entry against an eigenvector is the eigenvalue. -/
theorem inner_diag_eq_eigenvalue {T : E →L[𝕜] E} {ι : Type*} {b : ι → E}
    (hb : Orthonormal 𝕜 b) {mu : ι → 𝕜} (heig : ∀ i, T (b i) = mu i • b i) (i : ι) :
    inner 𝕜 (b i) (T (b i)) = mu i := by
  have hself : inner 𝕜 (b i) (b i) = (1 : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, hb.1 i]
    norm_num
  rw [heig i, inner_smul_right, hself, mul_one]

/-- **The diagonal sum in an eigenbasis is the sum of the eigenvalues.** -/
theorem tsum_inner_diag_eq_tsum_eigenvalues {T : E →L[𝕜] E} {ι : Type*} {b : ι → E}
    (hb : Orthonormal 𝕜 b) {mu : ι → 𝕜} (heig : ∀ i, T (b i) = mu i • b i) :
    (∑' i, inner 𝕜 (b i) (T (b i))) = ∑' i, mu i :=
  tsum_congr (inner_diag_eq_eigenvalue hb heig)

/-- Specialization to the canonical Hilbert basis used by `opTrace`: if that basis diagonalizes
`T`, the operator trace is the sum of the eigenvalues. -/
theorem opTrace_eq_tsum_eigenvalues [CompleteSpace E] {T : E →L[𝕜] E} {mu : _ → 𝕜}
    (heig : ∀ i, T (hsBasis 𝕜 E i) = mu i • hsBasis 𝕜 E i) :
    opTrace T = ∑' i, mu i := by
  rw [opTrace]
  exact tsum_inner_diag_eq_tsum_eigenvalues (hsBasis 𝕜 E).orthonormal heig

end GaloisForLFunctions.HTGeometry
