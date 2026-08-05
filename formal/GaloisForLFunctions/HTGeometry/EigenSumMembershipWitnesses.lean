import GaloisForLFunctions.HTGeometry.HermitianDegenerationFlag

/-!
# The high eigen-sum is inhabited

The degeneration flag is cut out by membership in the span of the eigenspaces above a threshold.
The corpus already proves that each eigenspace above the threshold is *contained* in the sum; what
the flag arguments consume is the membership form of that containment, together with the zero
vector.  This is the recorded different-head gap: an inclusion produces no membership key.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →ₗ[ℂ] E}

/-- The zero vector lies in every high eigen-sum. -/
theorem zero_mem_eigenSum (T : E →ₗ[ℂ] E) (c : ℝ) : (0 : E) ∈ eigenSum T c :=
  Submodule.zero_mem _

/-- Hence every eigenvector above the threshold lies in the high eigen-sum. -/
theorem mem_eigenSum_of_mem_eigenspace {c μ : ℝ} (hμ : c < μ) {x : E}
    (hx : x ∈ Module.End.eigenspace T (μ : ℂ)) : x ∈ eigenSum T c :=
  eigenspace_le_eigenSum hμ hx

end GaloisForLFunctions.HTGeometry
