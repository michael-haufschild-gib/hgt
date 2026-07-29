import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The canonical Hilbert sampling defect

For a bounded sampling operator `S : H → Y` and a Riesz representer `h : H`, the information
invisible to sampling is the orthogonal projection of `h` onto `ker S`.  Its norm is the canonical
Hilbert defect.  This file proves the exact upper bound on every sample-invisible test and exhibits
the projected representer as the sharp witness.

The vanishing criterion is the unconditional identity
`defect = 0 ↔ h ∈ closure (range S†)`.  This file deliberately introduces no predicate standing
in for the stronger, source-specific assertion `h ∈ range S†`; that assertion is not formalized
until it is proved for the actual sampling operator.
-/

open scoped ComplexConjugate

noncomputable section

namespace RHTower

variable {𝕜 H Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- The component of a Riesz representer lying in the kernel of the sampling operator. -/
def hilbertSamplingInvisiblePart (S : H →L[𝕜] Y) (h : H) : H :=
  S.ker.orthogonalProjection h

/-- The norm of the sampling-invisible component of a Riesz representer. -/
def hilbertSamplingDefect (S : H →L[𝕜] Y) (h : H) : ℝ :=
  ‖S.ker.orthogonalProjection h‖

/-- Zero Hilbert defect is exactly membership in the closure of the adjoint range. -/
theorem hilbertSamplingDefect_eq_zero_iff [CompleteSpace Y]
    (S : H →L[𝕜] Y) (h : H) :
    hilbertSamplingDefect S h = 0 ↔
      h ∈ (ContinuousLinearMap.adjoint S).range.topologicalClosure := by
  rw [hilbertSamplingDefect, norm_eq_zero]
  rw [Submodule.orthogonalProjectionOntoOnto_eq_zero_iff]
  rw [S.orthogonal_ker]

/-- The canonical invisible component really is killed by the sampling operator. -/
theorem hilbertSamplingInvisiblePart_mem_ker
    (S : H →L[𝕜] Y) (h : H) :
    hilbertSamplingInvisiblePart S h ∈ S.ker := by
  exact (S.ker.orthogonalProjection h).property

/-- Every sample-invisible test pairs with the representer by at most its norm times the canonical
Hilbert defect. -/
theorem norm_inner_le_norm_mul_hilbertSamplingDefect
    (S : H →L[𝕜] Y) (h x : H) (hx : S x = 0) :
    ‖inner 𝕜 x h‖ ≤ ‖x‖ * hilbertSamplingDefect S h := by
  let u : S.ker := ⟨x, hx⟩
  have hinner : inner 𝕜 u (S.ker.orthogonalProjection h) = inner 𝕜 x h :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left u h
  rw [← hinner]
  exact norm_inner_le_norm u (S.ker.orthogonalProjection h)

/-- The invisible component attains the squared defect, certifying sharpness without a supremum
construction. -/
theorem norm_inner_invisiblePart_eq_defect_sq
    (S : H →L[𝕜] Y) (h : H) :
    ‖inner 𝕜 (hilbertSamplingInvisiblePart S h) h‖ =
      hilbertSamplingDefect S h ^ 2 := by
  let u : S.ker := S.ker.orthogonalProjection h
  have hinner : inner 𝕜 u (S.ker.orthogonalProjection h) =
      inner 𝕜 (hilbertSamplingInvisiblePart S h) h := by
    simp [u, hilbertSamplingInvisiblePart]
  calc
    ‖inner 𝕜 (hilbertSamplingInvisiblePart S h) h‖ =
        ‖inner 𝕜 u (S.ker.orthogonalProjection h)‖ := congrArg norm hinner.symm
    _ = ‖inner 𝕜 u u‖ := by rfl
    _ = ‖u‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; simp
    _ = hilbertSamplingDefect S h ^ 2 := by rfl

/-- Injective sampling has no invisible Hilbert component.  This does not assert closed range or a
bounded inverse. -/
theorem hilbertSamplingDefect_eq_zero_of_injective
    (S : H →L[𝕜] Y) (hS : Function.Injective S) (h : H) :
    hilbertSamplingDefect S h = 0 := by
  have hker : S.ker = ⊥ := LinearMap.ker_eq_bot.mpr hS
  simp [hilbertSamplingDefect, hker]

end RHTower
