import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The canonical Hilbert sampling defect

For a bounded sampling operator `S : H → Y` and a Riesz representer `h : H`, the information
invisible to sampling is the orthogonal projection of `h` onto `ker S`.  Its norm is the canonical
Hilbert defect.  This file proves the exact upper bound on every sample-invisible test and exhibits
the projected representer as the sharp witness.

The vanishing criterion separates the two range questions needed by the prime-log route:

* zero defect means `h ∈ closure (range S†)`;
* bounded coefficient reconstruction means `h ∈ range S†` itself.

Thus injective sampling kills the defect but does not, without a closed-range theorem, produce a
bounded reconstruction formula.
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

/-- A bounded coefficient reconstruction exists when the representer belongs to the actual range
of the adjoint sampling operator, not merely to its closure. -/
def HasBoundedSamplingReconstruction [CompleteSpace Y]
    (S : H →L[𝕜] Y) (h : H) : Prop :=
  h ∈ (ContinuousLinearMap.adjoint S).range

theorem hasBoundedSamplingReconstruction_iff_exists [CompleteSpace Y]
    (S : H →L[𝕜] Y) (h : H) :
    HasBoundedSamplingReconstruction S h ↔
      ∃ c : Y, ContinuousLinearMap.adjoint S c = h := by
  rfl

/-- Zero Hilbert defect is exactly membership in the closure of the adjoint range. -/
theorem hilbertSamplingDefect_eq_zero_iff [CompleteSpace Y]
    (S : H →L[𝕜] Y) (h : H) :
    hilbertSamplingDefect S h = 0 ↔
      h ∈ (ContinuousLinearMap.adjoint S).range.topologicalClosure := by
  rw [hilbertSamplingDefect, norm_eq_zero]
  rw [Submodule.orthogonalProjection_eq_zero_iff]
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
    Submodule.inner_orthogonalProjection_eq_of_mem_left u h
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

/-- Actual adjoint-range membership always forces zero defect. -/
theorem HasBoundedSamplingReconstruction.defect_eq_zero [CompleteSpace Y]
    {S : H →L[𝕜] Y} {h : H} (hrange : HasBoundedSamplingReconstruction S h) :
    hilbertSamplingDefect S h = 0 := by
  rw [hilbertSamplingDefect_eq_zero_iff]
  exact Submodule.le_topologicalClosure _ hrange

/-- Injective sampling has no invisible Hilbert component.  This does not assert closed range or a
bounded inverse. -/
theorem hilbertSamplingDefect_eq_zero_of_injective
    (S : H →L[𝕜] Y) (hS : Function.Injective S) (h : H) :
    hilbertSamplingDefect S h = 0 := by
  have hker : S.ker = ⊥ := LinearMap.ker_eq_bot.mpr hS
  simp [hilbertSamplingDefect, hker]

/-- If the adjoint range is closed, zero defect upgrades to an actual bounded coefficient
reconstruction. -/
theorem hilbertSamplingDefect_eq_zero_iff_of_isClosed_adjoint_range [CompleteSpace Y]
    (S : H →L[𝕜] Y) (h : H)
    (hclosed : IsClosed ((ContinuousLinearMap.adjoint S).range : Set H)) :
    hilbertSamplingDefect S h = 0 ↔ HasBoundedSamplingReconstruction S h := by
  rw [hilbertSamplingDefect_eq_zero_iff, HasBoundedSamplingReconstruction]
  rw [hclosed.submodule_topologicalClosure_eq]

end RHTower
