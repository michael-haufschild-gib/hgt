import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram

/-!
# Minimal representatives of a trace fibre

Orthogonal removal of the trace kernel preserves every output and gives the
unique representative of least norm. The exact norm excess is the squared
norm of the discarded component. This is the Hilbert-space mechanism of
Corollary 9.30 of Du, *Arithmetic theta products and doubling at arbitrary level*,
applied to the cross-Gram maps.
-/

noncomputable section
open scoped InnerProductSpace

namespace HilbertMetric.NomologicalCrossGram

variable {𝕜 D W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 D]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- The representative obtained by removing the component invisible to `T`. -/
def activeRepresentative (T : D →L[𝕜] W) : D →L[𝕜] D :=
  T.kerᗮ.starProjection

theorem activeRepresentative_eq (T : D →L[𝕜] W) (x : D) :
    activeRepresentative T x = x - T.ker.starProjection x :=
  T.ker.starProjection_orthogonal_val x

/-- Removing the kernel component preserves the actual output. -/
theorem map_activeRepresentative (T : D →L[𝕜] W) (x : D) :
    T (activeRepresentative T x) = T x := by
  rw [activeRepresentative_eq, map_sub,
    show T (T.ker.starProjection x) = 0 from T.ker.starProjection_apply_mem x,
    sub_zero]

/-- Two inputs have the same trace exactly when their active representatives agree. -/
theorem activeRepresentative_eq_iff (T : D →L[𝕜] W) (x y : D) :
    activeRepresentative T x = activeRepresentative T y ↔ T x = T y := by
  constructor
  · intro h
    simpa only [map_activeRepresentative] using congrArg T h
  · intro h
    have hk : x - y ∈ T.ker := by
      change T (x - y) = 0
      rw [map_sub, h, sub_self]
    have hp : activeRepresentative T (x - y) = 0 := by
      change x - y ∈ T.kerᗮ.starProjection.ker
      rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
      exact hk
    simpa only [map_sub, sub_eq_zero] using hp

/-- Exact Pythagorean cost of the part discarded by the trace quotient. -/
theorem activeRepresentative_norm_split (T : D →L[𝕜] W) (x : D) :
    ‖x‖ ^ 2 = ‖activeRepresentative T x‖ ^ 2 +
      ‖x - activeRepresentative T x‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x T.kerᗮ
  rw [T.kerᗮ.starProjection_orthogonal_val x] at h
  exact h

/-- The complete fibre has a unique norm-minimizing representative. -/
theorem activeRepresentative_unique_minimizer (T : D →L[𝕜] W) (x : D) :
    ∃! y : D, T y = T x ∧ ∀ z : D, T z = T x → ‖y‖ ≤ ‖z‖ := by
  have hle (z : D) : ‖activeRepresentative T z‖ ≤ ‖z‖ := by
    have hs := activeRepresentative_norm_split T z
    nlinarith only [hs, sq_nonneg ‖z - activeRepresentative T z‖,
      norm_nonneg (activeRepresentative T z), norm_nonneg z]
  refine ⟨activeRepresentative T x, ⟨map_activeRepresentative T x, ?_⟩, ?_⟩
  · intro z hz
    rw [(activeRepresentative_eq_iff T x z).mpr hz.symm]
    exact hle z
  · rintro y ⟨hy, hmin⟩
    have ha := (activeRepresentative_eq_iff T y x).mpr hy
    have hb := hmin (activeRepresentative T x) (map_activeRepresentative T x)
    have hs := activeRepresentative_norm_split T y
    rw [ha] at hs
    have hz : ‖y - activeRepresentative T x‖ = 0 := by
      nlinarith only [hs, sq_nonneg ‖y - activeRepresentative T x‖,
        norm_nonneg y, norm_nonneg (activeRepresentative T x),
        norm_nonneg (y - activeRepresentative T x), hb]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

#print axioms map_activeRepresentative
#print axioms activeRepresentative_eq_iff
#print axioms activeRepresentative_norm_split
#print axioms activeRepresentative_unique_minimizer

end HilbertMetric.NomologicalCrossGram
