import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram
import GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital

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
open GaloisForLFunctions.HTGeometry

namespace HilbertMetric.NomologicalCrossGram

variable {𝕜 D W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 D]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

local instance : CompleteSpace D := FiniteDimensional.complete 𝕜 D

/-- Two inputs have the same trace exactly when their active representatives agree. -/
theorem coimageProjection_eq_iff (T : D →L[𝕜] W) (x y : D) :
    coimageProjection T x = coimageProjection T y ↔ T x = T y := by
  constructor
  · intro h
    simpa only [comp_coimageProjection] using congrArg T h
  · intro h
    have hk : x - y ∈ T.ker := by
      change T (x - y) = 0
      rw [map_sub, h, sub_self]
    have hp : coimageProjection T (x - y) = 0 := by
      change x - y ∈ T.kerᗮ.starProjection.ker
      rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
      exact hk
    simpa only [map_sub, sub_eq_zero] using hp

/-- Exact Pythagorean cost of the part discarded by the trace quotient. -/
theorem coimageProjection_norm_split (T : D →L[𝕜] W) (x : D) :
    ‖x‖ ^ 2 = ‖coimageProjection T x‖ ^ 2 +
      ‖x - coimageProjection T x‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x T.kerᗮ
  rw [T.kerᗮ.starProjection_orthogonal_val x] at h
  exact h

/-- The complete fibre has a unique norm-minimizing representative. -/
theorem coimageProjection_unique_minimizer (T : D →L[𝕜] W) (x : D) :
    ∃! y : D, T y = T x ∧ ∀ z : D, T z = T x → ‖y‖ ≤ ‖z‖ := by
  refine ⟨coimageProjection T x, ⟨comp_coimageProjection T x, ?_⟩, ?_⟩
  · intro z hz
    rw [(coimageProjection_eq_iff T x z).mpr hz.symm]
    exact norm_coimageProjection_le T z
  · rintro y ⟨hy, hmin⟩
    have ha := (coimageProjection_eq_iff T y x).mpr hy
    have hb := hmin (coimageProjection T x) (comp_coimageProjection T x)
    have hs := coimageProjection_norm_split T y
    rw [ha] at hs
    have hz : ‖y - coimageProjection T x‖ = 0 := by
      nlinarith only [hs, sq_nonneg ‖y - coimageProjection T x‖,
        norm_nonneg y, norm_nonneg (coimageProjection T x),
        norm_nonneg (y - coimageProjection T x), hb]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Passing from a map to its Gram loses no information about minimal source representatives. -/
theorem coimageProjection_gram [FiniteDimensional 𝕜 W] (T : D →L[𝕜] W) :
    coimageProjection (gram T) = coimageProjection T := by
  simp only [coimageProjection, ker_gram]

#print axioms coimageProjection_eq_iff
#print axioms coimageProjection_norm_split
#print axioms coimageProjection_unique_minimizer
#print axioms coimageProjection_gram

end HilbertMetric.NomologicalCrossGram
