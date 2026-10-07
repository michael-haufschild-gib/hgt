import GaloisForLFunctions.HTGeometry.HilbertSphereExtension
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Complex linearity detected on the unit sphere

A Hilbert sphere isometry has a complex-linear isometric extension exactly when
it commutes with multiplication by `I`. Equivalently, it preserves the full
complex Gram kernel. This refines the real-linear sphere extension when used
with the corpus's complex observation and evaluation geometry.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

local instance : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
local instance : InnerProductSpace ℝ F := InnerProductSpace.complexToReal

/-- Multiplication by `I`, regarded as a map of the unit sphere. -/
def complexSphereQuarterTurn (u : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨Complex.I • (u : E), by
    simpa only [mem_sphere, dist_zero_right, norm_smul, Complex.norm_I, one_mul]
      using u.property⟩

@[simp] theorem complexSphereQuarterTurn_coe (u : sphere (0 : E) 1) :
    (complexSphereQuarterTurn u : E) = Complex.I • (u : E) := rfl

/-- Quarter-turn compatibility of the boundary map is exactly complex linear extendability. -/
theorem hilbertSphereIsometry_complex_extension_iff
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    (∃ T : E ≃ₗᵢ[ℂ] F, ∀ u : sphere (0 : E) 1, T (u : E) = (f u : F)) ↔
      ∀ u : sphere (0 : E) 1,
        (f (complexSphereQuarterTurn u) : F) = Complex.I • (f u : F) := by
  constructor
  · rintro ⟨T, hT⟩ u
    rw [← hT, complexSphereQuarterTurn_coe, map_smul, hT]
  · intro h
    let T := hilbertSphereExtension f
    have hI (x : E) : T (Complex.I • x) = Complex.I • T x := by
      by_cases hx : x = 0
      · simp [hx]
      let u : sphere (0 : E) 1 := ⟨NormedSpace.normalize x, by
        simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩
      have hu : ‖x‖ • (u : E) = x := NormedSpace.norm_smul_normalize x
      calc
        T (Complex.I • x) = T (‖x‖ • (complexSphereQuarterTurn u : E)) := by
          rw [complexSphereQuarterTurn_coe, smul_comm ‖x‖, hu]
        _ = ‖x‖ • (f (complexSphereQuarterTurn u) : F) := by
          rw [map_smul, hilbertSphereExtension_unit]
        _ = Complex.I • T x := by
          rw [h, ← hilbertSphereExtension_unit f u, smul_comm ‖x‖, ← map_smul, hu]
    let L : E ≃ₗᵢ[ℂ] F :=
      { toLinearEquiv :=
          { toEquiv := T.toEquiv
            map_add' := T.map_add
            map_smul' := by
              intro c x
              change T (c • x) = c • T x
              rw [← Complex.re_add_im c, add_smul, mul_smul, map_add,
                Complex.coe_smul, Complex.coe_smul, map_smul, map_smul, hI,
                add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul] }
        norm_map' := T.norm_map }
    exact ⟨L, hilbertSphereExtension_unit f⟩

/-- Complex Gram preservation is precisely complex linear extendability of a sphere isometry. -/
theorem hilbertSphereIsometry_complex_extension_iff_inner
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    (∃ T : E ≃ₗᵢ[ℂ] F, ∀ u : sphere (0 : E) 1, T (u : E) = (f u : F)) ↔
      ∀ u v : sphere (0 : E) 1,
        inner ℂ (f u : F) (f v : F) = inner ℂ (u : E) (v : E) := by
  constructor
  · rintro ⟨T, hT⟩ u v
    rw [← hT, ← hT]
    exact T.inner_map_map (u : E) (v : E)
  · intro h
    apply (hilbertSphereIsometry_complex_extension_iff f).mpr
    intro u
    have hi (v : sphere (0 : E) 1) :
        inner ℂ (f v : F) (f (complexSphereQuarterTurn u) : F) =
          inner ℂ (f v : F) (Complex.I • (f u : F)) := by
      rw [h, complexSphereQuarterTurn_coe, inner_smul_right, inner_smul_right, h]
    have hall (y : F) :
        inner ℂ y ((f (complexSphereQuarterTurn u) : F) - Complex.I • (f u : F)) = 0 := by
      by_cases hy : y = 0
      · simp [hy]
      let v : sphere (0 : F) 1 := ⟨NormedSpace.normalize y, by
        simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hy⟩
      have hv := hi (f.symm v)
      rw [f.apply_symm_apply] at hv
      have hz : inner ℂ (v : F)
          ((f (complexSphereQuarterTurn u) : F) - Complex.I • (f u : F)) = 0 := by
        rw [inner_sub_right, hv, sub_self]
      calc
        _ = inner ℂ (‖y‖ • (v : F))
            ((f (complexSphereQuarterTurn u) : F) - Complex.I • (f u : F)) := by
          rw [show ‖y‖ • (v : F) = y from NormedSpace.norm_smul_normalize y]
        _ = 0 := by rw [← Complex.coe_smul, inner_smul_left, hz, mul_zero]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (hall _))

end

end GaloisForLFunctions.HTGeometry
