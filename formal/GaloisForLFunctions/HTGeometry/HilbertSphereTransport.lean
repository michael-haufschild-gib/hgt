import GaloisForLFunctions.HTGeometry.HilbertSphereExtension
import GaloisForLFunctions.HTGeometry.CrossSphereIsometryTransport
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Linear, Gram, and measure transport from sphere distances

Applications of the Hilbert-space specialization of the sphere-isometry
extension theorem in `openai/math`. The boundary map itself transports finite
Gram data, ambient volume, sphere measure, and every real sphere integral.
-/

open Metric MeasureTheory Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The existing sphere-transport map recovers the original boundary isometry exactly. -/
@[simp] theorem crossSphereMap_hilbertSphereExtension
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    crossSphereMap (hilbertSphereExtension f) = f.toEquiv := by
  apply Equiv.ext
  intro u
  apply Subtype.ext
  exact hilbertSphereExtension_unit f u

/-- The real Gram kernel of any sphere family is determined by its boundary distances. -/
theorem hilbertSphereIsometry_gram {ι : Type*}
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (u : ι → sphere (0 : E) 1) :
    Matrix.gram ℝ (fun i => (f (u i) : F)) = Matrix.gram ℝ (fun i => (u i : E)) := by
  ext i j
  exact hilbertSphereIsometry_inner f (u i) (u j)

/-- Boundary distances determine every finite real Gram determinant. -/
theorem hilbertSphereIsometry_gram_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (u : ι → sphere (0 : E) 1) :
    (Matrix.gram ℝ (fun i => (f (u i) : F))).det =
      (Matrix.gram ℝ (fun i => (u i : E))).det :=
  congrArg Matrix.det (hilbertSphereIsometry_gram f u)

/-- Linear independence of finite real sphere frames is invariant under boundary isometries. -/
theorem hilbertSphereIsometry_linearIndependent {ι : Type*} [Fintype ι]
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (u : ι → sphere (0 : E) 1) :
    LinearIndependent ℝ (fun i => (f (u i) : F)) ↔
      LinearIndependent ℝ (fun i => (u i : E)) := by
  rw [← Matrix.posDef_gram_iff_linearIndependent,
    ← Matrix.posDef_gram_iff_linearIndependent, hilbertSphereIsometry_gram]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- A boundary isometry canonically determines a volume-preserving map of the ambient spaces. -/
theorem hilbertSphereExtension_measurePreserving
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    MeasurePreserving (hilbertSphereExtension f) (volume : Measure E) (volume : Measure F) :=
  (hilbertSphereExtension f).measurePreserving

/-- Sphere measure is transported by an arbitrary onto boundary isometry. -/
theorem hilbertSphereIsometry_measurePreserving
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    MeasurePreserving f (volume : Measure E).toSphere (volume : Measure F).toSphere := by
  let T := hilbertSphereExtension f
  have he : (crossSphereMap T : sphere (0 : E) 1 → sphere (0 : F) 1) = f :=
    congrArg (fun e : sphere (0 : E) 1 ≃ sphere (0 : F) 1 =>
      (e : sphere (0 : E) 1 → sphere (0 : F) 1)) (crossSphereMap_hilbertSphereExtension f)
  rw [← he]
  refine ⟨(continuous_crossSphereMap T).measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (continuous_crossSphereMap T).measurable hS]
  exact toSphere_preimage_crossSphereMap T hS

/-- All real sphere observables have the same integral after boundary-isometric transport. -/
theorem hilbertSphereIsometry_integral
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (g : sphere (0 : F) 1 → ℝ) :
    (∫ u, g (f u) ∂(volume : Measure E).toSphere) =
      ∫ v, g v ∂(volume : Measure F).toSphere :=
  (hilbertSphereIsometry_measurePreserving f).integral_comp
    f.toHomeomorph.measurableEmbedding g

end

end GaloisForLFunctions.HTGeometry
