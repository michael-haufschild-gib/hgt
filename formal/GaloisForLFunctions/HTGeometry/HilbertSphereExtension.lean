import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Tactic.Linarith

/-!
# Sphere isometries extend to real Hilbert-space isometries

Hilbert-space specialization of the sphere-isometry extension theorem in
`openai/math`, `lean/OAI/Analysis/SphereIsometry/Extension.lean`.
Direct polarization provides the radial extension without completeness or
nontriviality assumptions. Its uniqueness connects boundary distance data to
existing linear-isometry infrastructure.
-/

open Metric
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ E] in
private theorem sphere_norm_one (u : sphere (0 : E) 1) : ‖(u : E)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

private def sphereNormalize (x : E) (hx : x ≠ 0) : sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩

/-- A sphere isometry determines a radial map on the whole Hilbert space, including its origin. -/
def hilbertSphereRadial (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (x : E) : F := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • (f (sphereNormalize x hx) : F)

@[simp] theorem hilbertSphereRadial_zero (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    hilbertSphereRadial f 0 = 0 := by
  simp [hilbertSphereRadial]

/-- Pairwise sphere distances recover all real inner products on the sphere. -/
theorem hilbertSphereIsometry_inner (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1)
    (u v : sphere (0 : E) 1) :
    inner ℝ (f u : F) (f v : F) = inner ℝ (u : E) (v : E) := by
  have hd : ‖(f u : F) - (f v : F)‖ = ‖(u : E) - (v : E)‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using f.dist_eq u v
  have hs := norm_sub_sq_real (u : E) (v : E)
  have ht := norm_sub_sq_real (f u : F) (f v : F)
  rw [sphere_norm_one, sphere_norm_one] at hs ht
  rw [hd] at ht
  linarith

@[simp] theorem hilbertSphereRadial_norm (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1)
    (x : E) : ‖hilbertSphereRadial f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hilbertSphereRadial, dif_neg hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), sphere_norm_one, mul_one]

@[simp] theorem hilbertSphereRadial_unit (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1)
    (u : sphere (0 : E) 1) : hilbertSphereRadial f (u : E) = (f u : F) := by
  have hu : (u : E) ≠ 0 := by
    intro h
    have := sphere_norm_one u
    simp [h] at this
  have hn : sphereNormalize (u : E) hu = u :=
    Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (sphere_norm_one u))
  simp only [hilbertSphereRadial, dif_neg hu, sphere_norm_one, one_smul, hn]

/-- The radial map preserves every real inner product, without completeness or dimension premises. -/
theorem hilbertSphereRadial_inner (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1)
    (x y : E) : inner ℝ (hilbertSphereRadial f x) (hilbertSphereRadial f y) = inner ℝ x y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  simp only [hilbertSphereRadial, dif_neg hx, dif_neg hy,
    real_inner_smul_left, inner_smul_right, hilbertSphereIsometry_inner]
  change ‖y‖ * (‖x‖ * inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y)) = _
  rw [← real_inner_smul_left, ← inner_smul_right,
    NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]

/-- Sphere-distance preservation extends to all distances by radial polarization. -/
theorem hilbertSphereRadial_isometry (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    Isometry (hilbertSphereRadial f) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm]
  have he : ‖hilbertSphereRadial f x - hilbertSphereRadial f y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, hilbertSphereRadial_norm,
      hilbertSphereRadial_norm, hilbertSphereRadial_inner]
  nlinarith [norm_nonneg (hilbertSphereRadial f x - hilbertSphereRadial f y),
    norm_nonneg (x - y)]

private theorem hilbertSphereRadial_pos_smul_unit
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1)
    (u : sphere (0 : E) 1) (r : ℝ) (hr : 0 < r) :
    hilbertSphereRadial f (r • (u : E)) = r • (f u : F) := by
  have hn : ‖r • (u : E)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, sphere_norm_one, mul_one]
  have hx : r • (u : E) ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hn
    linarith
  have hu : sphereNormalize (r • (u : E)) hx = u := by
    apply Subtype.ext
    exact (NormedSpace.normalize_smul_of_pos hr (u : E)).trans
      (NormedSpace.normalize_eq_self_of_norm_eq_one (sphere_norm_one u))
  simp only [hilbertSphereRadial, dif_neg hx, hn, hu]

/-- Onto sphere isometries have onto radial extensions, including zero-dimensional spaces. -/
theorem hilbertSphereRadial_surjective (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    Function.Surjective (hilbertSphereRadial f) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let v := sphereNormalize y hy
  refine ⟨‖y‖ • (f.symm v : E), ?_⟩
  rw [hilbertSphereRadial_pos_smul_unit f (f.symm v) ‖y‖ (norm_pos_iff.mpr hy),
    f.apply_symm_apply]
  exact NormedSpace.norm_smul_normalize y

/-- The Hilbert-space specialization of Tingley's extension theorem, with a canonical radial map. -/
def hilbertSphereExtension (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) : E ≃ₗᵢ[ℝ] F :=
  let e : E ≃ᵢ F :=
    { toEquiv := Equiv.ofBijective (hilbertSphereRadial f)
        ⟨(hilbertSphereRadial_isometry f).injective, hilbertSphereRadial_surjective f⟩
      isometry_toFun := hilbertSphereRadial_isometry f }
  e.toRealLinearIsometryEquivOfMapZero (hilbertSphereRadial_zero f)

@[simp] theorem hilbertSphereExtension_apply
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (x : E) :
    hilbertSphereExtension f x = hilbertSphereRadial f x := rfl

@[simp] theorem hilbertSphereExtension_unit
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) (u : sphere (0 : E) 1) :
    hilbertSphereExtension f (u : E) = (f u : F) := hilbertSphereRadial_unit f u

/-- Sphere isometries have a unique linear isometric extension. -/
theorem hilbertSphereExtension_existsUnique
    (f : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1) :
    ∃! T : E ≃ₗᵢ[ℝ] F, ∀ u : sphere (0 : E) 1, T (u : E) = (f u : F) := by
  refine ⟨hilbertSphereExtension f, hilbertSphereExtension_unit f, ?_⟩
  intro T hT
  ext x
  by_cases hx : x = 0
  · simp [hx]
  calc
    T x = T (‖x‖ • (sphereNormalize x hx : E)) := by
      rw [show ‖x‖ • (sphereNormalize x hx : E) = x from NormedSpace.norm_smul_normalize x]
    _ = ‖x‖ • (f (sphereNormalize x hx) : F) := by rw [map_smul, hT]
    _ = hilbertSphereExtension f x := by simp only [hilbertSphereExtension_apply,
        hilbertSphereRadial, dif_neg hx]

end

end GaloisForLFunctions.HTGeometry
