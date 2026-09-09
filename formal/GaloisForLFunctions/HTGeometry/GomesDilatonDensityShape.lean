import GaloisForLFunctions.HTGeometry.GomesDilatonConnectionReconstruction

/-!
# Density shape and the constant kernel of a polynomial connection

A scalar-density reconstruction experiment prompted by arXiv:2607.24901v1 section 4.
Dividing by the density at the origin forgets exactly the same constant log-amplitude
as the existing first-order Schwartz connection. This is origin normalization, not
probability normalization. Tensor products here mean multiplication on one real base.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Positive density shape with its value at the origin fixed to one. -/
def gomesDilatonDensityShape (H : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (H.eval x - H.eval 0)

/-- Origin normalization is the literal quotient of positive density values. -/
theorem gomesDilatonDensityShape_ratio (H : ℝ[X]) (x : ℝ) :
    gomesDilatonDensityShape H x = dilatonWeight H x / dilatonWeight H 0 :=
  Real.exp_sub _ _

/-- Removing the constant coefficient realizes shape as another polynomial density. -/
theorem gomesDilatonDensityShape_centered (H : ℝ[X]) :
    gomesDilatonDensityShape H = dilatonWeight (H - C (H.eval 0)) := by
  funext x
  simp only [gomesDilatonDensityShape, dilatonWeight, eval_sub, eval_C]

/-- Every shape is strictly positive on the entire real line. -/
theorem gomesDilatonDensityShape_pos (H : ℝ[X]) (x : ℝ) :
    0 < gomesDilatonDensityShape H x := Real.exp_pos _

/-- Shape is continuous, without any decay or integrability requirement. -/
theorem gomesDilatonDensityShape_continuous (H : ℝ[X]) :
    Continuous (gomesDilatonDensityShape H) :=
  Real.continuous_exp.comp (H.continuous.sub continuous_const)

/-- Origin normalization fixes the amplitude to one. -/
theorem gomesDilatonDensityShape_origin (H : ℝ[X]) :
    gomesDilatonDensityShape H 0 = 1 := by
  simp only [gomesDilatonDensityShape, sub_self, Real.exp_zero]

/-- Complete classification of the information lost by density-shape observation. -/
theorem gomesDilatonDensityShape_eq_iff (H K : ℝ[X]) :
    gomesDilatonDensityShape H = gomesDilatonDensityShape K ↔
      ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonDensityShape_centered, gomesDilatonDensityShape_centered]
  constructor
  · intro h
    have he := gomesDilatonWeight_injective h
    refine ⟨H.eval 0 - K.eval 0, ?_⟩
    rw [map_sub]
    linear_combination he
  · rintro ⟨c, rfl⟩
    congr 1
    simp only [eval_add, eval_C, map_add]
    ring

/-- The complete shape and the full connection forget exactly the same data. -/
theorem gomesDilatonDensityShape_connection_iff (H K : ℝ[X]) :
    gomesDilatonDensityShape H = gomesDilatonDensityShape K ↔
      dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  rw [gomesDilatonDensityShape_eq_iff, gomesDilatonConnection_constant_iff]

/-- Arbitrary constant shifts remain invisible after origin normalization. -/
theorem gomesDilatonDensityShape_constant (H : ℝ[X]) (c : ℝ) :
    gomesDilatonDensityShape (H + C c) = gomesDilatonDensityShape H :=
  (gomesDilatonDensityShape_eq_iff _ _).mpr ⟨c, rfl⟩

/-- Density shape together with one amplitude reconstructs the whole polynomial. -/
theorem gomesDilatonDensityShape_amplitude_injective :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonDensityShape H, dilatonWeight H 0)) := by
  intro H K h
  have hs := congrArg Prod.fst h
  have ha := congrArg Prod.snd h
  exact (gomesDilatonConnection_density_origin_iff H K).mp
    ⟨(gomesDilatonDensityShape_connection_iff H K).mp hs, ha⟩

/-- Tensor multiplication descends exactly to the origin-normalized shapes. -/
theorem gomesDilatonDensityShape_add (H K : ℝ[X]) (x : ℝ) :
    gomesDilatonDensityShape (H + K) x =
      gomesDilatonDensityShape H x * gomesDilatonDensityShape K x := by
  simp only [gomesDilatonDensityShape, eval_add, ← Real.exp_add]
  congr 1
  ring

/-- Dualization inverts the complete positive shape. -/
theorem gomesDilatonDensityShape_neg (H : ℝ[X]) (x : ℝ) :
    gomesDilatonDensityShape (-H) x = (gomesDilatonDensityShape H x)⁻¹ := by
  simp only [gomesDilatonDensityShape, eval_neg, ← Real.exp_neg]
  congr 1
  ring

/-- Even a nonzero constant profile has the same complete shape as the zero profile. -/
theorem gomesDilatonDensityShape_not_injective :
    ¬ Function.Injective gomesDilatonDensityShape := by
  intro h
  have he : (1 : ℝ[X]) = 0 := h
    ((gomesDilatonDensityShape_eq_iff 1 0).mpr ⟨1, by simp⟩)
  exact one_ne_zero he

end GaloisForLFunctions.HTGeometry
