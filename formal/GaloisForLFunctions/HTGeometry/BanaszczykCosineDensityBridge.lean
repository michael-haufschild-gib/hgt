import GaloisForLFunctions.HTGeometry.AlternativeHypothesisLemma4
import GaloisForLFunctions.HTGeometry.BanaszczykRationalDensity

/-!
# Cosine-density bridge for vector balancing

The compactly supported function already used by
`AlternativeHypothesisLemma4` is exactly the one-dimensional factor in Lemma
2.4 of Guo--Fang--Lu.  This module turns that coincidence into a reusable
probability density and verifies the paper's tangent-coordinate Jacobian.

Thus one corpus test function now has two independent meanings: a compact
Fourier test and the seed distribution for vector balancing.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

/-- Zero extension of the corpus's cosine-squared test function from `(-1,1)`.
This is the `C = 1`, `d = 1` factor of the paper's cube density. -/
def banaszczykCosineDensity : ℝ → ℝ :=
  Set.indicator (Set.Ioo (-1 : ℝ) 1) alternativeHypothesisLemma4GOne

theorem banaszczykCosineDensity_nonneg (x : ℝ) :
    0 ≤ banaszczykCosineDensity x := by
  unfold banaszczykCosineDensity
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    unfold alternativeHypothesisLemma4GOne
    positivity
  · rw [Set.indicator_of_notMem hx]

theorem banaszczykCosineDensity_pos_of_mem {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < banaszczykCosineDensity x := by
  rw [banaszczykCosineDensity, Set.indicator_of_mem hx]
  unfold alternativeHypothesisLemma4GOne
  have hs : 0 < Real.pi / 2 := by positivity
  have hangle : Real.pi * x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have h := mul_lt_mul_of_pos_right hx.1 hs
      convert h using 1 <;> ring
    · have h := mul_lt_mul_of_pos_right hx.2 hs
      convert h using 1 <;> ring
  have hcos := Real.cos_pos_of_mem_Ioo hangle
  positivity

@[simp]
theorem banaszczykCosineDensity_pos_iff (x : ℝ) :
    0 < banaszczykCosineDensity x ↔ x ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · intro h
    by_contra hx
    rw [banaszczykCosineDensity, Set.indicator_of_notMem hx] at h
    exact lt_irrefl 0 h
  · exact banaszczykCosineDensity_pos_of_mem

@[simp]
theorem banaszczykCosineDensity_eq_zero_iff (x : ℝ) :
    banaszczykCosineDensity x = 0 ↔ x ∉ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hx hmem
    have hpos := banaszczykCosineDensity_pos_of_mem hmem
    rw [hx] at hpos
    exact lt_irrefl 0 hpos
  · intro hx
    rw [banaszczykCosineDensity, Set.indicator_of_notMem hx]

theorem integrable_banaszczykCosineDensity :
    Integrable banaszczykCosineDensity := by
  unfold banaszczykCosineDensity
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  refine (Continuous.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
  unfold alternativeHypothesisLemma4GOne
  fun_prop

/-- The corpus's cosine-squared test is already normalized on `(-1,1)`. -/
@[simp]
theorem integral_banaszczykCosineDensity :
    ∫ x : ℝ, banaszczykCosineDensity x = 1 := by
  unfold banaszczykCosineDensity
  rw [integral_indicator measurableSet_Ioo]
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [show alternativeHypothesisLemma4GOne =
      fun x : ℝ => Real.cos (x * (Real.pi / 2)) ^ (2 : ℕ) by
    funext x
    unfold alternativeHypothesisLemma4GOne
    congr 2
    ring]
  rw [intervalIntegral.integral_comp_mul_right
    (fun x : ℝ => Real.cos x ^ (2 : ℕ)) (by positivity : Real.pi / 2 ≠ 0)]
  rw [smul_eq_mul, integral_cos_sq]
  rw [show (-1 : ℝ) * (Real.pi / 2) = -(Real.pi / 2) by ring,
    show (1 : ℝ) * (Real.pi / 2) = Real.pi / 2 by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  ring

/-- Inverse tangent chart from the rational line to the open support interval. -/
def banaszczykTangentCoordinate (t : ℝ) : ℝ :=
  (2 / Real.pi) * Real.arctan t

theorem banaszczykTangentCoordinate_mem (t : ℝ) :
    banaszczykTangentCoordinate t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h := Real.arctan_mem_Ioo t
  have hs : 0 < 2 / Real.pi := by positivity
  constructor
  · have hm := mul_lt_mul_of_pos_left h.1 hs
    unfold banaszczykTangentCoordinate
    convert hm using 1
    all_goals field_simp [Real.pi_ne_zero]
  · have hm := mul_lt_mul_of_pos_left h.2 hs
    unfold banaszczykTangentCoordinate
    convert hm using 1
    all_goals field_simp [Real.pi_ne_zero]

theorem hasDerivAt_banaszczykTangentCoordinate (t : ℝ) :
    HasDerivAt banaszczykTangentCoordinate
      ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹) t := by
  unfold banaszczykTangentCoordinate
  simpa [one_div] using (Real.hasDerivAt_arctan t).const_mul (2 / Real.pi)

/-- Exact pointwise change-of-variables identity from the compact cosine
density to the paper's rational density. -/
theorem banaszczyk_tangent_jacobian (t : ℝ) :
    banaszczykCosineDensity (banaszczykTangentCoordinate t) *
        ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹) =
      banaszczykRationalDensity t := by
  rw [banaszczykCosineDensity,
    Set.indicator_of_mem (banaszczykTangentCoordinate_mem t)]
  unfold alternativeHypothesisLemma4GOne banaszczykTangentCoordinate
  have harg : Real.pi * ((2 / Real.pi) * Real.arctan t) / 2 = Real.arctan t := by
    field_simp [Real.pi_ne_zero]
  rw [harg, Real.cos_sq_arctan]
  unfold banaszczykRationalDensity
  field_simp [Real.pi_ne_zero, show (1 + t ^ (2 : ℕ) : ℝ) ≠ 0 by positivity]

end GaloisForLFunctions.HTGeometry
