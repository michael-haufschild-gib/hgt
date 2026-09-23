import GaloisForLFunctions.HTGeometry.BanaszczykCosineDensityBridge
import GaloisForLFunctions.HTGeometry.OpenBanaszczykTransform
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product density on the Komlós target cube

This specializes Lemma 2.4 of Guo--Fang--Lu to the exact cube already used by
the corpus's Banaszczyk transform.  It proves, in every finite dimension, that
the scaled cosine product is an integrable probability density and is positive
exactly on the open Komlós cube.  The coordinatewise tangent chart has the
paper's rational product density as its exact Jacobian transform.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Cosine-squared probability density rescaled to one coordinate of the
Komlós cube. -/
def komlosCoordinateDensity (x : ℝ) : ℝ :=
  komlosCubeRadius⁻¹ * banaszczykCosineDensity (x / komlosCubeRadius)

theorem integrable_komlosCoordinateDensity :
    Integrable komlosCoordinateDensity := by
  unfold komlosCoordinateDensity
  exact ((integrable_comp_div_iff banaszczykCosineDensity
    komlosCubeRadius_pos.ne').mpr integrable_banaszczykCosineDensity).const_mul _

@[simp]
theorem integral_komlosCoordinateDensity :
    ∫ x : ℝ, komlosCoordinateDensity x = 1 := by
  unfold komlosCoordinateDensity
  rw [integral_const_mul, Measure.integral_comp_div, integral_banaszczykCosineDensity]
  rw [abs_of_pos komlosCubeRadius_pos]
  simp [smul_eq_mul, komlosCubeRadius_pos.ne']

theorem komlosCoordinateDensity_nonneg (x : ℝ) :
    0 ≤ komlosCoordinateDensity x := by
  unfold komlosCoordinateDensity
  exact mul_nonneg (inv_nonneg.mpr komlosCubeRadius_pos.le)
    (banaszczykCosineDensity_nonneg _)

@[simp]
theorem komlosCoordinateDensity_pos_iff (x : ℝ) :
    0 < komlosCoordinateDensity x ↔ |x| < komlosCubeRadius := by
  rw [komlosCoordinateDensity, mul_pos_iff_of_pos_left (inv_pos.mpr komlosCubeRadius_pos),
    banaszczykCosineDensity_pos_iff, Set.mem_Ioo, abs_lt]
  constructor
  · intro h
    constructor
    · have h' := (lt_div_iff₀ komlosCubeRadius_pos).mp h.1
      simpa using h'
    · have h' := (div_lt_iff₀ komlosCubeRadius_pos).mp h.2
      simpa using h'
  · intro h
    constructor
    · apply (lt_div_iff₀ komlosCubeRadius_pos).mpr
      simpa using h.1
    · apply (div_lt_iff₀ komlosCubeRadius_pos).mpr
      simpa using h.2

/-- Product cosine-squared density in dimension `d`. -/
def komlosProductDensity (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, komlosCoordinateDensity (x i)

theorem komlosProductDensity_nonneg (d : ℕ) (x : Fin d → ℝ) :
    0 ≤ komlosProductDensity d x := by
  unfold komlosProductDensity
  exact Finset.prod_nonneg fun i _ => komlosCoordinateDensity_nonneg (x i)

/-- Exact support statement: positivity is equivalent to membership in the
open target cube, including dimension zero. -/
@[simp]
theorem komlosProductDensity_pos_iff (d : ℕ) (x : Fin d → ℝ) :
    0 < komlosProductDensity d x ↔ x ∈ komlosCube d := by
  constructor
  · intro hpos
    rw [komlosCube, mem_openCoordinateCube]
    intro i
    by_contra hi
    have hle : komlosCoordinateDensity (x i) ≤ 0 := by
      rw [← not_lt]
      exact fun h => hi ((komlosCoordinateDensity_pos_iff (x i)).mp h)
    have hz : komlosCoordinateDensity (x i) = 0 :=
      le_antisymm hle (komlosCoordinateDensity_nonneg (x i))
    have hzero : komlosProductDensity d x = 0 := by
      unfold komlosProductDensity
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · intro hx
    rw [komlosCube, mem_openCoordinateCube] at hx
    unfold komlosProductDensity
    exact Finset.prod_pos fun i _ => (komlosCoordinateDensity_pos_iff (x i)).mpr (hx i)

theorem integrable_komlosProductDensity (d : ℕ) :
    Integrable (komlosProductDensity d)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  unfold komlosProductDensity
  exact Integrable.fintype_prod fun _ => integrable_komlosCoordinateDensity

/-- Dimension-free normalization of the product density. -/
@[simp]
theorem integral_komlosProductDensity (d : ℕ) :
    ∫ x : Fin d → ℝ, komlosProductDensity d x
        ∂(Measure.pi fun _ : Fin d => (volume : Measure ℝ)) = 1 := by
  unfold komlosProductDensity
  rw [integral_fintype_prod_eq_pow, integral_komlosCoordinateDensity]
  simp

/-- Scaled tangent chart from the rational line to one Komlós coordinate. -/
def komlosTangentCoordinate (t : ℝ) : ℝ :=
  komlosCubeRadius * banaszczykTangentCoordinate t

theorem hasDerivAt_komlosTangentCoordinate (t : ℝ) :
    HasDerivAt komlosTangentCoordinate
      (komlosCubeRadius * ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹)) t := by
  unfold komlosTangentCoordinate
  exact (hasDerivAt_banaszczykTangentCoordinate t).const_mul komlosCubeRadius

/-- Scaling cancels exactly in the tangent Jacobian. -/
theorem komlos_tangent_jacobian (t : ℝ) :
    komlosCoordinateDensity (komlosTangentCoordinate t) *
        (komlosCubeRadius * ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹)) =
      banaszczykRationalDensity t := by
  have h := banaszczyk_tangent_jacobian t
  unfold komlosCoordinateDensity komlosTangentCoordinate
  have hR : komlosCubeRadius ≠ 0 := komlosCubeRadius_pos.ne'
  rw [mul_div_cancel_left₀ _ hR]
  calc
    komlosCubeRadius⁻¹ * banaszczykCosineDensity (banaszczykTangentCoordinate t) *
          (komlosCubeRadius * ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹)) =
        banaszczykCosineDensity (banaszczykTangentCoordinate t) *
          ((2 / Real.pi) * (1 + t ^ (2 : ℕ))⁻¹) := by
      field_simp [hR]
    _ = banaszczykRationalDensity t := h

def komlosTangentChart (d : ℕ) (t : Fin d → ℝ) : Fin d → ℝ :=
  fun i => komlosTangentCoordinate (t i)

def komlosTangentJacobian (d : ℕ) (t : Fin d → ℝ) : ℝ :=
  ∏ i, komlosCubeRadius * ((2 / Real.pi) * (1 + (t i) ^ (2 : ℕ))⁻¹)

/-- Finite-dimensional product form of the tangent-Jacobian identity. -/
theorem komlos_product_tangent_jacobian (d : ℕ) (t : Fin d → ℝ) :
    komlosProductDensity d (komlosTangentChart d t) * komlosTangentJacobian d t =
      ∏ i, banaszczykRationalDensity (t i) := by
  unfold komlosProductDensity komlosTangentChart komlosTangentJacobian
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => komlos_tangent_jacobian (t i)

end GaloisForLFunctions.HTGeometry
