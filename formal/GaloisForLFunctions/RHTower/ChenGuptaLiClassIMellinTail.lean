/-
# Chen--Gupta--Li Class-I initial Mellin tail

This turns the existing safe-line inverse Mellin identity into CGL Section
12.1's literal `exp(-(Y+1)⁻¹) + tail` form for every certified primitive
Class-I zero.  It is an exact safe-line identity; the separate finite contour
argument controls only the difference between its two vertical edges so far.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIContours
import GaloisForLFunctions.RHTower.ChenGuptaLiInfiniteMellinDetector

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A positive real scale carried as certified data, rather than a raw
positivity premise. -/
abbrev CGLPositiveSmoothingScale := {x : ℝ // 0 < x}

/-- The shifted unit coefficient in CGL's full detector product. -/
def cglShiftedUnitCoefficient (s : CGLRightHalfPlanePoint) (n : ℕ) : ℂ :=
  cglUnitCoefficient n * (n : ℂ) ^ (-s.1)

/-- The shifted full detector coefficient is exactly its unit atom plus its
literal shifted tail coefficient. -/
theorem cglShiftedDetectorProductCoefficient_eq_unit_add_tail
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (n : ℕ) :
    cglShiftedDetectorProductCoefficient X q χ s n =
      cglShiftedUnitCoefficient s n + cglShiftedDetectorTailCoefficient X q χ s n := by
  unfold cglShiftedDetectorProductCoefficient cglShiftedUnitCoefficient
    cglShiftedDetectorTailCoefficient
  rw [cglTruncatedMobiusTwist_convolution_eq_unit_add_tail]
  ring

/-- The exponential profile of the shifted unit coefficient is its literal
single atom. -/
theorem coeffLaplaceProfile_shiftedUnit
    (s : CGLRightHalfPlanePoint) (x : ℝ) :
    coeffLaplaceProfile (cglShiftedUnitCoefficient s) x = Complex.exp (-x) := by
  unfold coeffLaplaceProfile cglShiftedUnitCoefficient
  rw [tsum_eq_single 1]
  · simp [cglUnitCoefficient]
  · intro n hn
    simp [cglUnitCoefficient, hn]

/-- The positive-scale shifted detector tail is absolutely summable after its
literal exponential smoothing. -/
theorem summable_cglShiftedDetectorTailCoefficient_laplace
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Summable (fun n : ℕ => cglShiftedDetectorTailCoefficient X q χ s n *
      Complex.exp (-((n : ℝ) * x.1 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_cglShiftedDetectorTailCoefficient_uniformBound
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_exp_neg_nat_mul x.2).mul_left C)
  rw [norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x.1)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (hbound X q χ s n) hexp

private theorem summable_cglShiftedUnitCoefficient_laplace
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Summable (fun n : ℕ => cglShiftedUnitCoefficient s n *
      Complex.exp (-((n : ℝ) * x.1 : ℝ))) := by
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  apply Set.Finite.subset (Finset.finite_toSet {1})
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hne
  have hn1 : n ≠ 1 := by simpa using hne
  simp [cglShiftedUnitCoefficient, cglUnitCoefficient, hn1] at hn

private theorem coeffLaplaceProfile_shiftedDetectorProduct_eq_unit_add_tail
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    coeffLaplaceProfile (cglShiftedDetectorProductCoefficient X q χ s) x.1 =
      Complex.exp (-x.1) + coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1 := by
  rw [← coeffLaplaceProfile_shiftedUnit s x.1]
  unfold coeffLaplaceProfile
  rw [← (summable_cglShiftedUnitCoefficient_laplace s x).tsum_add
    (summable_cglShiftedDetectorTailCoefficient_laplace X q χ s x)]
  apply tsum_congr
  intro n
  rw [cglShiftedDetectorProductCoefficient_eq_unit_add_tail]
  ring

/-- Shifting preserves the proved vanishing of every tail coefficient through
the literal detector cutoff. -/
theorem cglShiftedDetectorTailCoefficient_vanishes_below_cutoff
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (k : Fin X) :
    cglShiftedDetectorTailCoefficient X q χ s (k.1 + 2) = 0 := by
  unfold cglShiftedDetectorTailCoefficient
  rw [cglDetectorTailCoefficient_vanishes_below_cutoff]
  ring

/-- The point of an actual primitive Class-I window zero, certified as lying
in CGL's right half-plane. -/
def cglPrimitiveClassIWindowZeroRightHalfPlanePoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) : CGLRightHalfPlanePoint :=
  ⟨z.1.1, le_of_lt z.2⟩

/-- **CGL Section 12.1, safe-line tail identity.**  At every certified
primitive Class-I zero, the exact safe-line inverse Mellin value is the
literal smoothed unit atom plus the shifted detector tail. -/
theorem cglPrimitiveClassI_mellin_initialLine_tail_identity
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    mellinInv 2 (fun w => Complex.Gamma w *
      (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1 (z.1.1 + w) *
        DirichletCharacter.LFunction χ.1.1 (z.1.1 + w))) ((Y + 1 : ℕ) : ℝ)⁻¹ =
      Complex.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) +
        coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
          ((Y + 1 : ℕ) : ℝ)⁻¹ := by
  calc
    mellinInv 2 (fun w => Complex.Gamma w *
        (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1 (z.1.1 + w) *
          DirichletCharacter.LFunction χ.1.1 (z.1.1 + w))) ((Y + 1 : ℕ) : ℝ)⁻¹ =
        coeffLaplaceProfile (cglShiftedDetectorProductCoefficient X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z))
          ((Y + 1 : ℕ) : ℝ)⁻¹ := by
      simpa [cglPrimitiveClassIWindowZeroRightHalfPlanePoint] using
        cglDetectorProduct_mellin_initialLine_identity X n Y χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
    _ = _ := coeffLaplaceProfile_shiftedDetectorProduct_eq_unit_add_tail X n χ.1.1
      (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
      ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩

end RHTower
