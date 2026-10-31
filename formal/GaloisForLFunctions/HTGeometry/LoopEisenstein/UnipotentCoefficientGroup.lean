import GaloisForLFunctions.HTGeometry.FiniteRingSl2
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Unipotent coefficient groups over commutative rings

The upper-left entry has constant coefficient one and is a power-series
unit. The determinant determines the lower-right entry from the other
three entries, without any further relation on their coefficients.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
noncomputable section
variable (R : Type*) [CommRing R]

/-- Matrices whose constant reduction is an upper unipotent matrix. -/
def unipotentCoefficientGroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (PowerSeries R)) :=
  (FiniteRingSl2.upperHom (R := R)).range.comap
    (Matrix.SpecialLinearGroup.map (PowerSeries.constantCoeff (R := R)))

/-- Three constant-entry conditions describe the unipotent coefficient group. -/
theorem mem_unipotentCoefficientGroup (g : Matrix.SpecialLinearGroup (Fin 2) (PowerSeries R)) :
    g ∈ unipotentCoefficientGroup R ↔
      PowerSeries.constantCoeff (g 0 0) = 1 ∧
        PowerSeries.constantCoeff (g 1 0) = 0 ∧ PowerSeries.constantCoeff (g 1 1) = 1 := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) R => h 0 0) hs.symm,
      congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) R => h 1 0) hs.symm,
      congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) R => h 1 1) hs.symm⟩
  · rintro ⟨ha, hc, hd⟩
    refine ⟨Multiplicative.ofAdd (PowerSeries.constantCoeff (g 0 1)), ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha.symm
    · rfl
    · exact hc.symm
    · exact hd.symm

/-- Three independent entries of a positive unipotent matrix. -/
abbrev UnipotentCoefficientCoordinates :=
  {a : PowerSeries R // PowerSeries.constantCoeff a = 1} ×
    PowerSeries R × {c : PowerSeries R // PowerSeries.constantCoeff c = 0}

private def coordinateInverse (a : {a : PowerSeries R // PowerSeries.constantCoeff a = 1}) :
    PowerSeries R := PowerSeries.invOfUnit a 1

private theorem coordinate_mul_inverse
    (a : {a : PowerSeries R // PowerSeries.constantCoeff a = 1}) :
    (a : PowerSeries R) * coordinateInverse R a = 1 :=
  PowerSeries.mul_invOfUnit _ _ a.property

private theorem coordinateInverse_constantCoeff
    (a : {a : PowerSeries R // PowerSeries.constantCoeff a = 1}) :
    PowerSeries.constantCoeff (coordinateInverse R a) = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := R)) (coordinate_mul_inverse R a)
  simpa only [map_mul, a.property, one_mul, map_one] using h

/-- Build the literal determinant-one matrix from the three free entries. -/
def unipotentCoefficientOfCoordinates (p : UnipotentCoefficientCoordinates R) :
    unipotentCoefficientGroup R := by
  let d := coordinateInverse R p.1 * (1 + p.2.1 * (p.2.2 : PowerSeries R))
  have hdet : (p.1 : PowerSeries R) * d - p.2.1 * (p.2.2 : PowerSeries R) = 1 := by
    dsimp only [d]
    rw [← mul_assoc, coordinate_mul_inverse, one_mul]
    ring
  let g : Matrix.SpecialLinearGroup (Fin 2) (PowerSeries R) := ⟨!![p.1, p.2.1; p.2.2, d], by
    rw [Matrix.det_fin_two]
    exact hdet⟩
  refine ⟨g, (mem_unipotentCoefficientGroup R g).mpr ⟨p.1.property, p.2.2.property, ?_⟩⟩
  change PowerSeries.constantCoeff d = 1
  simp only [d, map_mul, map_add, map_one, p.2.2.property, mul_zero, add_zero,
    coordinateInverse_constantCoeff, one_mul]

/-- Read the upper-left, upper-right and lower-left entries. -/
def unipotentCoefficientToCoordinates (g : unipotentCoefficientGroup R) :
    UnipotentCoefficientCoordinates R :=
  (⟨g.1 0 0, ((mem_unipotentCoefficientGroup R g).mp g.property).1⟩,
    g.1 0 1, ⟨g.1 1 0, ((mem_unipotentCoefficientGroup R g).mp g.property).2.1⟩)

/-- The completed unipotent group has three independent power-series coordinates. -/
def unipotentCoefficientEquiv :
    unipotentCoefficientGroup R ≃ UnipotentCoefficientCoordinates R where
  toFun := unipotentCoefficientToCoordinates R
  invFun := unipotentCoefficientOfCoordinates R
  left_inv g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · change coordinateInverse R ⟨g.1 0 0, _⟩ * (1 + g.1 0 1 * g.1 1 0) = g.1 1 1
      have ha : PowerSeries.constantCoeff (g.1 0 0) = 1 :=
        ((mem_unipotentCoefficientGroup R g).mp g.property).1
      have hu : IsUnit (g.1 0 0) :=
        PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [ha]; exact isUnit_one)
      apply hu.mul_left_cancel
      have hm : g.1 0 0 * coordinateInverse R ⟨g.1 0 0, ha⟩ = 1 :=
        coordinate_mul_inverse R ⟨g.1 0 0, ha⟩
      rw [← mul_assoc, hm, one_mul]
      have hd := Matrix.SpecialLinearGroup.det_coe g.1
      rw [Matrix.det_fin_two] at hd
      linear_combination -hd
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentCoefficientEquiv
