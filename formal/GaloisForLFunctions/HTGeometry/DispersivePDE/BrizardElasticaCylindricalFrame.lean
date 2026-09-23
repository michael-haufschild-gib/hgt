import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaFrameInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Cylindrical frame from vertical Frenet coefficients

Equations (78)--(82) construct radial and azimuthal axes from the vertical-axis Frenet
coefficients `A,B,C`.  Regularity is packaged in the data, so every theorem is closed and the
square-root denominator is globally nonzero.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure RegularVerticalCoefficients where
  A : ℝ
  B : ℝ
  C : ℝ
  unitSphere : A ^ (2 : ℕ) + B ^ (2 : ℕ) + C ^ (2 : ℕ) = 1
  cylindricalRegular : C ^ (2 : ℕ) < 1

@[ext]
structure FrenetCoordinates where
  tangent : ℝ
  normal : ℝ
  binormal : ℝ

def frenetDot (u v : FrenetCoordinates) : ℝ :=
  u.tangent * v.tangent + u.normal * v.normal + u.binormal * v.binormal

def frenetCross (u v : FrenetCoordinates) : FrenetCoordinates where
  tangent := u.normal * v.binormal - u.binormal * v.normal
  normal := u.binormal * v.tangent - u.tangent * v.binormal
  binormal := u.tangent * v.normal - u.normal * v.tangent

noncomputable def cylindricalDenominator (P : RegularVerticalCoefficients) : ℝ :=
  Real.sqrt (1 - P.C ^ (2 : ℕ))

theorem cylindricalDenominator_pos (P : RegularVerticalCoefficients) :
    0 < cylindricalDenominator P := by
  rw [cylindricalDenominator]
  exact Real.sqrt_pos.2 (sub_pos.2 P.cylindricalRegular)

theorem cylindricalDenominator_sq (P : RegularVerticalCoefficients) :
    cylindricalDenominator P ^ (2 : ℕ) = 1 - P.C ^ (2 : ℕ) := by
  rw [cylindricalDenominator, Real.sq_sqrt]
  exact le_of_lt (sub_pos.2 P.cylindricalRegular)

def verticalInFrenet (P : RegularVerticalCoefficients) : FrenetCoordinates :=
  ⟨P.A, P.B, P.C⟩

/-- Equation (78): radial unit vector in Frenet coordinates. -/
noncomputable def radialInFrenet (P : RegularVerticalCoefficients) : FrenetCoordinates :=
  ⟨P.B / cylindricalDenominator P, -P.A / cylindricalDenominator P, 0⟩

/-- Equation (79): azimuthal unit vector, defined intrinsically by the cross product. -/
noncomputable def azimuthalInFrenet (P : RegularVerticalCoefficients) : FrenetCoordinates :=
  frenetCross (verticalInFrenet P) (radialInFrenet P)

theorem verticalInFrenet_unit (P : RegularVerticalCoefficients) :
    frenetDot (verticalInFrenet P) (verticalInFrenet P) = 1 := by
  rw [frenetDot, verticalInFrenet]
  simpa [pow_two] using P.unitSphere

theorem radialInFrenet_unit (P : RegularVerticalCoefficients) :
    frenetDot (radialInFrenet P) (radialInFrenet P) = 1 := by
  have hden := cylindricalDenominator_sq P
  have hsum : P.A ^ (2 : ℕ) + P.B ^ (2 : ℕ) = 1 - P.C ^ (2 : ℕ) := by
    linarith [P.unitSphere]
  rw [frenetDot, radialInFrenet]
  field_simp [ne_of_gt (cylindricalDenominator_pos P)]
  nlinarith

theorem vertical_dot_radial (P : RegularVerticalCoefficients) :
    frenetDot (verticalInFrenet P) (radialInFrenet P) = 0 := by
  rw [frenetDot, verticalInFrenet, radialInFrenet]
  field_simp [ne_of_gt (cylindricalDenominator_pos P)]
  ring

theorem azimuthalInFrenet_eq (P : RegularVerticalCoefficients) :
    azimuthalInFrenet P =
      ⟨P.C * P.A / cylindricalDenominator P,
        P.C * P.B / cylindricalDenominator P,
        -cylindricalDenominator P⟩ := by
  ext
  · rw [azimuthalInFrenet, frenetCross, verticalInFrenet, radialInFrenet]
    ring
  · rw [azimuthalInFrenet, frenetCross, verticalInFrenet, radialInFrenet]
    ring
  · rw [azimuthalInFrenet, frenetCross, verticalInFrenet, radialInFrenet]
    have hden := cylindricalDenominator_sq P
    have hsum : P.A ^ (2 : ℕ) + P.B ^ (2 : ℕ) = 1 - P.C ^ (2 : ℕ) := by
      linarith [P.unitSphere]
    field_simp [ne_of_gt (cylindricalDenominator_pos P)]
    nlinarith

theorem azimuthalInFrenet_unit (P : RegularVerticalCoefficients) :
    frenetDot (azimuthalInFrenet P) (azimuthalInFrenet P) = 1 := by
  rw [azimuthalInFrenet_eq, frenetDot]
  have hden := cylindricalDenominator_sq P
  have hsum : P.A ^ (2 : ℕ) + P.B ^ (2 : ℕ) = 1 - P.C ^ (2 : ℕ) := by
    linarith [P.unitSphere]
  field_simp [ne_of_gt (cylindricalDenominator_pos P)]
  nlinarith [sq_nonneg P.C]

theorem radial_cross_azimuthal (P : RegularVerticalCoefficients) :
    frenetCross (radialInFrenet P) (azimuthalInFrenet P) =
      verticalInFrenet P := by
  rw [azimuthalInFrenet_eq]
  ext
  · simp [frenetCross, radialInFrenet, verticalInFrenet]
    field_simp [ne_of_gt (cylindricalDenominator_pos P)]
  · simp [frenetCross, radialInFrenet, verticalInFrenet]
    field_simp [ne_of_gt (cylindricalDenominator_pos P)]
  · simp [frenetCross, radialInFrenet, verticalInFrenet]
    have hden := cylindricalDenominator_sq P
    have hsum : P.A ^ (2 : ℕ) + P.B ^ (2 : ℕ) = 1 - P.C ^ (2 : ℕ) := by
      linarith [P.unitSphere]
    field_simp [ne_of_gt (cylindricalDenominator_pos P)]
    calc
      P.C * (P.B ^ (2 : ℕ) - -P.A ^ (2 : ℕ)) =
          P.C * (P.A ^ (2 : ℕ) + P.B ^ (2 : ℕ)) := by ring
      _ = P.C * (1 - P.C ^ (2 : ℕ)) := by rw [hsum]
      _ = cylindricalDenominator P ^ (2 : ℕ) * P.C := by rw [hden]; ring

/-- Equation (80): radial component of the unit tangent. -/
theorem tangent_radial_component (P : RegularVerticalCoefficients) :
    (radialInFrenet P).tangent = P.B / cylindricalDenominator P := rfl

/-- Equation (81): azimuthal component of the unit tangent. -/
theorem tangent_azimuthal_component (P : RegularVerticalCoefficients) :
    (azimuthalInFrenet P).tangent =
      P.A * P.C / cylindricalDenominator P := by
  rw [azimuthalInFrenet_eq]
  ring

/-- Equation (82): vertical component of the unit tangent. -/
theorem tangent_vertical_component_direct (P : RegularVerticalCoefficients) :
    (verticalInFrenet P).tangent = P.A := rfl

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
