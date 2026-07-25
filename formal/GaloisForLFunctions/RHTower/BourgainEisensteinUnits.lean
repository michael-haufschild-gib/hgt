/-
# Finiteness of Eisenstein units

Every unit has norm one, hence both coordinates lie in `[-1,1]`.  This
gives a finite unit type without assuming the usual six-unit
classification.  Finiteness is enough for the unique-factorization
divisor enumeration used in the parabola-fiber bound.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinEuclidean
import Mathlib.Data.Fintype.OfMap

namespace RHTower.BourgainEisensteinInt

/-- Every Eisenstein unit has norm one. -/
theorem norm_coe_unit (u : BourgainEisensteinIntˣ) :
    norm (u : BourgainEisensteinInt) = 1 := by
  have hmul :
      norm (u : BourgainEisensteinInt) *
          norm (↑u⁻¹ : BourgainEisensteinInt) = 1 := by
    rw [← norm_mul]
    simp
  have hu : 0 < norm (u : BourgainEisensteinInt) :=
    norm_pos.mpr (Units.ne_zero u)
  have huinv : 0 < norm (↑u⁻¹ : BourgainEisensteinInt) :=
    norm_pos.mpr (Units.ne_zero u⁻¹)
  nlinarith

/-- Coordinates of an Eisenstein unit lie in `[-1,1]`. -/
theorem coe_unit_coordinates_mem_Icc
    (u : BourgainEisensteinIntˣ) :
    (u.val.re ∈ Finset.Icc (-1 : ℤ) 1) ∧
      (u.val.im ∈ Finset.Icc (-1 : ℤ) 1) := by
  have hnorm := norm_coe_unit u
  have hfour := four_mul_norm u
  rw [hnorm] at hfour
  have himsq : u.val.im ^ (2 : ℕ) ≤ 1 := by
    nlinarith [sq_nonneg (2 * u.val.re - u.val.im)]
  have himlower : (-1 : ℤ) ≤ u.val.im := by
    nlinarith [sq_nonneg (u.val.im + 1)]
  have himupper : u.val.im ≤ 1 := by
    nlinarith [sq_nonneg (u.val.im - 1)]
  have hdiffsq :
      (2 * u.val.re - u.val.im) ^ (2 : ℕ) ≤ 4 := by
    nlinarith [sq_nonneg u.val.im]
  have hdiffLower : (-2 : ℤ) ≤ 2 * u.val.re - u.val.im := by
    nlinarith [sq_nonneg (2 * u.val.re - u.val.im + 2)]
  have hdiffUpper : 2 * u.val.re - u.val.im ≤ 2 := by
    nlinarith [sq_nonneg (2 * u.val.re - u.val.im - 2)]
  rw [Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · constructor <;> omega
  · exact ⟨himlower, himupper⟩

/-- Coordinate code of a unit into the fixed `3 × 3` box. -/
noncomputable def unitBoxCode
    (u : BourgainEisensteinIntˣ) :
    {z : ℤ // z ∈ Finset.Icc (-1 : ℤ) 1} ×
      {z : ℤ // z ∈ Finset.Icc (-1 : ℤ) 1} :=
  (⟨u.val.re, (coe_unit_coordinates_mem_Icc u).1⟩,
    ⟨u.val.im, (coe_unit_coordinates_mem_Icc u).2⟩)

theorem unitBoxCode_injective :
    Function.Injective unitBoxCode := by
  intro u v h
  apply Units.ext
  apply BourgainEisensteinInt.ext
  · exact congrArg (fun z => z.1.1) h
  · exact congrArg (fun z => z.2.1) h

/-- Eisenstein units form a finite type. -/
noncomputable instance instFintypeUnits :
    Fintype BourgainEisensteinIntˣ :=
  Fintype.ofInjective unitBoxCode unitBoxCode_injective

end RHTower.BourgainEisensteinInt
