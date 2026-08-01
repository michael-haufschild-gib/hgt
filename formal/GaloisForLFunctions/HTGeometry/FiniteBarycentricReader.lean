import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Finite weighted-barycentric readers

An exact weighted-barycentric packet reader is the projectivization of an additive marked
current.  Multiplication by the total mass recovers that current, so a positive barycentric
normalization preserves scalar zero loci and signs.  This is the reusable algebraic classification
needed by the edge-marked Gamma--Jacobi reader.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total mass of a finite marked packet. -/
def finiteBarycentricTotalMass
    {E : Type*} (edges : Finset E) (mass : E → ℝ) : ℝ :=
  ∑ e ∈ edges, mass e

/-- Additive mass-weighted current carried by a finite marked packet. -/
def finiteBarycentricCurrent
    {E V : Type*} [AddCommMonoid V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V) : V :=
  ∑ e ∈ edges, mass e • value e

/-- Normalized weighted-barycentric reader of a finite marked packet. -/
def finiteBarycentricReader
    {E V : Type*} [AddCommMonoid V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V) : V :=
  (finiteBarycentricTotalMass edges mass)⁻¹ •
    finiteBarycentricCurrent edges mass value

/-- **Dehomogenization law.**  Multiplication by nonzero total mass recovers the additive marked
current exactly. -/
theorem finiteBarycentricTotalMass_smul_reader
    {E V : Type*} [AddCommMonoid V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V)
    (htotal : finiteBarycentricTotalMass edges mass ≠ 0) :
    finiteBarycentricTotalMass edges mass •
        finiteBarycentricReader edges mass value =
      finiteBarycentricCurrent edges mass value := by
  rw [finiteBarycentricReader, smul_smul,
    mul_inv_cancel₀ htotal, one_smul]

/-- Exact converse classification: a proposed packet value is the barycentric reader exactly
when its mass-weighted lift is the additive marked current. -/
theorem finiteBarycentricReader_eq_iff_totalMass_smul_eq_current
    {E V : Type*} [AddCommMonoid V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V) (v : V)
    (htotal : finiteBarycentricTotalMass edges mass ≠ 0) :
    finiteBarycentricReader edges mass value = v ↔
      finiteBarycentricTotalMass edges mass • v =
        finiteBarycentricCurrent edges mass value := by
  constructor
  · intro h
    rw [← h]
    exact finiteBarycentricTotalMass_smul_reader edges mass value htotal
  · intro h
    rw [finiteBarycentricReader, ← h, smul_smul,
      inv_mul_cancel₀ htotal, one_smul]

/-- A nonzero normalization cannot create or remove a zero of the additive current. -/
theorem finiteBarycentricReader_eq_zero_iff_current_eq_zero
    {E V : Type*} [AddCommMonoid V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V)
    (htotal : finiteBarycentricTotalMass edges mass ≠ 0) :
    finiteBarycentricReader edges mass value = 0 ↔
      finiteBarycentricCurrent edges mass value = 0 := by
  rw [finiteBarycentricReader]
  exact smul_eq_zero.trans (or_iff_right (inv_ne_zero htotal))

/-- Linear observation commutes with finite barycentric normalization. -/
theorem LinearMap.map_finiteBarycentricReader
    {E V W : Type*} [AddCommMonoid V] [Module ℝ V]
    [AddCommMonoid W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (edges : Finset E) (mass : E → ℝ) (value : E → V) :
    L (finiteBarycentricReader edges mass value) =
      finiteBarycentricReader edges mass (fun e => L (value e)) := by
  simp only [finiteBarycentricReader, finiteBarycentricCurrent,
    map_smul, map_sum]

/-- Negating every marked value negates the packet reader. -/
theorem finiteBarycentricReader_neg
    {E V : Type*} [AddCommGroup V] [Module ℝ V]
    (edges : Finset E) (mass : E → ℝ) (value : E → V) :
    finiteBarycentricReader edges mass (fun e => -value e) =
      -finiteBarycentricReader edges mass value := by
  simp [finiteBarycentricReader, finiteBarycentricCurrent,
    smul_neg, Finset.sum_neg_distrib]

/-- Positive normalization preserves strict positivity of a real additive current. -/
theorem finiteBarycentricReader_pos_iff_current_pos
    {E : Type*} (edges : Finset E) (mass value : E → ℝ)
    (htotal : 0 < finiteBarycentricTotalMass edges mass) :
    0 < finiteBarycentricReader edges mass value ↔
      0 < finiteBarycentricCurrent edges mass value := by
  rw [finiteBarycentricReader]
  exact smul_pos_iff_of_pos_left (inv_pos.mpr htotal)

/-- Positive normalization preserves strict negativity of a real additive current. -/
theorem finiteBarycentricReader_neg_iff_current_neg
    {E : Type*} (edges : Finset E) (mass value : E → ℝ)
    (htotal : 0 < finiteBarycentricTotalMass edges mass) :
    finiteBarycentricReader edges mass value < 0 ↔
      finiteBarycentricCurrent edges mass value < 0 := by
  rw [finiteBarycentricReader]
  exact smul_neg_iff_of_pos_left (inv_pos.mpr htotal)

end

end GaloisForLFunctions.HTGeometry
