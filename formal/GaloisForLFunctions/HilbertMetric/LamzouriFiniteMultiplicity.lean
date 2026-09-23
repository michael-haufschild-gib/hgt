import Mathlib

/-!
# Finite multiplicity inequalities behind Lamzouri's simple-zero bounds

The diagonal bookkeeping in Lamzouri's pair-correlation argument depends only
on a finite support and its natural-number multiplicities.  This module isolates
that source-independent layer.  It proves Montgomery's simple-point inequality,
the corresponding distinct-support inequality, the diagonal energy floor, and
the three scalar quadratic minorants used in the Hilbert-space proof.

Every result is unconditional: zero multiplicities are handled by filtering the
positive support, while positive and simple supports are defined intrinsically.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Total multiplicity of a finite packet. -/
def finiteMultiplicityMass {ι : Type*} (s : Finset ι) (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (m i : ℝ)

/-- Diagonal collision energy of a finite multiplicity packet. -/
def finiteMultiplicityCollisionMass {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ)

/-- Points occurring exactly once in a finite multiplicity packet. -/
def finiteSimpleMultiplicitySupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) : Finset ι :=
  s.filter fun i => m i = 1

/-- Points occurring with positive multiplicity in a finite packet. -/
def finitePositiveMultiplicitySupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) : Finset ι :=
  s.filter fun i => 0 < m i

/-- Montgomery's diagonal inequality: simple support dominates twice total
multiplicity minus diagonal collision energy. -/
theorem finiteSimpleMultiplicitySupport_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) :
    2 * finiteMultiplicityMass s m - finiteMultiplicityCollisionMass s m ≤
      ((finiteSimpleMultiplicitySupport s m).card : ℝ) := by
  unfold finiteMultiplicityMass finiteMultiplicityCollisionMass
    finiteSimpleMultiplicitySupport
  rw [show ((s.filter fun i => m i = 1).card : ℝ) =
      ∑ i ∈ s, if m i = 1 then (1 : ℝ) else 0 by simp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : m i = 1
  · norm_num [h]
  · rw [if_neg h]
    have hm : m i = 0 ∨ 2 ≤ m i := by omega
    rcases hm with hm | hm
    · simp [hm]
    · have hm' : (2 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm
      norm_num
      nlinarith [sq_nonneg ((m i : ℝ) - 2)]

/-- Positive support dominates the rank--trace expression
`(3/2) mass - (1/2) collision`.  When every listed point has positive
multiplicity, this is the distinct-point bound from Proposition 2.1. -/
theorem finitePositiveMultiplicitySupport_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) :
    (3 / 2 : ℝ) * finiteMultiplicityMass s m -
        (1 / 2 : ℝ) * finiteMultiplicityCollisionMass s m ≤
      ((finitePositiveMultiplicitySupport s m).card : ℝ) := by
  unfold finiteMultiplicityMass finiteMultiplicityCollisionMass
    finitePositiveMultiplicitySupport
  rw [show ((s.filter fun i => 0 < m i).card : ℝ) =
      ∑ i ∈ s, if 0 < m i then (1 : ℝ) else 0 by simp]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : m i = 0
  · simp [h0]
  · have hpos : 0 < m i := Nat.pos_of_ne_zero h0
    rw [if_pos hpos]
    rcases Nat.lt_or_ge (m i) 3 with hlt | hge
    · interval_cases hmi : m i <;> norm_num
    · have hge' : (3 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hge
      nlinarith [sq_nonneg ((m i : ℝ) - 3)]

/-- Every positive integer multiplicity contributes at least its mass to the
diagonal collision energy. -/
theorem finiteMultiplicityMass_le_collisionMass {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) :
    finiteMultiplicityMass s m ≤ finiteMultiplicityCollisionMass s m := by
  unfold finiteMultiplicityMass finiteMultiplicityCollisionMass
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : m i = 0
  · simp [h0]
  · have hm : (1 : ℝ) ≤ (m i : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hprod : 0 ≤ (m i : ℝ) * ((m i : ℝ) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hm)
    nlinarith

/-- All-real specialization of the simple-plus-real inequality: simple
support plus total mass dominates three masses minus collision energy. -/
theorem finiteSimpleMultiplicitySupport_add_mass_lower
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) :
    3 * finiteMultiplicityMass s m - finiteMultiplicityCollisionMass s m ≤
      ((finiteSimpleMultiplicitySupport s m).card : ℝ) +
        finiteMultiplicityMass s m := by
  have h := finiteSimpleMultiplicitySupport_lower s m
  linarith

/-- Tangent-line lower bound for a square, used with the free parameter in
the simple-or-real estimate. -/
theorem lamzouriQuadratic_affineMinorant (a t : ℝ) :
    2 * a * t - t ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by
  nlinarith [sq_nonneg (a - t)]

/-- The `t = 2` scalar inequality used on the first Hilbert range. -/
theorem lamzouriQuadratic_twoMinorant (a : ℝ) : 4 * a - 4 ≤ a ^ (2 : ℕ) := by
  nlinarith [lamzouriQuadratic_affineMinorant a 2]

/-- The `t = 1` scalar inequality used on the middle Hilbert range. -/
theorem lamzouriQuadratic_oneMinorant (a : ℝ) : 2 * a - 1 ≤ a ^ (2 : ℕ) := by
  nlinarith [lamzouriQuadratic_affineMinorant a 1]

end

end GaloisForLFunctions.HilbertMetric
