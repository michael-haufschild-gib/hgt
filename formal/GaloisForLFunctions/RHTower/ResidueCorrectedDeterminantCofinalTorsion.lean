import Mathlib

/-!
# Residue-corrected determinant cofinal torsion: exact finite algebra

This module formalizes algebraic layer of residue-corrected determinant character.
For finite atom set P, residueMass is primary zeta residue factor and residueFinitePart is
finite part at critical pole. Main results are exact one-atom update, affine finite-part
transport, cleared determinant excision, determinant-cluster germ factorization, and
relative-torsion cocycle.

Analytic Mertens limits and cofinal realization are deliberately separate modules.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Primary residue factor after removing finite atom set. -/
def residueMass {ι : Type*} (q : ι → ℝ) (P : Finset ι) : ℝ :=
  ∏ v ∈ P, (1 - (q v)⁻¹)

/-- Bracketed finite-part coordinate before multiplication by primary residue. -/
def residueFinitePartBase {ι : Type*} (γ₀ : ℝ) (q : ι → ℝ)
    (P : Finset ι) : ℝ :=
  γ₀ + ∑ v ∈ P, Real.log (q v) / (q v - 1)

/-- Unnormalized finite part of critical zeta pole. -/
def residueFinitePart {ι : Type*} (ρ γ₀ : ℝ) (q : ι → ℝ)
    (P : Finset ι) : ℝ :=
  ρ * residueMass q P * residueFinitePartBase γ₀ q P

theorem residueMass_empty {ι : Type*} (q : ι → ℝ) :
    residueMass q ∅ = 1 := by
  simp [residueMass]

theorem residueFinitePartBase_empty {ι : Type*} (γ₀ : ℝ) (q : ι → ℝ) :
    residueFinitePartBase γ₀ q ∅ = γ₀ := by
  simp [residueFinitePartBase]

theorem residueMass_insert {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (P : Finset ι) {v : ι} (hv : v ∉ P) :
    residueMass q (insert v P) =
      residueMass q P * (1 - (q v)⁻¹) := by
  simp [residueMass, hv, mul_comm]

theorem residueFinitePartBase_insert {ι : Type*} [DecidableEq ι]
    (γ₀ : ℝ) (q : ι → ℝ) (P : Finset ι) {v : ι} (hv : v ∉ P) :
    residueFinitePartBase γ₀ q (insert v P) =
      residueFinitePartBase γ₀ q P + Real.log (q v) / (q v - 1) := by
  simp [residueFinitePartBase, hv, add_comm, add_left_comm]

/-- Every finite primary residue factor is positive when atom heights exceed one. -/
theorem residueMass_pos {ι : Type*} (q : ι → ℝ) (P : Finset ι)
    (hq : ∀ v ∈ P, 1 < q v) :
    0 < residueMass q P := by
  rw [residueMass]
  apply Finset.prod_pos
  intro v hv
  have hqv : 0 < q v := lt_trans zero_lt_one (hq v hv)
  exact sub_pos.mpr ((inv_lt_one₀ hqv).2 (hq v hv))

/-- Exact one-atom finite-part update. -/
theorem residueFinitePart_insert_sub {ι : Type*} [DecidableEq ι]
    (ρ γ₀ : ℝ) (q : ι → ℝ) (P : Finset ι) {v : ι}
    (hv : v ∉ P) (hq : 1 < q v) :
    residueFinitePart ρ γ₀ q (insert v P) - residueFinitePart ρ γ₀ q P =
      ρ * residueMass q P / q v *
        (Real.log (q v) - residueFinitePartBase γ₀ q P) := by
  unfold residueFinitePart
  rw [residueMass_insert q P hv,
    residueFinitePartBase_insert γ₀ q P hv]
  have hq0 : q v ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  have hq1 : q v - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  rw [inv_eq_one_div]
  field_simp
  ring

/-- Affine form of one-atom update, used by determinant excision. -/
theorem residueFinitePart_insert_affine {ι : Type*} [DecidableEq ι]
    (ρ γ₀ : ℝ) (q : ι → ℝ) (P : Finset ι) {v : ι}
    (hv : v ∉ P) (hq : 1 < q v) :
    residueFinitePart ρ γ₀ q (insert v P) =
      (1 - 1 / q v) * residueFinitePart ρ γ₀ q P +
        ρ * residueMass q P * Real.log (q v) / q v := by
  unfold residueFinitePart
  rw [residueMass_insert q P hv,
    residueFinitePartBase_insert γ₀ q P hv]
  have hq0 : q v ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  have hq1 : q v - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  rw [inv_eq_one_div]
  field_simp

/-- Insertion raises finite part exactly when atom log-height exceeds current base coordinate. -/
theorem residueFinitePart_insert_lt_iff {ι : Type*} [DecidableEq ι]
    (ρ γ₀ : ℝ) (q : ι → ℝ) (P : Finset ι) {v : ι}
    (hρ : 0 < ρ) (hP : ∀ w ∈ P, 1 < q w) (hv : v ∉ P) (hq : 1 < q v) :
    residueFinitePart ρ γ₀ q P <
        residueFinitePart ρ γ₀ q (insert v P) ↔
      residueFinitePartBase γ₀ q P < Real.log (q v) := by
  rw [← sub_pos, residueFinitePart_insert_sub ρ γ₀ q P hv hq]
  have hmass : 0 < residueMass q P := residueMass_pos q P hP
  have hq0 : 0 < q v := lt_trans (by norm_num) hq
  have hcoef : 0 < ρ * residueMass q P / q v := div_pos (mul_pos hρ hmass) hq0
  exact (mul_pos_iff_of_pos_left hcoef).trans sub_pos

/-- Residue-corrected determinant built from finite part and divisor-carrying core. -/
def residueCorrectedDeterminant (κ : ℂ) (core : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-κ * z) * core z

/--
Cleared one-atom excision.  This is the global entire identity, so it remains meaningful at
common zeros of the determinant sections.  Parameter `u` is inverse atom height and `corr` is
the residue-logarithm correction.
-/
theorem residueCorrectedDeterminant_excision
    (κ u corr : ℂ) (core coreNew : ℂ → ℂ)
    (hcore : ∀ z, coreNew z * core (u * z) = core z) (z : ℂ) :
    Complex.exp (corr * z) *
          residueCorrectedDeterminant ((1 - u) * κ + corr) coreNew z *
      residueCorrectedDeterminant κ core (u * z) =
      residueCorrectedDeterminant κ core z := by
  simp only [residueCorrectedDeterminant]
  calc
    _ = Complex.exp
          (corr * z + (-((1 - u) * κ + corr) * z) + (-κ * (u * z))) *
          (coreNew z * core (u * z)) := by
      rw [Complex.exp_add, Complex.exp_add]
      ring
    _ = Complex.exp (-κ * z) * core z := by
      rw [hcore z]
      congr 1
      ring

/-- Limiting residue-corrected determinant germ with finite-part coordinate c. -/
def residueDeterminantClusterGerm (c z : ℂ) : ℂ :=
  Complex.exp ((1 - c) * z) * (-z + 1)

/-- Canonically divisor-cancelled relative determinant torsion. -/
def residueRelativeDeterminantTorsion (c d z : ℂ) : ℂ :=
  Complex.exp ((d - c) * z)

/-- Relative torsion factors determinant germs everywhere, including common zero z = 1. -/
theorem residueDeterminantClusterGerm_eq_torsion_mul
    (c d z : ℂ) :
    residueDeterminantClusterGerm c z =
      residueRelativeDeterminantTorsion c d z *
        residueDeterminantClusterGerm d z := by
  rw [residueDeterminantClusterGerm, residueRelativeDeterminantTorsion,
    residueDeterminantClusterGerm, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Relative determinant torsions form exact pair-groupoid cocycle. -/
theorem residueRelativeDeterminantTorsion_cocycle
    (c d e z : ℂ) :
    residueRelativeDeterminantTorsion c d z *
        residueRelativeDeterminantTorsion d e z =
      residueRelativeDeterminantTorsion c e z := by
  rw [residueRelativeDeterminantTorsion, residueRelativeDeterminantTorsion,
    residueRelativeDeterminantTorsion, ← Complex.exp_add]
  congr 1
  ring

theorem residueRelativeDeterminantTorsion_self (c z : ℂ) :
    residueRelativeDeterminantTorsion c c z = 1 := by
  simp [residueRelativeDeterminantTorsion]

theorem residueRelativeDeterminantTorsion_ne_zero (c d z : ℂ) :
    residueRelativeDeterminantTorsion c d z ≠ 0 :=
  Complex.exp_ne_zero _

theorem residueDeterminantClusterGerm_one (c : ℂ) :
    residueDeterminantClusterGerm c 1 = 0 := by
  simp [residueDeterminantClusterGerm]

/-- First derivative at origin recovers finite-part coordinate exactly. -/
theorem residueDeterminantClusterGerm_hasDerivAt_zero (c : ℂ) :
    HasDerivAt (residueDeterminantClusterGerm c) (-c) 0 := by
  have hlin : HasDerivAt (fun z : ℂ => (1 - c) * z) (1 - c) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (1 - c)
  have hhead :
      HasDerivAt (fun z : ℂ => Complex.exp ((1 - c) * z)) (1 - c) 0 := by
    simpa only [mul_zero, Complex.exp_zero, one_mul] using hlin.cexp
  have htail : HasDerivAt (fun z : ℂ => -z + 1) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).neg.add_const (1 : ℂ)
  change HasDerivAt
    (fun z : ℂ => Complex.exp ((1 - c) * z) * (-z + 1)) (-c) 0
  apply (hhead.mul htail).congr_deriv
  simp only [mul_zero, Complex.exp_zero, one_mul]
  ring

/-- Determinant cluster germ parameterization is injective. -/
theorem residueDeterminantClusterGerm_injective :
    Function.Injective residueDeterminantClusterGerm := by
  intro c d h
  have hc := (residueDeterminantClusterGerm_hasDerivAt_zero c).deriv
  have hd := (residueDeterminantClusterGerm_hasDerivAt_zero d).deriv
  rw [h] at hc
  rw [hc] at hd
  simpa using neg_inj.mp hd

end RHTower
