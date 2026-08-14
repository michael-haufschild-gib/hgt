import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators

/-!
# Exact Parseval identity for products of cyclic residue groups

Finite-stage nonarchimedean Fourier analysis reduces simultaneously to a
finite product of cyclic prime-power quotients.  This file proves the exact
orthogonality and Parseval identities for that dependent product directly
from one-coordinate character orthogonality.  No Fourier isometry is used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Finset AddChar ZMod
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (N : ι → ℕ) [∀ i, NeZero (N i)]

/-- Product of cyclic residue groups with coordinate moduli `N i`. -/
abbrev FieldOneFiniteCyclicProduct := ∀ i, ZMod (N i)

/-- Canonical self-dual character kernel on a product of cyclic groups. -/
def fieldOneFiniteCyclicProductCharacter
    (j k : FieldOneFiniteCyclicProduct N) : ℂ :=
  ∏ i, ZMod.stdAddChar (-(j i * k i))

/-- Literal unnormalized DFT on a product of cyclic residue groups. -/
def fieldOneFiniteCyclicProductDFT
    (f : FieldOneFiniteCyclicProduct N → ℂ)
    (k : FieldOneFiniteCyclicProduct N) : ℂ :=
  ∑ j, fieldOneFiniteCyclicProductCharacter N j k * f j

/-- Exact orthogonality of the canonical characters of a product of cyclic
groups. -/
theorem fieldOneFiniteCyclicProductFourier_orthogonality
    (j l : FieldOneFiniteCyclicProduct N) :
    ∑ k,
        star (fieldOneFiniteCyclicProductCharacter N j k) *
          fieldOneFiniteCyclicProductCharacter N l k =
      if j = l then (∏ i, N i : ℕ) else 0 := by
  have hfactor :
      (∑ k,
          star (fieldOneFiniteCyclicProductCharacter N j k) *
            fieldOneFiniteCyclicProductCharacter N l k) =
        ∑ k : FieldOneFiniteCyclicProduct N,
          ∏ i, (star (ZMod.stdAddChar (-(j i * k i))) *
            ZMod.stdAddChar (-(l i * k i))) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [fieldOneFiniteCyclicProductCharacter, star_prod]
    rw [← Finset.prod_mul_distrib]
  rw [hfactor]
  calc
    (∑ k : FieldOneFiniteCyclicProduct N,
        ∏ i, (star (ZMod.stdAddChar (-(j i * k i))) *
          ZMod.stdAddChar (-(l i * k i)))) =
        ∏ i, ∑ k : ZMod (N i),
          (star (ZMod.stdAddChar (-(j i * k))) *
            ZMod.stdAddChar (-(l i * k))) :=
      (Fintype.prod_sum fun i k =>
        star (ZMod.stdAddChar (-(j i * k))) *
          ZMod.stdAddChar (-(l i * k))).symm
    _ = _ := by
      simp_rw [fieldOneFiniteCyclicFourier_orthogonality]
      by_cases h : j = l
      · subst l
        simp
      · have hex : ∃ i, j i ≠ l i := by
          by_contra hall
          apply h
          funext i
          exact not_ne_iff.mp (not_exists.mp hall i)
        obtain ⟨i, hi⟩ := hex
        simp [h, Finset.prod_eq_zero (Finset.mem_univ i), hi]

/-- Unnormalized Parseval identity on a product of cyclic residue groups.
The exact factor is the product cardinality. -/
theorem fieldOneFiniteCyclicProductFourier_parseval
    (f : FieldOneFiniteCyclicProduct N → ℂ) :
    ∑ k, Complex.normSq (fieldOneFiniteCyclicProductDFT N f k) =
      (∏ i, N i : ℕ) * ∑ j, Complex.normSq (f j) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [fieldOneFiniteCyclicProductDFT, map_sum,
    starRingEnd_apply, star_mul, Finset.sum_mul, Finset.mul_sum]
  let T : FieldOneFiniteCyclicProduct N →
      FieldOneFiniteCyclicProduct N →
      FieldOneFiniteCyclicProduct N → ℂ := fun k l j =>
    star (f j) *
      star (fieldOneFiniteCyclicProductCharacter N j k) *
      (fieldOneFiniteCyclicProductCharacter N l k * f l)
  change (∑ k, ∑ l, ∑ j, T k l j) = _
  calc
    _ = ∑ k, ∑ j, ∑ l, T k l j := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, T k l j := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, T k l j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j, ∑ l, (star (f j) * f l) *
          ∑ k,
            star (fieldOneFiniteCyclicProductCharacter N j k) *
              fieldOneFiniteCyclicProductCharacter N l k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [T]
      ring
    _ = ∑ j, ∑ l, (star (f j) * f l) *
          (if j = l then ((∏ i, N i : ℕ) : ℂ) else 0) := by
      simp_rw [fieldOneFiniteCyclicProductFourier_orthogonality N]
      simp only [Nat.cast_ite, Nat.cast_zero]
    _ = ∑ j,
        ((∏ i, (N i : ℂ)) * (star (f j) * f j)) := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      simp
      ring

/-- Parseval identity for the probability-normalized product DFT. -/
theorem fieldOneFiniteCyclicProductFourier_normalized_parseval
    (f : FieldOneFiniteCyclicProduct N → ℂ) :
    ∑ k, Complex.normSq
        ((((∏ i, N i : ℕ) : ℂ)⁻¹) *
          fieldOneFiniteCyclicProductDFT N f k) =
      (((∏ i, N i : ℕ) : ℝ)⁻¹) *
        ∑ j, Complex.normSq (f j) := by
  simp_rw [Complex.normSq_mul]
  rw [← Finset.mul_sum]
  rw [fieldOneFiniteCyclicProductFourier_parseval]
  simp only [map_inv₀, Complex.normSq_natCast]
  have hPN : (∏ i, N i : ℕ) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (N i)
  have hPR : ((∏ i, N i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hPN
  field_simp

end

end GaloisForLFunctions.RHTower
