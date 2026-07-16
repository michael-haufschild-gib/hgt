import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase
import GaloisForLFunctions.HTGeometry.RelativeLogCharacteristicArrangement
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Physical characteristic incidence

This module compares three levels of the multiple-Gamma source constraint without using any
special-function identity:

* a coface sequence whose physical factors are one parameter times units generates exactly the
  `r`-fold principal fat-point ideal;
* actual source translation defects diagonalize on exponential modes with the same coface symbols
  as the DA logarithmic characteristic arrangement;
* for a rationally independent source frame, the common physical degeneracy spectrum is exactly
  the central character.

The unit-scaled ideal theorem also isolates an orientation no-go: the unframed fat point forgets
all unit phases.  Orientation therefore has to live in a source-labelled framing or polarization,
not in the underlying ideal.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def unitScaledCofaceGenerator
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) : R :=
  ∏ j ∈ Finset.univ.erase i, a * (u j : R)

theorem unitScaledCofaceGenerator_eq_pow_mul_unit
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) :
    unitScaledCofaceGenerator r a u i =
      a ^ r * (∏ j ∈ Finset.univ.erase i, (u j : R)) := by
  rw [unitScaledCofaceGenerator, Finset.prod_mul_distrib]
  have hcard : (Finset.univ.erase i).card = r := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  rw [Finset.prod_const, hcard]

def unitScaledCofaceIdeal
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) : Ideal R :=
  Ideal.span (Set.range (unitScaledCofaceGenerator r a u))

/-- A one-parameter pullback whose source factors are the parameter times units has exactly the
principal `r`-fold fat-point ideal. -/
theorem unitScaledCofaceIdeal_eq_span_pow
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    unitScaledCofaceIdeal r a u = Ideal.span ({a ^ r} : Set R) := by
  apply le_antisymm
  · rw [unitScaledCofaceIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [unitScaledCofaceGenerator_eq_pow_mul_unit]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    let i : Fin (r + 1) := ⟨0, Nat.succ_pos r⟩
    let U : Rˣ := ∏ j ∈ Finset.univ.erase i, u j
    have hgen : unitScaledCofaceGenerator r a u i ∈
        unitScaledCofaceIdeal r a u :=
      Ideal.subset_span (Set.mem_range_self i)
    rw [unitScaledCofaceGenerator_eq_pow_mul_unit] at hgen
    have hcoe : (U : R) = ∏ j ∈ Finset.univ.erase i, (u j : R) := by
      exact Units.coe_prod u (Finset.univ.erase i)
    rw [← hcoe] at hgen
    have hcancel := (unitScaledCofaceIdeal r a u).mul_mem_left (↑(U⁻¹)) hgen
    simpa [U, mul_assoc, mul_comm, mul_left_comm] using hcancel

/-- The unit multiplying `a^r` in one pulled-back coface generator. -/
def unitScaledCofaceUnit
    {R : Type*} [CommRing R] (r : ℕ)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) : Rˣ :=
  ∏ j ∈ Finset.univ.erase i, u j

theorem unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) :
    unitScaledCofaceGenerator r a u i =
      a ^ r * (unitScaledCofaceUnit r u i : R) := by
  rw [unitScaledCofaceGenerator_eq_pow_mul_unit]
  congr 1
  exact (Units.coe_prod u (Finset.univ.erase i)).symm

/-- Scale every coface by its unit inverse and subtract the zeroth row from the others. -/
def unitScaledCofaceRowReduce
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ if i = 0 then
      (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) * v 0
    else
      (↑((unitScaledCofaceUnit r u i)⁻¹) : R) * v i -
        (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) * v 0

/-- The explicit inverse row operation. -/
def unitScaledCofaceRowRestore
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ (unitScaledCofaceUnit r u i : R) *
    (if i = 0 then v 0 else v i + v 0)

/-- The pulled-back coface row operations form an invertible linear change of generators. -/
def unitScaledCofaceRowEquiv
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ) :
    (Fin (r + 1) → R) ≃ₗ[R] (Fin (r + 1) → R) where
  toFun := unitScaledCofaceRowReduce r u
  invFun := unitScaledCofaceRowRestore r u
  map_add' v w := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, hi] <;> ring
  map_smul' c v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, hi, smul_eq_mul] <;> ring
  left_inv v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, unitScaledCofaceRowRestore, hi]
  right_inv v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, unitScaledCofaceRowRestore, hi]

/-- Explicit row reduction of the physical coface sequence to `(a^r, 0, ..., 0)`. -/
theorem unitScaledCofaceRowEquiv_generators
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    unitScaledCofaceRowEquiv r u (unitScaledCofaceGenerator r a u) =
      fun i ↦ if i = 0 then a ^ r else 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [unitScaledCofaceRowEquiv, unitScaledCofaceRowReduce,
      unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit,
      mul_assoc, mul_comm]
  · simp [unitScaledCofaceRowEquiv, unitScaledCofaceRowReduce, hi,
      unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit,
      mul_assoc, mul_comm]

/-- Translation defect on a complex-valued mode. -/
def physicalTranslationDefect (tau : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ f (z + tau) - f z

/-- The exponential mode on which translation defects diagonalize. -/
def physicalExponentialMode (lambda : ℂ) : ℂ → ℂ :=
  fun z ↦ Complex.exp (lambda * z)

theorem physicalExponentialMode_add (lambda tau z : ℂ) :
    physicalExponentialMode lambda (z + tau) =
      Complex.exp (lambda * tau) * physicalExponentialMode lambda z := by
  rw [physicalExponentialMode]
  rw [show lambda * (z + tau) = lambda * tau + lambda * z by ring]
  exact Complex.exp_add _ _

/-- Exponential modes diagonalize each physical source defect. -/
theorem physicalTranslationDefect_exponentialMode
    (lambda tau z : ℂ) :
    physicalTranslationDefect tau (physicalExponentialMode lambda) z =
      (Complex.exp (lambda * tau) - 1) * physicalExponentialMode lambda z := by
  rw [physicalTranslationDefect, physicalExponentialMode_add]
  ring

/-- An ordered product of source defects.  The order is immaterial on translations, but retaining
it makes the principal-symbol computation independent of a separate operator algebra. -/
def iteratedPhysicalTranslationDefect
    {ι : Type*} (tau : ι → ℂ) : List ι → (ℂ → ℂ) → (ℂ → ℂ)
  | [], f => f
  | i :: indices, f =>
      physicalTranslationDefect (tau i)
        (iteratedPhysicalTranslationDefect tau indices f)

/-- The complete iterated boundary diagonalizes with the product of its source characters. -/
theorem iteratedPhysicalTranslationDefect_exponentialMode
    {ι : Type*} (tau : ι → ℂ) (indices : List ι) (lambda z : ℂ) :
    iteratedPhysicalTranslationDefect tau indices
        (physicalExponentialMode lambda) z =
      (indices.map (fun i ↦ Complex.exp (lambda * tau i) - 1)).prod *
        physicalExponentialMode lambda z := by
  induction indices generalizing z with
  | nil => simp [iteratedPhysicalTranslationDefect]
  | cons i indices ih =>
      simp only [iteratedPhysicalTranslationDefect, physicalTranslationDefect, ih,
        List.map_cons, List.prod_cons]
      rw [physicalExponentialMode_add]
      ring

/-- The scalar physical symbol of one coface of the DA-relative source ideal. -/
def physicalCofaceSymbol
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (Complex.exp (lambda * tau j) - 1)

/-- The corresponding coface product of actual source translation defects on an exponential
mode. -/
def physicalCofaceBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) : ℂ → ℂ :=
  iteratedPhysicalTranslationDefect tau (Finset.univ.erase i).toList
    (physicalExponentialMode lambda)

/-- The physical one-parameter logarithmic clock cut out by the structural periods. -/
def physicalLogarithmicClock
    {r : ℕ} (tau : Fin (r + 1) → ℂ) (lambda : ℂ) :
    Fin (r + 1) → ℂ :=
  fun j ↦ lambda * tau j

theorem physicalCofaceBoundary_apply
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda z : ℂ)
    (i : Fin (r + 1)) :
    physicalCofaceBoundary r tau lambda i z =
      physicalCofaceSymbol r tau lambda i * physicalExponentialMode lambda z := by
  simpa [physicalCofaceBoundary, physicalCofaceSymbol] using
    iteratedPhysicalTranslationDefect_exponentialMode tau
      (Finset.univ.erase i).toList lambda z

/-- A coface boundary kills the exponential mode exactly when its scalar source symbol vanishes. -/
theorem physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) :
    physicalCofaceBoundary r tau lambda i = 0 ↔
      physicalCofaceSymbol r tau lambda i = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [physicalCofaceBoundary_apply] at h0
    simpa [physicalExponentialMode] using h0
  · intro h
    funext z
    rw [physicalCofaceBoundary_apply, h, zero_mul]
    rfl

/-- The DA logarithmic characteristic boundary and the actual source-translation boundary have
the same restriction to the physical exponential family. -/
theorem multipleGammaPhysicalLogCharacteristicBoundary_iff_sourceBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ) :
    MultipleGammaLogCharacteristicBoundary r
        (physicalLogarithmicClock tau lambda) ↔
      ∀ i : Fin (r + 1), physicalCofaceBoundary r tau lambda i = 0 := by
  change (∀ i : Fin (r + 1), physicalCofaceSymbol r tau lambda i = 0) ↔ _
  constructor
  · intro h i
    exact (physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero r tau lambda i).2 (h i)
  · intro h i
    exact (physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero r tau lambda i).1 (h i)

/-- Two rationally independent periods have no common nonzero holomorphic exponential
resonance. -/
theorem exp_mul_pair_eq_one_eq_one_iff_of_linearIndependent
    (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v) (lambda : ℂ) :
    (Complex.exp (lambda * v 0) = 1 ∧
      Complex.exp (lambda * v 1) = 1) ↔ lambda = 0 := by
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h0
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    by_cases hlambda : lambda = 0
    · exact hlambda
    have hcross : (n : ℂ) * v 0 = (m : ℂ) * v 1 := by
      apply mul_left_cancel₀ hlambda
      calc
        lambda * ((n : ℂ) * v 0) = (n : ℂ) * (lambda * v 0) := by ring
        _ = (n : ℂ) * ((m : ℂ) * (2 * Real.pi * I)) := by rw [hm]
        _ = (m : ℂ) * ((n : ℂ) * (2 * Real.pi * I)) := by ring
        _ = (m : ℂ) * (lambda * v 1) := by rw [hn]
        _ = lambda * ((m : ℂ) * v 1) := by ring
    have hcomb : ∑ i,
        (![((n : ℤ) : ℚ), -((m : ℤ) : ℚ)] : Fin 2 → ℚ) i • v i = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def]
      push_cast
      simpa [sub_eq_add_neg] using sub_eq_zero.mpr hcross
    have hz := Fintype.linearIndependent_iff.mp hv _ hcomb
    have hnQ : ((n : ℤ) : ℚ) = 0 := hz 0
    have hnZ : n = 0 := by exact_mod_cast hnQ
    have hnzero : lambda * v 1 = 0 := by simpa [hnZ] using hn
    exact (mul_eq_zero.mp hnzero).resolve_right
      ((linearIndependent_fin2.mp hv).1)
  · rintro rfl
    simp

/-- For a generic multiple-Gamma period family, the physical holomorphic clock meets the full
DA-relative pair arrangement only at the central character. -/
theorem multipleGammaPhysicalLogCharacteristicBoundary_iff_zero
    {r : ℕ} (hr : 1 ≤ r) (tau : Fin (r + 1) → ℂ)
    (htau : LinearIndependent ℚ tau) (lambda : ℂ) :
    MultipleGammaLogCharacteristicBoundary r
        (physicalLogarithmicClock tau lambda) ↔
      lambda = 0 := by
  rw [multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    let pair : Fin 2 → Fin (r + 1) := ![a, b]
    have hpair : Function.Injective pair := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [pair]
    have hLI : LinearIndependent ℚ (fun i ↦ tau (pair i)) :=
      htau.comp pair hpair
    apply (exp_mul_pair_eq_one_eq_one_iff_of_linearIndependent
      (fun i ↦ tau (pair i)) hLI lambda).mp
    simpa [physicalLogarithmicClock, pair] using And.intro ha hb
  · rintro rfl
    refine ⟨⟨0, Nat.succ_pos r⟩, ⟨1, by omega⟩, ?_,
      by simp [physicalLogarithmicClock], by simp [physicalLogarithmicClock]⟩
    simp

/-- The common physical degeneracy spectrum of the DA-relative characteristic ideal and the
actual source-translation boundary is the single central character. -/
theorem multipleGammaPhysicalSourceBoundary_iff_zero
    {r : ℕ} (hr : 1 ≤ r) (tau : Fin (r + 1) → ℂ)
    (htau : LinearIndependent ℚ tau) (lambda : ℂ) :
    (∀ i : Fin (r + 1), physicalCofaceBoundary r tau lambda i = 0) ↔
      lambda = 0 := by
  rw [← multipleGammaPhysicalLogCharacteristicBoundary_iff_sourceBoundary,
    multipleGammaPhysicalLogCharacteristicBoundary_iff_zero hr tau htau]

end

end GaloisForLFunctions.HTGeometry
