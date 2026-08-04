import GaloisForLFunctions.RHTower.ResidueJetCompactOpen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Determinant-defect micro-spectra

This module formalizes finite algebraic realization core of determinant-defect completion law.
A root-of-unity block has vanishing power traces below chosen order and arbitrary prescribed
first surviving moment.  Construction is pointwise natural for operator pencils: every pure
homogeneous jet direction is realized exactly.  Together with graded forward-difference
cancellation in ResidueJetSpectralSuspension and compact-open completeness in
ResidueJetCompactOpen, this proves unconditional finite core of completion law.

Schatten norms, finite-rank operator determinants, and their graph closure are not available in
Mathlib and remain analytic paper-level statements.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace RHTower

/--
Power-trace moment of N copies of root-of-unity block
t, tζ, ..., tζ^(k-1).
-/
def rootMicroSpectrumMoment (k N q : ℕ) (t ζ : ℂ) : ℂ :=
  (N : ℂ) * ∑ r ∈ range k, (t * ζ ^ r) ^ q

/-- Geometric root block has zero moment in every positive degree below its order. -/
lemma rootPower_geom_sum_eq_zero {k q : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (hq0 : q ≠ 0) (hqk : q < k) :
    ∑ r ∈ range k, (ζ ^ q) ^ r = 0 := by
  have hxne : ζ ^ q - 1 ≠ 0 :=
    sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt hq0 hqk)
  have hxpow : (ζ ^ q) ^ k = 1 := by
    calc
      (ζ ^ q) ^ k = ζ ^ (q * k) := (pow_mul ζ q k).symm
      _ = ζ ^ (k * q) := by rw [Nat.mul_comm]
      _ = (ζ ^ k) ^ q := pow_mul ζ k q
      _ = 1 := by rw [hζ.pow_eq_one, one_pow]
  have hprod : (ζ ^ q - 1) * ∑ r ∈ range k, (ζ ^ q) ^ r = 0 := by
    rw [mul_geom_sum, hxpow, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left hxne

/-- Root micro-spectrum cancels each positive trace moment below chosen order. -/
theorem rootMicroSpectrumMoment_eq_zero_of_lt {k N q : ℕ} {t ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) (hq0 : q ≠ 0) (hqk : q < k) :
    rootMicroSpectrumMoment k N q t ζ = 0 := by
  rw [rootMicroSpectrumMoment]
  have hsum : ∑ r ∈ range k, (t * ζ ^ r) ^ q =
      t ^ q * ∑ r ∈ range k, (ζ ^ q) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm r q]
  rw [hsum, rootPower_geom_sum_eq_zero hζ hq0 hqk, mul_zero, mul_zero]

/-- First surviving root-block moment is rank times scalar kth power. -/
theorem rootMicroSpectrumMoment_self {k N : ℕ} {t ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ k) :
    rootMicroSpectrumMoment k N k t ζ = ((N * k : ℕ) : ℂ) * t ^ k := by
  rw [rootMicroSpectrumMoment]
  have hterm : ∀ r ∈ range k, (t * ζ ^ r) ^ k = t ^ k := by
    intro r _
    rw [mul_pow, ← pow_mul, Nat.mul_comm r k, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  ring

/--
Every complex moment is realized exactly by a finite root micro-spectrum whose lower positive
moments vanish.  N * k is block rank.
-/
theorem exists_rootMicroSpectrum_realizing
    {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (c : ℂ) :
    ∃ t ζ : ℂ, IsPrimitiveRoot ζ k ∧
      (∀ q, 0 < q → q < k → rootMicroSpectrumMoment k N q t ζ = 0) ∧
      rootMicroSpectrumMoment k N k t ζ = c := by
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / k)
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hcast : (((N * k : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero hN.ne' hk.ne'
  obtain ⟨t, ht⟩ :=
    IsAlgClosed.exists_pow_nat_eq (c / ((N * k : ℕ) : ℂ)) hk
  refine ⟨t, ζ, hζ, ?_, ?_⟩
  · intro q hq0 hqk
    exact rootMicroSpectrumMoment_eq_zero_of_lt hζ hq0.ne' hqk
  · rw [rootMicroSpectrumMoment_self hζ, ht]
    field_simp

/-- Root micro-spectrum applied to one linear parameter functional. -/
def rootMicroSpectrumPencilMoment
    {V : Type*} (k N q : ℕ) (t ζ : ℂ) (ell : V → ℂ) (v : V) : ℂ :=
  rootMicroSpectrumMoment k N q (t * ell v) ζ

/-- Pure homogeneous pencil direction has all lower moments cancelled. -/
theorem rootMicroSpectrumPencilMoment_eq_zero_of_lt
    {V : Type*} {k N q : ℕ} {t ζ : ℂ} {ell : V → ℂ}
    (hζ : IsPrimitiveRoot ζ k) (hq0 : q ≠ 0) (hqk : q < k) (v : V) :
    rootMicroSpectrumPencilMoment k N q t ζ ell v = 0 :=
  rootMicroSpectrumMoment_eq_zero_of_lt hζ hq0 hqk

/-- First surviving pencil moment is corresponding pure homogeneous power. -/
theorem rootMicroSpectrumPencilMoment_self
    {V : Type*} {k N : ℕ} {t ζ : ℂ} {ell : V → ℂ}
    (hζ : IsPrimitiveRoot ζ k) (v : V) :
    rootMicroSpectrumPencilMoment k N k t ζ ell v =
      ((N * k : ℕ) : ℂ) * t ^ k * (ell v) ^ k := by
  rw [rootMicroSpectrumPencilMoment, rootMicroSpectrumMoment_self hζ, mul_pow]
  ring

/--
Every scalar multiple of a pure homogeneous form is a first surviving pencil moment, uniformly
for every parameter value.
-/
theorem exists_rootMicroSpectrumPencil_realizing
    {V : Type*} {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (c : ℂ) (ell : V → ℂ) :
    ∃ t ζ : ℂ, IsPrimitiveRoot ζ k ∧
      (∀ q, 0 < q → q < k →
        ∀ v, rootMicroSpectrumPencilMoment k N q t ζ ell v = 0) ∧
      (∀ v, rootMicroSpectrumPencilMoment k N k t ζ ell v =
        c * (ell v) ^ k) := by
  obtain ⟨t, ζ, hζ, hlower, htop⟩ :=
    exists_rootMicroSpectrum_realizing hk hN c
  refine ⟨t, ζ, hζ, ?_, ?_⟩
  · intro q hq0 hqk v
    exact rootMicroSpectrumPencilMoment_eq_zero_of_lt hζ hq0.ne' hqk v
  · intro v
    rw [rootMicroSpectrumPencilMoment_self hζ, ← htop]
    simp only [rootMicroSpectrumMoment_self hζ]

/-! ## Summability-transition filtration -/

/--
Continuous trace polynomial inserted when changing regularized determinant order from p to q.
The input tau records trace of each power.
-/
def determinantCompletionTransition
    (p q : ℕ) (tau : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Ico p q, (tau j / (j : ℂ)) * z ^ j

/-- Trace-transition polynomials add exactly along summability tower. -/
theorem determinantCompletionTransition_cocycle
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r)
    (tau : ℕ → ℂ) (z : ℂ) :
    determinantCompletionTransition p q tau z +
        determinantCompletionTransition q r tau z =
      determinantCompletionTransition p r tau z := by
  exact Finset.sum_Ico_consecutive
    (fun j => (tau j / (j : ℂ)) * z ^ j) hpq hqr

/--
Changing regularized core by exponential trace transition and subtracting same transition from
defect polynomial preserves completed determinant character.
-/
theorem determinantCompletionTransition_preserves_character
    (p q : ℕ) (tau : ℕ → ℂ) (P core : ℂ) (z : ℂ) :
    Complex.exp P * core =
      Complex.exp (P - determinantCompletionTransition p q tau z) *
        (Complex.exp (determinantCompletionTransition p q tau z) * core) := by
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end RHTower
