import Mathlib.Tactic

/-!
# Sigma directions and local divisor jets

This module isolates the local algebra behind a possible `{sigma_p}`-graded divisor
refinement at one pinned annulus.  If a function has local form `X^m * u`, then a
first-order source direction can affect the divisor only through its class modulo `X^m`.
Multiplicative source directions, locally of the form `(X^m * u) * h_p`, have zero class
modulo `X^m`; they change only the local unit, not the divisor jet.

The statement is carrier-free: it does not construct a global family of functions, and it
does not use positivity or character theory.
-/

noncomputable section

namespace RHTower

open Polynomial

/-- The ideal `(X^m)` in the polynomial local model. -/
abbrev jetIdeal (R : Type*) [CommRing R] (m : ℕ) : Ideal (Polynomial R) :=
  Ideal.span ({(Polynomial.X : Polynomial R) ^ m} : Set (Polynomial R))

/-- The local divisor-jet algebra `R[X]/(X^m)`.  It models the first `m` Taylor
coefficients at a zero of multiplicity `m`. -/
abbrev LocalDivisorJet (R : Type*) [CommRing R] (m : ℕ) :=
  Polynomial R ⧸ jetIdeal R m

/-- The class of a local source direction in the divisor-jet algebra. -/
def jetClass (R : Type*) [CommRing R] (m : ℕ) (P : Polynomial R) : LocalDivisorJet R m :=
  Ideal.Quotient.mk (jetIdeal R m) P

/-- The zero factor `X^m` vanishes in the local divisor-jet algebra. -/
theorem X_pow_mem_jetIdeal (R : Type*) [CommRing R] (m : ℕ) :
    (Polynomial.X : Polynomial R) ^ m ∈ jetIdeal R m := by
  exact Ideal.subset_span (by simp)

/-- Anything divisible by `X^m` has zero local divisor-jet class. -/
theorem jetClass_eq_zero_of_X_pow_dvd (R : Type*) [CommRing R] (m : ℕ) {P : Polynomial R}
    (h : (Polynomial.X : Polynomial R) ^ m ∣ P) : jetClass R m P = 0 := by
  rcases h with ⟨Q, rfl⟩
  rw [jetClass]
  have hmem : Q * ((Polynomial.X : Polynomial R) ^ m) ∈ jetIdeal R m :=
    Ideal.mul_mem_left _ Q (X_pow_mem_jetIdeal R m)
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [mul_comm] using hmem)

/-- A local multiplicative source direction `X^m * Q` has zero divisor jet. -/
theorem jetClass_mul_X_pow_eq_zero (R : Type*) [CommRing R] (m : ℕ) (Q : Polynomial R) :
    jetClass R m (((Polynomial.X : Polynomial R) ^ m) * Q) = 0 :=
  jetClass_eq_zero_of_X_pow_dvd R m ⟨Q, rfl⟩

/-- Adding a multiple of `X^m` does not change a local divisor-jet class. -/
theorem jetClass_add_X_pow_mul (R : Type*) [CommRing R] (m : ℕ) (P Q : Polynomial R) :
    jetClass R m (P + ((Polynomial.X : Polynomial R) ^ m) * Q) = jetClass R m P := by
  rw [jetClass, jetClass]
  change Ideal.Quotient.mk (jetIdeal R m) (P + ((Polynomial.X : Polynomial R) ^ m) * Q) =
    Ideal.Quotient.mk (jetIdeal R m) P
  rw [map_add]
  have hzero : Ideal.Quotient.mk (jetIdeal R m) (((Polynomial.X : Polynomial R) ^ m) * Q) = 0 := by
    exact jetClass_mul_X_pow_eq_zero R m Q
  rw [hzero, add_zero]

/-- A local divisor-jet class is zero exactly when all coefficients below the
multiplicity cutoff vanish. -/
theorem jetClass_eq_zero_iff_coeff_lt_eq_zero (R : Type*) [CommRing R] (m : ℕ)
    {P : Polynomial R} :
    jetClass R m P = 0 ↔ ∀ j < m, P.coeff j = 0 := by
  rw [jetClass]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hmem
    have hdiv : (Polynomial.X : Polynomial R) ^ m ∣ P := by
      simpa [jetIdeal] using (Ideal.mem_span_singleton.mp hmem)
    exact Polynomial.X_pow_dvd_iff.mp hdiv
  · intro hcoeff
    have hdiv : (Polynomial.X : Polynomial R) ^ m ∣ P :=
      Polynomial.X_pow_dvd_iff.mpr hcoeff
    rcases hdiv with ⟨Q, rfl⟩
    have hmem : Q * ((Polynomial.X : Polynomial R) ^ m) ∈ jetIdeal R m :=
      Ideal.mul_mem_left _ Q (X_pow_mem_jetIdeal R m)
    simpa [mul_comm] using hmem

/-- Equivalently, a local divisor-jet class is nonzero exactly when some coefficient
below the multiplicity cutoff survives. -/
theorem jetClass_ne_zero_iff_exists_coeff_lt_ne_zero (R : Type*) [CommRing R] (m : ℕ)
    {P : Polynomial R} :
    jetClass R m P ≠ 0 ↔ ∃ j, j < m ∧ P.coeff j ≠ 0 := by
  constructor
  · intro hnonzero
    by_contra hnone
    push Not at hnone
    exact hnonzero ((jetClass_eq_zero_iff_coeff_lt_eq_zero R m).mpr hnone)
  · rintro ⟨j, hj, hcoeff⟩ hzero
    have hall := (jetClass_eq_zero_iff_coeff_lt_eq_zero R m).mp hzero
    exact hcoeff (hall j hj)

/-- A sigma-family has a nontrivial local divisor jet if some sigma direction has nonzero
class in `R[X]/(X^m)`. -/
def HasNontrivialSigmaJet {R Sigma : Type*} [CommRing R] (m : ℕ)
    (delta : Sigma → Polynomial R) : Prop :=
  ∃ p : Sigma, jetClass R m (delta p) ≠ 0

/-- If every sigma direction is divisible by `X^m`, the sigma-family has no nontrivial
local divisor jet. -/
theorem no_nontrivialSigmaJet_of_X_pow_dvd {R Sigma : Type*} [CommRing R] (m : ℕ)
    {delta : Sigma → Polynomial R}
    (hdiv : ∀ p : Sigma, (Polynomial.X : Polynomial R) ^ m ∣ delta p) :
    ¬ HasNontrivialSigmaJet m delta := by
  rintro ⟨p, hp⟩
  exact hp (jetClass_eq_zero_of_X_pow_dvd R m (hdiv p))

/-- A purely multiplicative sigma-family `delta_p = X^m * h_p` has no nontrivial
local divisor jet. -/
theorem no_nontrivialSigmaJet_of_multiplicative {R Sigma : Type*} [CommRing R] (m : ℕ)
    (h : Sigma → Polynomial R) :
    ¬ HasNontrivialSigmaJet m (fun p => ((Polynomial.X : Polynomial R) ^ m) * h p) := by
  refine no_nontrivialSigmaJet_of_X_pow_dvd (R := R) (Sigma := Sigma) m ?_
  intro p
  exact ⟨h p, rfl⟩

/-- Multiplying a local zero model `X^m * u` by any sigma-dependent local factor still gives
zero divisor jet: the deformation remains divisible by the zero factor. -/
theorem no_nontrivialSigmaJet_of_unit_multiplicative {R Sigma : Type*} [CommRing R] (m : ℕ)
    (u : Polynomial R) (h : Sigma → Polynomial R) :
    ¬ HasNontrivialSigmaJet m (fun p => (((Polynomial.X : Polynomial R) ^ m) * u) * h p) := by
  refine no_nontrivialSigmaJet_of_X_pow_dvd (R := R) (Sigma := Sigma) m ?_
  intro p
  exact ⟨u * h p, by rw [mul_assoc]⟩

end RHTower
