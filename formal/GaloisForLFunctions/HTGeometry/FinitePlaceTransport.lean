/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the FLT LICENSE.

Adapted for this project from
https://github.com/ImperialCollegeLondon/FLT/blob/071d16bb51e87165b4f4b5466f14051344bf426b/FLT/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean.
Names are project-scoped to avoid future mathlib clashes.
-/

import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Finite-place transport

Closed finite-prime transport infrastructure used by the number-field Artin Euler-factor lane.
-/

open IsDedekindDomain
open scoped NumberField

namespace GaloisForLFunctions

/-- Pull a height-one prime back along a ring equivalence. -/
def heightOneSpectrumComap {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P : HeightOneSpectrum B) : HeightOneSpectrum A :=
  { asIdeal := Ideal.comap e P.asIdeal
    isPrime := P.asIdeal.comap_isPrime e
    ne_bot := by
      intro h
      apply P.ne_bot
      apply Ideal.comap_injective_of_surjective e e.surjective
      rw [h, Ideal.comap_bot_of_injective e e.injective] }

/-- Height-one spectra are equivalent across a ring equivalence. -/
def heightOneSpectrumEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    HeightOneSpectrum A ≃ HeightOneSpectrum B where
  toFun := heightOneSpectrumComap e.symm
  invFun := heightOneSpectrumComap e
  left_inv P := by
    ext1
    convert! Ideal.comap_comap e.toRingHom e.symm.toRingHom
    simp
  right_inv Q := by
    ext1
    convert! Ideal.comap_comap e.symm.toRingHom e.toRingHom
    simp

/-- Finite place of `ℤ` determined by a natural prime. -/
def heightOneSpectrumIntOfNatPrime {p : ℕ} (hp : p.Prime) : HeightOneSpectrum ℤ :=
  { asIdeal := Ideal.span {(p : ℤ)}
    isPrime := by
      rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hp.ne_zero), ← Nat.prime_iff_prime_int]
    ne_bot := mt Submodule.span_singleton_eq_bot.mp (Int.ofNat_ne_zero.mpr hp.ne_zero) }

/-- Canonical finite place of `ℚ` determined by a natural prime. -/
noncomputable def heightOneSpectrumRatOfNatPrime {p : ℕ} (hp : p.Prime) :
    HeightOneSpectrum (𝓞 ℚ) :=
  heightOneSpectrumEquiv Rat.ringOfIntegersEquiv.symm (heightOneSpectrumIntOfNatPrime hp)

end GaloisForLFunctions
