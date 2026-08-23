/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Prime-cyclic one-generator Hasse detection

An additive observable on a prime cyclic group is completely determined by its value at one.
It is either zero or faithful, with the two alternatives detected by that single value.  This is
the route-neutral algebra behind every prime-order local-invariant slice.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- An additive observable on a prime cyclic group vanishes exactly when its generator does. -/
theorem zmodPrime_addMonoidHom_eq_zero_iff_apply_one_eq_zero
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : ZMod p →+ A) :
    F = 0 ↔ F 1 = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  constructor
  · intro hF
    rw [hF]
    rfl
  · intro hF
    ext z
    have hz : z = z.val • (1 : ZMod p) := by
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, mul_one]
    rw [hz, map_nsmul, hF, nsmul_zero]
    rfl

/-- Two additive observables on a prime cyclic group agree globally exactly when they agree on
the generator. -/
theorem zmodPrime_addMonoidHom_eq_iff_apply_one_eq
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F G : ZMod p →+ A) :
    F = G ↔ F 1 = G 1 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  constructor
  · exact fun h => DFunLike.congr_fun h 1
  · intro h
    ext z
    have hz : z = z.val • (1 : ZMod p) := by
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, mul_one]
    rw [hz, map_nsmul, map_nsmul, h]

/-- An additive observable on a prime cyclic group is faithful exactly when it does not kill the
generator. -/
theorem zmodPrime_addMonoidHom_injective_iff_apply_one_ne_zero
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : ZMod p →+ A) :
    Function.Injective F ↔ F 1 ≠ 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  constructor
  · intro hF hzero
    have hone : (1 : ZMod p) = 0 := hF (by simpa using hzero)
    exact one_ne_zero hone
  · intro hone x y hxy
    have hmap : F (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    by_contra hne
    have hsm : ((x - y)⁻¹.val) • (x - y) = (1 : ZMod p) := by
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hne)
    apply hone
    rw [← hsm, map_nsmul, hmap, nsmul_zero]

/-- Prime-cyclic Hasse dichotomy: a local invariant is either identically trivial or faithfully
retains its whole prime-order source, and the generator decides which. -/
theorem zmodPrime_addMonoidHom_trivial_or_faithful_hasse
    (p : Nat.Primes) {A : Type*} [AddGroup A] (F : ZMod p →+ A) :
    (F = 0 ∧ F 1 = 0) ∨ (Function.Injective F ∧ F 1 ≠ 0) := by
  by_cases h : F 1 = 0
  · exact Or.inl ⟨
      (zmodPrime_addMonoidHom_eq_zero_iff_apply_one_eq_zero p F).2 h, h⟩
  · exact Or.inr ⟨
      (zmodPrime_addMonoidHom_injective_iff_apply_one_ne_zero p F).2 h, h⟩

/-- An additive observable on any presentation of a prime cyclic group vanishes exactly when it
vanishes on the transported generator. -/
theorem primeCyclic_addMonoidHom_eq_zero_iff_apply_generator
    (p : Nat.Primes) {B A : Type*} [AddGroup B] [AddGroup A]
    (e : ZMod p ≃+ B) (F : B →+ A) :
    F = 0 ↔ F (e 1) = 0 := by
  constructor
  · intro hF
    rw [hF]
    rfl
  · intro hgen
    have hcomp : F.comp e.toAddMonoidHom = 0 :=
      (zmodPrime_addMonoidHom_eq_zero_iff_apply_one_eq_zero p
        (F.comp e.toAddMonoidHom)).2 (by simpa using hgen)
    ext b
    have hb := DFunLike.congr_fun hcomp (e.symm b)
    simpa using hb

/-- Two additive observables on any presentation of a prime cyclic group agree globally exactly
when they agree on the transported generator. -/
theorem primeCyclic_addMonoidHom_eq_iff_apply_generator_eq
    (p : Nat.Primes) {B A : Type*} [AddGroup B] [AddGroup A]
    (e : ZMod p ≃+ B) (F G : B →+ A) :
    F = G ↔ F (e 1) = G (e 1) := by
  constructor
  · exact fun h => DFunLike.congr_fun h (e 1)
  · intro h
    have hcomp : F.comp e.toAddMonoidHom = G.comp e.toAddMonoidHom :=
      (zmodPrime_addMonoidHom_eq_iff_apply_one_eq p
        (F.comp e.toAddMonoidHom) (G.comp e.toAddMonoidHom)).2 (by simpa using h)
    ext b
    have hb := DFunLike.congr_fun hcomp (e.symm b)
    simpa using hb

/-- An additive observable on any presentation of a prime cyclic group is faithful exactly when
its transported generator is nonzero. -/
theorem primeCyclic_addMonoidHom_injective_iff_apply_generator_ne_zero
    (p : Nat.Primes) {B A : Type*} [AddGroup B] [AddGroup A]
    (e : ZMod p ≃+ B) (F : B →+ A) :
    Function.Injective F ↔ F (e 1) ≠ 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  constructor
  · intro hF hzero
    have he : e 1 = e 0 := hF (by simpa using hzero)
    exact one_ne_zero (e.injective he)
  · intro hgen
    have hcomp : Function.Injective (F.comp e.toAddMonoidHom) :=
      (zmodPrime_addMonoidHom_injective_iff_apply_one_ne_zero p
        (F.comp e.toAddMonoidHom)).2 (by simpa using hgen)
    intro x y hxy
    apply e.symm.injective
    exact hcomp (by simpa using hxy)

/-- Transported prime-cyclic Hasse dichotomy: the generator decides between the trivial and
faithful alternatives in every cyclic presentation. -/
theorem primeCyclic_addMonoidHom_trivial_or_faithful_hasse
    (p : Nat.Primes) {B A : Type*} [AddGroup B] [AddGroup A]
    (e : ZMod p ≃+ B) (F : B →+ A) :
    (F = 0 ∧ F (e 1) = 0) ∨ (Function.Injective F ∧ F (e 1) ≠ 0) := by
  by_cases h : F (e 1) = 0
  · exact Or.inl ⟨
      (primeCyclic_addMonoidHom_eq_zero_iff_apply_generator p e F).2 h, h⟩
  · exact Or.inr ⟨
      (primeCyclic_addMonoidHom_injective_iff_apply_generator_ne_zero p e F).2 h, h⟩

end GaloisForLFunctions.HTGeometry.ABHN
