/-
Finite pairing algebra for boundary crossing events.

The mathematical content is intentionally abstract: once a finite event set carries a
fixed-point-free involutive pairing, its unit contribution vanishes in `ZMod 2`. The
analytic work in applications is to construct the event type and the pairing.
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace RHTower

/-- A finite event set with a pairing involution that has no fixed event. -/
structure FixedPointFreePairing (Event : Type*) [Fintype Event] where
  pair : Equiv.Perm Event
  pair_sq : pair ^ 2 = 1
  no_fixed : ∀ e : Event, pair e ≠ e

/-- A band-edge pairing is a fixed-point-free pairing of the finite crossing events. -/
abbrev BandEdgePairing (Event : Type*) [Fintype Event] :=
  FixedPointFreePairing Event

variable {Event : Type*} [Fintype Event] [DecidableEq Event]

omit [DecidableEq Event] in
/-- The unit mod-two flux is the cardinality of the event set, reduced modulo two. -/
theorem bandEdgeUnitFlux_eq_card :
    (∑ _e : Event, (1 : ZMod 2)) = ((Fintype.card Event : ℕ) : ZMod 2) := by
  rw [Finset.sum_const, Finset.card_univ]
  simp

/-- A fixed-point-free involution has even finite cardinality. -/
theorem fixedPointFreePairing_two_dvd_card (P : FixedPointFreePairing Event) :
    2 ∣ Fintype.card Event := by
  have hsupport : P.pair.support = Finset.univ := by
    ext e
    simp [Equiv.Perm.mem_support, P.no_fixed e]
  simpa [hsupport] using Equiv.Perm.two_dvd_card_support (σ := P.pair) P.pair_sq

/-- The cardinality of a fixed-point-free paired event set is zero in `ZMod 2`. -/
theorem fixedPointFreePairing_card_zmod_two_eq_zero (P : FixedPointFreePairing Event) :
    ((Fintype.card Event : ℕ) : ZMod 2) = 0 := by
  rcases fixedPointFreePairing_two_dvd_card (Event := Event) P with ⟨k, hk⟩
  rw [hk, Nat.cast_mul]
  rw [show ((2 : ℕ) : ZMod 2) = 0 by exact CharP.cast_eq_zero (ZMod 2) 2]
  simp

/-- The unit mod-two flux of a fixed-point-free paired event set vanishes. -/
theorem bandEdgeUnitFlux_zmod_two_eq_zero (P : BandEdgePairing Event) :
    (∑ _e : Event, (1 : ZMod 2)) = 0 := by
  rw [bandEdgeUnitFlux_eq_card]
  exact fixedPointFreePairing_card_zmod_two_eq_zero (Event := Event) P

/-- An odd event set cannot carry a fixed-point-free pairing. -/
theorem not_fixedPointFreePairing_of_card_zmod_two_ne_zero
    (h : ((Fintype.card Event : ℕ) : ZMod 2) ≠ 0) :
    ¬ Nonempty (FixedPointFreePairing Event) := by
  rintro ⟨P⟩
  exact h (fixedPointFreePairing_card_zmod_two_eq_zero (Event := Event) P)

/-- Nonzero unit mod-two flux rules out the band-edge pairing interface. -/
theorem not_bandEdgePairing_of_unitFlux_ne_zero
    (h : (∑ _e : Event, (1 : ZMod 2)) ≠ 0) :
    ¬ Nonempty (BandEdgePairing Event) := by
  rintro ⟨P⟩
  exact h (bandEdgeUnitFlux_zmod_two_eq_zero (Event := Event) P)

end RHTower
