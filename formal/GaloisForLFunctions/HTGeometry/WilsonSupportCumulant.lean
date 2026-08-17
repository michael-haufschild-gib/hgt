import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Finset.Interval

/-!
# Wilson support cumulants

Möbius inversion over the Boolean lattice extracts exactly the contribution whose support equals
the requested vertex set. Consequently, a weighted word of length `r` has zero genuine-support
cumulant on every vertex set of cardinality greater than `r`.

The result is stated for arbitrary weights in any commutative ring. Closed Wilson-walk weights are
the application: assigning weight zero to nonclosed words turns the restricted support moment into
the closed-walk trace expansion. No matrix dimension, positivity, or spectral hypothesis is used.
-/

open Finset
open IncidenceAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V P R : Type*} [DecidableEq V] [Fintype P] [CommRing R]

/-- Total weight carried by objects with support exactly `S`. -/
def supportLayer (support : P → Finset V) (weight : P → R) (S : Finset V) : R :=
  ∑ p, if support p = S then weight p else 0

/-- Total weight carried by objects whose support is contained in `T`. -/
def supportMoment (support : P → Finset V) (weight : P → R) (T : Finset V) : R :=
  ∑ p, if support p ⊆ T then weight p else 0

/-- Möbius-inverted support cumulant on the Boolean interval below `S`. -/
def supportMobiusCumulant (support : P → Finset V) (weight : P → R)
    (S : Finset V) : R :=
  ∑ T ∈ Iic S, mu R T S * supportMoment support weight T

/-- A restricted-support moment is the sum of its exact-support layers. -/
theorem supportMoment_eq_sum_supportLayer (support : P → Finset V) (weight : P → R)
    (T : Finset V) :
    supportMoment support weight T = ∑ S ∈ Iic T, supportLayer support weight S := by
  classical
  simp only [supportMoment, supportLayer]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hsub : support p ⊆ T
  · rw [if_pos hsub]
    rw [Finset.sum_eq_single (support p)]
    · simp
    · intro b hb hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (mem_Iic.mpr hsub)).elim
  · rw [if_neg hsub]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    have hne : support p ≠ S := by
      intro heq
      apply hsub
      rw [heq]
      exact mem_Iic.mp hS
    simp [hne]

/-- **Exact support-extraction law.** Möbius inversion of restricted moments equals the weight
of objects whose support is exactly `S`. -/
theorem supportMobiusCumulant_eq_supportLayer
    (support : P → Finset V) (weight : P → R) (S : Finset V) :
    supportMobiusCumulant support weight S = supportLayer support weight S := by
  symm
  exact moebius_inversion_bot (supportLayer support weight)
    (supportMoment support weight) (supportMoment_eq_sum_supportLayer support weight) S

/-- Finite weighted family whose every member uses at most `r` support vertices. -/
structure SupportFilteredFamily (r : ℕ) where
  support : P → Finset V
  weight : P → R
  support_card_le : ∀ p, (support p).card ≤ r

/-- Supports strictly larger than the intrinsic filtration order. -/
def LargeSupport (r : ℕ) := {S : Finset V // r < S.card}

/-- Every cumulant above the intrinsic support order vanishes. -/
theorem SupportFilteredFamily.cumulant_eq_zero {r : ℕ}
    (F : SupportFilteredFamily (V := V) (P := P) (R := R) r) (S : LargeSupport (V := V) r) :
    supportMobiusCumulant F.support F.weight S.1 = 0 := by
  rw [supportMobiusCumulant_eq_supportLayer]
  unfold supportLayer
  apply Finset.sum_eq_zero
  intro p hp
  have hne : F.support p ≠ S.1 := by
    intro heq
    have hle := F.support_card_le p
    rw [heq] at hle
    exact (not_lt_of_ge hle) S.property
  simp [hne]

/-- Set of vertices visited by a word of length `r`. -/
def walkSupport {V : Type*} [DecidableEq V] {r : ℕ} (p : Fin r → V) : Finset V :=
  Finset.univ.image p

/-- A word of length `r` visits at most `r` vertices. -/
theorem walkSupport_card_le {V : Type*} [DecidableEq V] {r : ℕ} (p : Fin r → V) :
    (walkSupport p).card ≤ r := by
  rw [walkSupport]
  calc
    (Finset.univ.image p).card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
    _ = r := by simp

/-- Weighted length-`r` words as a support-filtered family. -/
def wilsonWalkSupportFamily {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    (r : ℕ) (weight : (Fin r → V) → R) :
    SupportFilteredFamily (V := V) (P := Fin r → V) (R := R) r where
  support := walkSupport
  weight := weight
  support_card_le := walkSupport_card_le

/-- **Wilson support-order law.** For arbitrary weights on length-`r` words, every genuine-support
cumulant on more than `r` vertices vanishes. This includes closed Wilson-walk trace weights. -/
theorem wilsonWalkSupportCumulant_eq_zero {V R : Type*}
    [Fintype V] [DecidableEq V] [CommRing R] (r : ℕ) (weight : (Fin r → V) → R)
    (S : LargeSupport (V := V) r) :
    supportMobiusCumulant walkSupport weight S.1 = 0 :=
  (wilsonWalkSupportFamily r weight).cumulant_eq_zero S

end

end GaloisForLFunctions.HTGeometry
