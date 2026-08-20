import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.SuperPoincareCentral
import Mathlib.Tactic

/-!
# Derived algebra for Super-Poincare certificates

These are mechanical consequences of the certificate structures: changing from an `N = 2`
presentation to its split presentation, and rotating the two real supercharges by their sum and
difference.  No analytic source family or spectral hypothesis enters.
-/

namespace SuperPoincare

namespace D1N2

variable {R : Type*} [Ring R] (S : D1N2 R)

/-- Either real supercharge of an `N = 2` sector is an `N = 1` sector with the same momentum. -/
def supercharge0D1N1 : D1N1 R where
  supercharge := S.supercharge0
  momentum := S.momentum
  supercharge_sq := S.supercharge0_sq

/-- Either real supercharge of an `N = 2` sector is an `N = 1` sector with the same momentum. -/
def supercharge1D1N1 : D1N1 R where
  supercharge := S.supercharge1
  momentum := S.momentum
  supercharge_sq := S.supercharge1_sq

/-- Forgetting equality of diagonal momenta gives a split `N = 2` sector. -/
def toD1N2Split : D1N2Split R where
  supercharge0 := S.supercharge0
  supercharge1 := S.supercharge1
  mixed_anticommutator := S.mixed_anticommutator

/-- An ordinary `N = 2` sector is a zero-central-charge extension. -/
def toD1N2Central : D1N2Central R where
  supercharge0 := S.supercharge0
  supercharge1 := S.supercharge1
  centralCharge := 0
  mixed_anticommutator := S.mixed_anticommutator
  centralCharge_commutes_supercharge0 := by simp
  centralCharge_commutes_supercharge1 := by simp

theorem toD1N2Split_momentum0 : S.toD1N2Split.momentum0 = S.momentum :=
  S.supercharge0_sq

theorem toD1N2Split_momentum1 : S.toD1N2Split.momentum1 = S.momentum :=
  S.supercharge1_sq

/-- The sum of two real `N = 2` supercharges squares to twice their common momentum. -/
theorem supercharge_add_sq :
    (S.supercharge0 + S.supercharge1) * (S.supercharge0 + S.supercharge1) =
      S.momentum + S.momentum := by
  calc
    (S.supercharge0 + S.supercharge1) * (S.supercharge0 + S.supercharge1) =
        S.supercharge0 * S.supercharge0 +
          (S.supercharge0 * S.supercharge1 + S.supercharge1 * S.supercharge0) +
          S.supercharge1 * S.supercharge1 := by
      noncomm_ring
    _ = S.momentum + S.momentum := by
      rw [S.supercharge0_sq, S.supercharge1_sq, S.mixed_anticommutator]
      simp

/-- The difference of two real `N = 2` supercharges squares to twice their common momentum. -/
theorem supercharge_sub_sq :
    (S.supercharge0 - S.supercharge1) * (S.supercharge0 - S.supercharge1) =
      S.momentum + S.momentum := by
  calc
    (S.supercharge0 - S.supercharge1) * (S.supercharge0 - S.supercharge1) =
        S.supercharge0 * S.supercharge0 -
          (S.supercharge0 * S.supercharge1 + S.supercharge1 * S.supercharge0) +
          S.supercharge1 * S.supercharge1 := by
      noncomm_ring
    _ = S.momentum + S.momentum := by
      rw [S.supercharge0_sq, S.supercharge1_sq, S.mixed_anticommutator]
      simp

/-- Sum and difference are again anticommuting real supercharges. -/
theorem supercharge_add_sub_anticommutes :
    (S.supercharge0 + S.supercharge1) * (S.supercharge0 - S.supercharge1) +
      (S.supercharge0 - S.supercharge1) * (S.supercharge0 + S.supercharge1) = 0 := by
  calc
    (S.supercharge0 + S.supercharge1) * (S.supercharge0 - S.supercharge1) +
        (S.supercharge0 - S.supercharge1) * (S.supercharge0 + S.supercharge1) =
        (S.supercharge0 * S.supercharge0 + S.supercharge0 * S.supercharge0) -
          (S.supercharge1 * S.supercharge1 + S.supercharge1 * S.supercharge1) := by
      noncomm_ring
    _ = 0 := by
      rw [S.supercharge0_sq, S.supercharge1_sq]
      abel

/-- Sum and difference give a second `N = 2` presentation with doubled momentum. -/
def sumDiffD1N2 : D1N2 R where
  supercharge0 := S.supercharge0 + S.supercharge1
  supercharge1 := S.supercharge0 - S.supercharge1
  momentum := S.momentum + S.momentum
  supercharge0_sq := S.supercharge_add_sq
  supercharge1_sq := S.supercharge_sub_sq
  mixed_anticommutator := S.supercharge_add_sub_anticommutes

end D1N2

namespace D1N2Split

variable {R : Type*} [Ring R] (S : D1N2Split R)

/-- The two even translations of every split sector commute. -/
theorem momentum0_commutes_momentum1 :
    S.momentum0 * S.momentum1 = S.momentum1 * S.momentum0 := by
  unfold momentum0 momentum1
  have h0 : (S.supercharge0 * S.supercharge0) * S.supercharge1 =
      S.supercharge1 * (S.supercharge0 * S.supercharge0) := by
    simpa only [momentum0] using S.momentum0_commutes_supercharge1
  calc
    (S.supercharge0 * S.supercharge0) * (S.supercharge1 * S.supercharge1) =
        ((S.supercharge0 * S.supercharge0) * S.supercharge1) * S.supercharge1 := by
      rw [← mul_assoc]
    _ = (S.supercharge1 * (S.supercharge0 * S.supercharge0)) * S.supercharge1 := by
      rw [h0]
    _ = S.supercharge1 * ((S.supercharge0 * S.supercharge0) * S.supercharge1) := by
      rw [mul_assoc]
    _ = S.supercharge1 * (S.supercharge1 * (S.supercharge0 * S.supercharge0)) := by
      rw [h0]
    _ = (S.supercharge1 * S.supercharge1) * (S.supercharge0 * S.supercharge0) := by
      rw [← mul_assoc]

end D1N2Split

end SuperPoincare
