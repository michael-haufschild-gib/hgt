import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldSignedOrbits
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Actual orientation quotient counts

A character to the two integer units defines an action on points with an
orientation label. Twisted Burnside counting identifies the difference
between its arithmetic orbit count and the ordinary orbit count with the
signed transporter mass. Stabilizers and ramification are retained.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- Points with an independent orientation label. -/
def OrientationPoints (_χ : G →* ℤˣ) (X : Type*) := X × ℤˣ

instance (χ : G →* ℤˣ) [Fintype X] : Fintype (OrientationPoints χ X) :=
  inferInstanceAs (Fintype (X × ℤˣ))

/-- An orientation character acts on an actual two-point fibre. -/
instance orientationAction (χ : G →* ℤˣ) : MulAction G (OrientationPoints χ X) where
  smul g z := (g • z.1, χ g * z.2)
  one_smul z := by
    change ((1 : G) • z.1, χ 1 * z.2) = z
    simp only [map_one, one_mul, one_smul]
    exact Prod.eta z
  mul_smul g h z := by
    change ((g * h) • z.1, χ (g * h) * z.2) = (g • (h • z.1), χ g * (χ h * z.2))
    simp only [map_mul, mul_assoc, mul_smul]

variable (χ : G →* ℤˣ)

/-- The arithmetic map fixes the orientation label before passage to orbits. -/
def orientationMap (φ : X →[G] X) : (OrientationPoints χ X) →[G] (OrientationPoints χ X) where
  toFun z := (φ z.1, z.2)
  map_smul' g z := by change (φ (g • z.1), χ g * z.2) = (g • φ z.1, χ g * z.2); rw [φ.map_smul]

/-- A twisted point in the orientation cover consists of two independent fixed equations. -/
def orientationTwistEquiv (φ : X →[G] X) (g : G) :
    {z : OrientationPoints χ X // g • z = orientationMap χ φ z} ≃
      {x : X // g • x = φ x} × {u : ℤˣ // χ g * u = u} where
  toFun z := (⟨z.val.1, congrArg Prod.fst z.property⟩, ⟨z.val.2, congrArg Prod.snd z.property⟩)
  invFun z := ⟨(z.1.val, z.2.val), Prod.ext z.1.property z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype G] [Fintype X]

private theorem orientation_fibre_card (u : ℤˣ) :
    (Nat.card {v : ℤˣ // u * v = v} : ℤ) = 1 + (u : ℤ) := by
  classical
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [Nat.card_eq_fintype_card]
  · letI : IsEmpty {v : ℤˣ // (-1 : ℤˣ) * v = v} := ⟨fun v => by
      have h : (-1 : ℤˣ) = 1 := mul_right_cancel (v.property.trans (one_mul v.val).symm)
      have hi := congrArg (fun w : ℤˣ => (w : ℤ)) h
      norm_num at hi⟩
    simp [Nat.card_eq_fintype_card]

omit [Fintype G] [Fintype X] in
/-- Each arithmetic twist gains exactly its orientation character in the cover. -/
theorem orientationTwist_card (φ : X →[G] X) (g : G) :
    (Nat.card {z : OrientationPoints χ X // g • z = orientationMap χ φ z} : ℤ) =
      (1 + (χ g : ℤ)) * Nat.card {x : X // g • x = φ x} := by
  rw [Nat.card_congr (orientationTwistEquiv χ φ g), Nat.card_prod, Nat.cast_mul,
    orientation_fibre_card, mul_comm]

/-- The orientation-cover count is defined from fixed orbits of the actual action. -/
def orientationFixedOrbitCount (φ : X →[G] X) : ℕ :=
  (equivariantFixedOrbits (orientationMap χ φ)).card

/-- Difference of actual counts equals the signed transporter mass, without positivity assumptions. -/
theorem orientationFixedOrbitCount_mul (φ : X →[G] X) :
    ((orientationFixedOrbitCount χ φ : ℤ) - (equivariantFixedOrbits φ).card) *
      Fintype.card G = ∑ x : X, transporterSignSum φ χ x := by
  have ha := congrArg (fun n : ℕ => (n : ℤ)) (sum_card_transporters (orientationMap χ φ))
  have hb := congrArg (fun n : ℕ => (n : ℤ)) (sum_card_transporters φ)
  simp only [Nat.cast_sum, Nat.cast_mul] at ha hb
  simp_rw [orientationTwist_card] at ha
  rw [sum_transporterSignSum]
  change (∑ g : G, (1 + (χ g : ℤ)) * Nat.card {x : X // g • x = φ x}) =
    (orientationFixedOrbitCount χ φ : ℤ) * Fintype.card G at ha
  simp only [add_mul, one_mul, sum_add_distrib] at ha
  rw [hb] at ha
  linear_combination -ha

/-- The rational local weights are the integral difference of two actual orbit counts. -/
theorem orientationFixedOrbitCount_sub_eq_sum (φ : X →[G] X) :
    (orientationFixedOrbitCount χ φ : ℚ) - (equivariantFixedOrbits φ).card =
      ∑ q : Quotient (orbitRel G X), orientationOrbitWeight φ χ q := by
  have hg : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [orientationOrbitWeight, div_eq_mul_inv]
  rw [← sum_mul, ← div_eq_mul_inv]
  apply (eq_div_iff hg).mpr
  rw [← Int.cast_sum, sum_orientationOrbitNumerator, ← sum_transporterSignSum]
  exact_mod_cast orientationFixedOrbitCount_mul χ φ

#print axioms orientationFixedOrbitCount_sub_eq_sum
#print axioms orientationTwist_card
#print axioms orientationFixedOrbitCount_mul
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
