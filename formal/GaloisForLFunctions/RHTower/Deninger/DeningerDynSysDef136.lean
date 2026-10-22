import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRelativeStalk
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Definition 13.6 and Proposition 13.8 at the scheme level

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definition 13.6,
Supplement 13.7 and Proposition 13.8.

An `o`-valued point of `X` over the base `X₀` is a point `x` of `X`, a point `y₀` of `X₀` in the
closure of the image of `x`, and a pointed multiplicative map `P_{y₀}` on the relative local ring
`𝒪_{X , y₀}` — the stalk of `π_* 𝒪_X` at `y₀` — whose value depends only on, and vanishes exactly
with, the value at `x`; together with a point `y` above `y₀` and the induced map on residue fields
making the upper square of diagram (148) commute.

Two consequences are recorded.  The map vanishes exactly where evaluation at `x` does, which is
conditions 1) and 2) combined; and the preimage of the maximal ideal is exactly the set of
relative sections vanishing at `y`, which is equation (149) of Supplement 13.7.  The second uses
that the residue map vanishes only at zero, automatic for a multiplicative map from a field into a
nontrivial ring.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry TopCat.Presheaf

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀)

/-- **Deninger, Definition 13.6 and Proposition 13.8.**  An `o`-valued point of `X` over the base
`X₀`: a point `x` of `X`, a point `y₀` of `X₀` in the closure of the image of `x`, a pointed
multiplicative map `P_{y₀}` on the relative local ring `𝒪_{X , y₀}` whose value depends only on
and vanishes exactly with the value at `x`, and a point `y` above `y₀` together with the induced
map on residue fields. -/
structure DeningerRelValuedTriple (O : Type u) [CommRing O] [IsLocalRing O] where
  /-- the point of `X`. -/
  point : X
  /-- the point of the base, a specialization of the image of `point`. -/
  basePoint : X₀
  /-- `y₀` lies in the closure of `π (x)`. -/
  specializes : π.base point ⤳ basePoint
  /-- the pointed multiplicative map `P_{y₀}`. -/
  map : deningerRelStalk π basePoint →*₀ O
  /-- condition 2): the value depends only on the value at `x`. -/
  map_congr : ∀ f g : deningerRelStalk π basePoint,
    (deningerRelEvalAt π specializes).hom f = (deningerRelEvalAt π specializes).hom g →
      map f = map g
  /-- condition 1): the value is nonzero when the value at `x` is. -/
  map_ne_zero : ∀ f : deningerRelStalk π basePoint,
    (deningerRelEvalAt π specializes).hom f ≠ 0 → map f ≠ 0
  /-- condition 3): a point above `y₀` … -/
  fibrePoint : X
  /-- … lying over `y₀` … -/
  fibreSpecializes : π.base fibrePoint ⤳ basePoint
  /-- … and the induced map on its residue field. -/
  residueMap : X.residueField fibrePoint →*₀ IsLocalRing.ResidueField O
  /-- the square of condition 3) commutes. -/
  residueMap_comm : ∀ f : deningerRelStalk π basePoint,
    residueMap ((deningerRelEvalAt π fibreSpecializes).hom f)
      = IsLocalRing.residue O (map f)

variable {π} {O : Type u} [CommRing O] [IsLocalRing O]

/-- **Deninger, Proposition 13.8, condition 1) and 2) combined.**  The map vanishes exactly where
the evaluation at `x` does. -/
theorem deningerRelValuedTriple_map_eq_zero_iff (P : DeningerRelValuedTriple π O)
    (f : deningerRelStalk π P.basePoint) :
    P.map f = 0 ↔ (deningerRelEvalAt π P.specializes).hom f = 0 := by
  constructor
  · intro h
    by_contra hne
    exact P.map_ne_zero f hne h
  · intro h
    have h0 : (deningerRelEvalAt π P.specializes).hom f
        = (deningerRelEvalAt π P.specializes).hom 0 := by rw [h, map_zero]
    rw [P.map_congr f 0 h0, map_zero]

/-- The residue map of a triple vanishes only at zero: a multiplicative map from a field into a
nontrivial ring sends nonzero elements to units. -/
theorem deningerRelValuedTriple_residueMap_eq_zero_iff (P : DeningerRelValuedTriple π O)
    (z : X.residueField P.fibrePoint) : P.residueMap z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  by_contra hz
  have hunit : P.residueMap z * P.residueMap z⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  rw [h, zero_mul] at hunit
  exact zero_ne_one hunit

/-- **Deninger, Supplement 13.7, equation (149), at the scheme level.**  The preimage of the
maximal ideal under `P_{y₀}` is exactly the set of relative sections vanishing at `y`. -/
theorem deningerRelValuedTriple_mem_maximalIdeal_iff (P : DeningerRelValuedTriple π O)
    (f : deningerRelStalk π P.basePoint) :
    P.map f ∈ IsLocalRing.maximalIdeal O
      ↔ (deningerRelEvalAt π P.fibreSpecializes).hom f = 0 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  show IsLocalRing.residue O (P.map f) = 0 ↔ _
  rw [← P.residueMap_comm f, deningerRelValuedTriple_residueMap_eq_zero_iff]

end

end RHTower
