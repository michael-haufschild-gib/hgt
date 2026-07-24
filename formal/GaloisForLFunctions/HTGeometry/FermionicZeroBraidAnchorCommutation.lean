import GaloisForLFunctions.HTGeometry.RightFlipScattering

/-!
# A flip anchor in the additive braid equation forces local leg commutation

For a family of leg operators solving the quantum (adjacent-flip-removed) Yang--Baxter equation

```
L₁₂(y) · L₁₃(x+y) · L₂₃(x) = L₂₃(x) · L₁₃(x+y) · L₁₂(y),
```

a scalar zero anchor `L(0) = c·1` with `c ≠ 0` forces, on setting `y = 0` and `x = 0` and cancelling
the nonzero scalar, the two pointwise commutation laws

```
[L₁₃(x), L₂₃(x)] = 0,   [L₁₂(x), L₁₃(x)] = 0.
```

This is a direct algebraic consequence of the zero anchor; no analyticity, classification, or
dimension-two hypothesis enters.  The abstract statement `braidZeroAnchor_commute` works in any
`ℂ`-algebra; `fermionicZeroBraid_leg_commute` specialises it to the corpus leg embeddings with the
non-adjacent leg realised by `conjugatedMiddleLeg` (flip conjugation of the adjacent `23` leg).
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- **Zero-anchor commutation law** (equation (5)).  In any `ℂ`-algebra, three leg families solving
the quantum Yang--Baxter equation whose `12`- and `23`-legs have the scalar zero anchor `c·1`,
`c ≠ 0`, satisfy the two pointwise commutation identities. -/
theorem braidZeroAnchor_commute {X T : Type*} [AddMonoid X] [Ring T] [Algebra ℂ T]
    (L12 L13 L23 : X → T) (c : ℂ) (hc : c ≠ 0)
    (hYBE : ∀ x y, L12 y * L13 (x + y) * L23 x = L23 x * L13 (x + y) * L12 y)
    (hanchor12 : L12 0 = c • (1 : T)) (hanchor23 : L23 0 = c • (1 : T)) :
    (∀ x, L13 x * L23 x = L23 x * L13 x) ∧ (∀ x, L12 x * L13 x = L13 x * L12 x) := by
  constructor
  · intro x
    have h := hYBE x 0
    rw [add_zero, hanchor12] at h
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    exact smul_right_injective T hc h
  · intro x
    have h := hYBE 0 x
    rw [zero_add, hanchor23] at h
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    exact smul_right_injective T hc h

/-- **Leg-embedded form.**  With the two adjacent legs `leg12, leg23` and the non-adjacent leg
`conjugatedMiddleLeg` (flip conjugation), a quantum-Yang--Baxter family `R` with scalar zero anchor
`c ≠ 0` has the non-adjacent leg commuting with each adjacent leg pointwise. -/
theorem fermionicZeroBraid_leg_commute
    {X P T : Type*} [AddMonoid X] [Monoid P] [Ring T] [Algebra ℂ T]
    (leg12 leg23 : P →* T) (F : P) (R : X → P) (c : ℂ) (hc : c ≠ 0)
    (hYBE : ∀ x y,
      leg12 (R y) * conjugatedMiddleLeg leg12 leg23 F (R (x + y)) * leg23 (R x)
        = leg23 (R x) * conjugatedMiddleLeg leg12 leg23 F (R (x + y)) * leg12 (R y))
    (hanchor12 : leg12 (R 0) = c • (1 : T))
    (hanchor23 : leg23 (R 0) = c • (1 : T)) :
    (∀ x, conjugatedMiddleLeg leg12 leg23 F (R x) * leg23 (R x)
        = leg23 (R x) * conjugatedMiddleLeg leg12 leg23 F (R x))
      ∧ (∀ x, leg12 (R x) * conjugatedMiddleLeg leg12 leg23 F (R x)
        = conjugatedMiddleLeg leg12 leg23 F (R x) * leg12 (R x)) :=
  braidZeroAnchor_commute (fun x => leg12 (R x))
    (fun x => conjugatedMiddleLeg leg12 leg23 F (R x)) (fun x => leg23 (R x)) c hc hYBE
    hanchor12 hanchor23

end GaloisForLFunctions.HTGeometry
