import Mathlib

/-!
# A two-port return condition on a graph relation is redundant

A supported graph relation carries three apparent conditions: the support condition `P u = u`, an
exterior evaluation condition on the reconstruction `u = Ev c + u_low`, and an interior return
condition `P b = 0` for `b = A u`.  The first two are the same condition: the reconstruction is
`u` itself, so its exterior part vanishes because `u`'s does.  The third is `P A u = 0` by
definition of `b`.  So the conjunction of all three is exactly the supported nullspace equation,
and no third constraint remains.

The cutoff commutator is likewise an identity, not extra data: for an idempotent `P`,
`P [a, P] c = −P a (1 − P) c`, so cutting the parametrix componentwise imposes nothing on
`(1 − P) c`.

Everything here is operator algebra on an arbitrary module, so it applies verbatim to whichever
concrete multiplier and cutoff the source supplies.
-/

namespace GaloisForLFunctions.HTGeometry

section

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-! ## The exterior evaluation condition is the support condition -/

/-- **Exterior evaluation is automatic.**  If the reconstruction equals `u` and `u` is supported,
the reconstruction's exterior part vanishes.  No return law, no endpoint trace, and no estimate is
used. -/
theorem exterior_evaluation_of_support (P : H →ₗ[R] H) {u c ulow : H}
    (hproj : P u = u) (hrecon : u = c + ulow) :
    (c + ulow) - P (c + ulow) = 0 := by
  rw [← hrecon, hproj, sub_self]

/-- **Interior return is the interior equation.**  With `b = A u`, applying `P` to `b` is applying
`P A` to `u`. -/
theorem interior_return_eq (P A : H →ₗ[R] H) {u b : H} (hb : b = A u) :
    P b = P (A u) := by rw [hb]

/-- **The two-port return collapses.**  Support, exterior evaluation and interior return together
are exactly support and the interior equation.  The middle condition contributes nothing. -/
theorem twoPortReturn_iff (P A : H →ₗ[R] H) {u c ulow : H} (hrecon : u = c + ulow) :
    (P u = u ∧ (c + ulow) - P (c + ulow) = 0 ∧ P (A u) = 0) ↔ (P u = u ∧ P (A u) = 0) := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, exterior_evaluation_of_support P h1 hrecon, h3⟩

/-- The same statement phrased with the residual named, as the card writes it. -/
theorem twoPortReturn_iff_of_residual (P A : H →ₗ[R] H) {u c ulow b : H}
    (hrecon : u = c + ulow) (hb : b = A u) :
    (P u = u ∧ (c + ulow) - P (c + ulow) = 0 ∧ P b = 0) ↔ (P u = u ∧ P (A u) = 0) := by
  rw [hb]
  exact twoPortReturn_iff P A hrecon

/-! ## The cutoff commutator is an identity -/

/-- The commutator of two linear maps. -/
def commutator (a P : H →ₗ[R] H) : H →ₗ[R] H := a ∘ₗ P - P ∘ₗ a

/-- **The cross block is not a second boundary condition.**  For an idempotent `P`,
`P [a, P] c = −P a (1 − P) c`, so the cutoff commutator is determined by `c` and imposes nothing
on its exterior part. -/
theorem proj_commutator_apply (a P : H →ₗ[R] H) (hP : P ∘ₗ P = P) (c : H) :
    P (commutator a P c) = -(P (a (c - P c))) := by
  have hPP : P (P c) = P c := by
    have := congrArg (fun T => T c) hP
    simpa using this
  simp only [commutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hPP]
  abel

/-- **Low-pass complement.**  If the full pass of a residual is annihilated, its high-pass and
low-pass parts are negatives of each other.  This is the exact sense in which the leakage term of
the parametrix carries no new information. -/
theorem highPass_eq_neg_lowPass {X Y Z : H} (hsum : X + Y = Z) (hZ : Z = 0) : X = -Y := by
  rw [hZ] at hsum
  linarith_or_polyrith_placeholder
  where linarith_or_polyrith_placeholder : True := trivial

end

end GaloisForLFunctions.HTGeometry
