import GaloisForLFunctions.HTGeometry.PaperStabilizedPointFlow

/-!
# An explicit global polynomial cross-section after stabilization

Move each point for time `-f(x)` to reach the zero fibre. The resulting
normalization has polynomial coordinates and is constant exactly on flow
orbits. The level and normalized point give a global product decomposition.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

/-- The zero level of the stabilized polynomial, as ordinary complex points. -/
abbrev PaperStabilizedZeroPoints := {x : Fin 5 → ℂ // aeval x (stabilize f) = 0}

/-- The uniquely normalized representative on the zero level. -/
def paperStabilizedPointNormalize (x : Fin 5 → ℂ) : PaperStabilizedZeroPoints :=
  ⟨paperStabilizedPointFlow (-(aeval x (stabilize f))) x, by
    rw [paperStabilizedPointFlow_level, add_neg_cancel]⟩

/-- Explicit polynomial coordinates for the normalization map. -/
def paperStabilizedPointNormalizerCoordinate (i : Fin 5) : R 5 :=
  (paperStabilizedAction.toAlgHom (X i)).eval (-(stabilize f))

/-- Normalization is polynomial in the original point coordinates. -/
theorem paperStabilizedPointNormalize_polynomial (x : Fin 5 → ℂ) (i : Fin 5) :
    (paperStabilizedPointNormalize x).val i =
      aeval x (paperStabilizedPointNormalizerCoordinate i) := by
  change paperStabilizedPointFlow (-(aeval x (stabilize f))) x i = _
  rw [paperStabilizedPointFlow_jointPolynomial]
  change (paperStabilizedAction.toAlgHom (X i)).eval₂ (aeval x).toRingHom
      (-(aeval x (stabilize f))) =
    aeval x ((paperStabilizedAction.toAlgHom (X i)).eval (-(stabilize f)))
  have he := Polynomial.eval₂_at_apply (p := paperStabilizedAction.toAlgHom (X i))
    (aeval x).toRingHom (-(stabilize f))
  have hn : (aeval x).toRingHom (-(stabilize f)) = -(aeval x (stabilize f)) :=
    map_neg (aeval x : R 5 →ₐ[ℂ] ℂ) _
  rw [hn] at he
  exact he

/-- A global product decomposition with the level as first coordinate. -/
def paperStabilizedPointSliceEquiv : (Fin 5 → ℂ) ≃ ℂ × PaperStabilizedZeroPoints where
  toFun x := (aeval x (stabilize f), paperStabilizedPointNormalize x)
  invFun p := paperStabilizedPointFlow p.1 p.2.val
  left_inv x := by
    change paperStabilizedPointFlow (aeval x (stabilize f))
      (paperStabilizedPointFlow (-(aeval x (stabilize f))) x) = x
    rw [paperStabilizedPointFlow_add, add_neg_cancel, paperStabilizedPointFlow_zero]
  right_inv p := by
    apply Prod.ext
    · change aeval (paperStabilizedPointFlow p.1 p.2.val) (stabilize f) = p.1
      rw [paperStabilizedPointFlow_level, p.2.property, zero_add]
    · apply Subtype.ext
      change paperStabilizedPointFlow
        (-(aeval (paperStabilizedPointFlow p.1 p.2.val) (stabilize f)))
        (paperStabilizedPointFlow p.1 p.2.val) = p.2.val
      rw [paperStabilizedPointFlow_level, p.2.property, zero_add,
        paperStabilizedPointFlow_add, neg_add_cancel, paperStabilizedPointFlow_zero]

/-- Normalization is fixed along every complex-time orbit. -/
theorem paperStabilizedPointNormalize_flow (t : ℂ) (x : Fin 5 → ℂ) :
    paperStabilizedPointNormalize (paperStabilizedPointFlow t x) =
      paperStabilizedPointNormalize x := by
  apply Subtype.ext
  change paperStabilizedPointFlow
      (-(aeval (paperStabilizedPointFlow t x) (stabilize f))) (paperStabilizedPointFlow t x) = _
  rw [paperStabilizedPointFlow_level, paperStabilizedPointFlow_add]
  have ht : -(aeval x (stabilize f) + t) + t = -(aeval x (stabilize f)) := by ring
  rw [ht]
  rfl

/-- Normalized representatives classify the actual additive-flow orbits exactly. -/
theorem paperStabilizedPointNormalize_eq_iff_orbit (x y : Fin 5 → ℂ) :
    paperStabilizedPointNormalize x = paperStabilizedPointNormalize y ↔
      ∃ t : ℂ, paperStabilizedPointFlow t x = y := by
  constructor
  · intro h
    refine ⟨aeval y (stabilize f) - aeval x (stabilize f), ?_⟩
    apply paperStabilizedPointSliceEquiv.injective
    apply Prod.ext
    · change aeval (paperStabilizedPointFlow _ x) (stabilize f) = aeval y (stabilize f)
      rw [paperStabilizedPointFlow_level]
      ring
    · exact (paperStabilizedPointNormalize_flow _ x).trans h
  · rintro ⟨t, rfl⟩
    exact (paperStabilizedPointNormalize_flow t x).symm

end

end GaloisForLFunctions.HTGeometry
