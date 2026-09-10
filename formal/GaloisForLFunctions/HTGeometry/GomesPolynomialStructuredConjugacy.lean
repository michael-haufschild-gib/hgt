import GaloisForLFunctions.HTGeometry.GomesPolynomialMultiplierIntertwining

/-!
# The structure needed to recover a polynomial connection coefficient

Arbitrary real-linear conjugacy forgets nonconstant coefficients except for degree.
Requiring the same map to preserve the coordinate multiplication action restores the
full coefficient. The remaining invertible symmetries are precisely nonzero scalars.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Connection intertwiners retaining the action of the polynomial coordinate. -/
abbrev GomesPolynomialStructuredIntertwiner (A B : ℝ[X]) :=
  {E : GomesPolynomialConnectionIntertwiner A B //
    E.val.toLinearMap.comp (gomesPolynomialMultiplicationMap X) =
      (gomesPolynomialMultiplicationMap X).comp E.val.toLinearMap}

/-- An invertible connection map is nonzero as a linear map. -/
theorem gomesPolynomialConnectionIntertwiner_linearMap_ne_zero
    (A B : ℝ[X]) (E : GomesPolynomialConnectionIntertwiner A B) :
    E.val.toLinearMap ≠ 0 := by
  intro h
  have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f 1) h
  change E.val (1 : ℝ[X]) = 0 at he
  have hz : E.val (1 : ℝ[X]) = E.val 0 := by
    simpa only [LinearMap.zero_apply, map_zero] using he
  exact one_ne_zero (E.val.injective hz)

/-- Every structured intertwiner is a nonzero scalar map between identical coefficients. -/
theorem gomesPolynomialStructuredIntertwiner_scalar_classification
    (A B : ℝ[X]) (E : GomesPolynomialStructuredIntertwiner A B) :
    A = B ∧ ∃ c : ℝ, c ≠ 0 ∧
      E.val.val.toLinearMap = c • (LinearMap.id : ℝ[X] →ₗ[ℝ] ℝ[X]) := by
  have hn := gomesPolynomialConnectionIntertwiner_linearMap_ne_zero A B E.val
  have h := (gomesPolynomialConnection_coordinate_compatible_maps_iff A B
    E.val.val.toLinearMap).mp ⟨E.property, E.val.property⟩
  rcases h with hz | ⟨hab, c, hc⟩
  · exact False.elim (hn hz)
  · refine ⟨hab, c, ?_, hc⟩
    intro hz
    exact hn (by simpa only [hz, zero_smul] using hc)

/-- Keeping coordinate multiplication makes connection coefficient reconstruction exact. -/
theorem gomesPolynomialConnection_structured_intertwiner_iff (A B : ℝ[X]) :
    Nonempty (GomesPolynomialStructuredIntertwiner A B) ↔ A = B := by
  constructor
  · rintro ⟨E⟩
    exact (gomesPolynomialStructuredIntertwiner_scalar_classification A B E).1
  · rintro rfl
    refine ⟨⟨gomesPolynomialConnectionIntertwinerRefl A, ?_⟩⟩
    apply LinearMap.ext
    intro P
    rfl

/-- Fixing the constant polynomial removes even the residual scalar freedom. -/
theorem gomesPolynomialStructuredIntertwiner_unital_iff_identity
    (A B : ℝ[X]) (E : GomesPolynomialStructuredIntertwiner A B) :
    E.val.val 1 = 1 ↔ E.val.val = LinearEquiv.refl ℝ ℝ[X] := by
  constructor
  · intro h
    apply LinearEquiv.ext
    intro P
    have he := gomesPolynomialXCompatibleMap_apply
      ⟨E.val.val.toLinearMap, E.property⟩ P
    change E.val.val P = E.val.val 1 * P at he
    change E.val.val P = P
    simpa only [h, one_mul] using he
  · intro h
    rw [h]
    rfl

/-- The exact gap between abstract and coordinate-preserving conjugacy. -/
theorem gomesPolynomialConnection_abstract_structured_gap_iff (A B : ℝ[X]) :
    (Nonempty (GomesPolynomialConnectionIntertwiner A B) ∧
      ¬ Nonempty (GomesPolynomialStructuredIntertwiner A B)) ↔
        A ≠ B ∧ A.derivative ≠ 0 ∧ B.derivative ≠ 0 ∧ A.natDegree = B.natDegree := by
  rw [gomesPolynomialConnection_intertwiner_iff,
    gomesPolynomialConnection_structured_intertwiner_iff]
  tauto

/-- Every nonzero constant shift is abstractly conjugate but structurally inequivalent. -/
theorem gomesPolynomialConnection_shift_structure_boundary
    (A : GomesNonconstantPolynomialCoefficient) (r : {r : ℝ // r ≠ 0}) :
    Nonempty (GomesPolynomialConnectionIntertwiner A.val (A.val + C r.val)) ∧
      ¬ Nonempty (GomesPolynomialStructuredIntertwiner A.val (A.val + C r.val)) := by
  have h := gomesPolynomialConnection_nonconstant_reconstruction_failure A r
  refine ⟨h.2, ?_⟩
  intro he
  exact h.1 ((gomesPolynomialConnection_structured_intertwiner_iff _ _).mp he).symm

end GaloisForLFunctions.HTGeometry
