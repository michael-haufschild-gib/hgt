import GaloisForLFunctions.HTGeometry.ResolvedSourceAugmentationConservativityLaw

/-!
# Source-pointed conservativity chain law

A composite observation loses no information on a selected source sector exactly when every stage
loses no information on the sector propagated to that stage.  This is the serial form of resolved
source conservativity and applies to arbitrary transports, quotients, augmentations, and readers.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R E F G : Type*}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]

/-- The invisible sector of a composite is the pullback of the invisible sector of its last stage. -/
theorem ker_comp_eq_comap_ker (f : E →ₗ[R] F) (g : F →ₗ[R] G) :
    LinearMap.ker (g.comp f) = (LinearMap.ker g).comap f := by
  ext x
  rfl

/-- **Source-pointed conservativity chain law.**  A serial composite is conservative on its
initial source sector exactly when the first stage is conservative there and the second stage is
conservative on the propagated source sector. -/
theorem isConservativeOn_comp_iff
    (f : E →ₗ[R] F) (g : F →ₗ[R] G) (S : Submodule R E) :
    IsConservativeOn (g.comp f) S ↔
      IsConservativeOn f S ∧ IsConservativeOn g (S.map f) := by
  simp only [IsConservativeOn, Submodule.disjoint_def]
  constructor
  · intro h
    constructor
    · intro x hxS hxf
      apply h x hxS
      change g (f x) = 0
      rw [hxf, map_zero]
    · intro y hyS hyg
      rcases hyS with ⟨x, hxS, rfl⟩
      have hx0 : x = 0 := h x hxS hyg
      rw [hx0, map_zero]
  · rintro ⟨hf, hg⟩ x hxS hgfx
    have hfxS : f x ∈ S.map f := ⟨x, hxS, rfl⟩
    have hfx0 : f x = 0 := hg (f x) hfxS hgfx
    exact hf x hxS hfx0

/-- Once one stage destroys source information, no later linear reader can restore it. -/
theorem not_isConservativeOn_comp_of_not_isConservativeOn
    (f : E →ₗ[R] F) (g : F →ₗ[R] G) (S : Submodule R E)
    (hf : ¬ IsConservativeOn f S) :
    ¬ IsConservativeOn (g.comp f) S := by
  intro hgf
  exact hf ((isConservativeOn_comp_iff f g S).mp hgf).1

/-- Failure at a later stage on the propagated source sector is failure of the whole route. -/
theorem not_isConservativeOn_comp_of_not_isConservativeOn_map
    (f : E →ₗ[R] F) (g : F →ₗ[R] G) (S : Submodule R E)
    (hg : ¬ IsConservativeOn g (S.map f)) :
    ¬ IsConservativeOn (g.comp f) S := by
  intro hgf
  exact hg ((isConservativeOn_comp_iff f g S).mp hgf).2

/-! ## Quantitative chain law -/

variable {K E₁ F₁ G₁ : Type*}
variable [NormedField K]
variable [NormedAddCommGroup E₁] [NormedSpace K E₁]
variable [NormedAddCommGroup F₁] [NormedSpace K F₁]
variable [SeminormedAddCommGroup G₁] [NormedSpace K G₁]

/-- Uniform lower bounds multiply along a source-pointed route. -/
theorem isUniformlyConservativeOn_comp
    (f : E₁ →ₗ[K] F₁) (g : F₁ →ₗ[K] G₁) (S : Submodule K E₁)
    (hf : IsUniformlyConservativeOn f S)
    (hg : IsUniformlyConservativeOn g (S.map f)) :
    IsUniformlyConservativeOn (g.comp f) S := by
  obtain ⟨cf, hcf, hboundf⟩ := hf
  obtain ⟨cg, hcg, hboundg⟩ := hg
  refine ⟨cg * cf, mul_pos hcg hcf, ?_⟩
  intro x hxS
  have hfxS : f x ∈ S.map f := ⟨x, hxS, rfl⟩
  calc
    (cg * cf) * ‖x‖ = cg * (cf * ‖x‖) := by ring
    _ ≤ cg * ‖f x‖ := mul_le_mul_of_nonneg_left (hboundf x hxS) (le_of_lt hcg)
    _ ≤ ‖g (f x)‖ := hboundg (f x) hfxS
    _ = ‖(g.comp f) x‖ := rfl

end

end GaloisForLFunctions.HTGeometry
