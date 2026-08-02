import GaloisForLFunctions.HTGeometry.SourcePointedConservativityChainLaw

/-!
# Source-pointed observation network law

Serial postprocessing can only enlarge an invisible source radical.  Parallel observation before
loss replaces the two radicals by their intersection.  Together with the conservativity chain law,
these identities give a calculus for finite source-pointed observation networks.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R E F G H : Type*}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]
variable [AddCommGroup H] [Module R H]

/-- Two observations retained in parallel before either output is forgotten. -/
def pairedObservation (f : E →ₗ[R] F) (h : E →ₗ[R] H) : E →ₗ[R] F × H :=
  f.prod h

@[simp]
theorem pairedObservation_apply (f : E →ₗ[R] F) (h : E →ₗ[R] H) (x : E) :
    pairedObservation f h x = (f x, h x) :=
  rfl

/-- Parallel observation intersects, rather than adds, the invisible radicals. -/
theorem ker_pairedObservation (f : E →ₗ[R] F) (h : E →ₗ[R] H) :
    LinearMap.ker (pairedObservation f h) = LinearMap.ker f ⊓ LinearMap.ker h := by
  ext x
  simp [pairedObservation]

/-- A resolved pair is conservative exactly when its two marginal radicals have no common
nonzero source direction. -/
theorem isConservativeOn_paired_iff
    (f : E →ₗ[R] F) (h : E →ₗ[R] H) (S : Submodule R E) :
    IsConservativeOn (pairedObservation f h) S ↔
      Disjoint S (LinearMap.ker f ⊓ LinearMap.ker h) := by
  rw [IsConservativeOn, ker_pairedObservation]

/-- Pointwise common-radical form of parallel conservativity. -/
theorem isConservativeOn_paired_iff_pointwise
    (f : E →ₗ[R] F) (h : E →ₗ[R] H) (S : Submodule R E) :
    IsConservativeOn (pairedObservation f h) S ↔
      ∀ x, x ∈ S → f x = 0 → h x = 0 → x = 0 := by
  rw [IsConservativeOn, Submodule.disjoint_def]
  constructor
  · intro hc x hxS hfx hhx
    apply hc x hxS
    change (f x, h x) = 0
    simp [hfx, hhx]
  · intro hc x hxS hxker
    change (f x, h x) = 0 at hxker
    have hfx : f x = 0 := congrArg Prod.fst hxker
    have hhx : h x = 0 := congrArg Prod.snd hxker
    exact hc x hxS hfx hhx

/-- Once a direction is invisible, every serial postprocessor remains blind to it. -/
theorem ker_le_ker_postprocess
    (f : E →ₗ[R] F) (g : F →ₗ[R] G) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp f) := by
  intro x hfx
  change g (f x) = 0
  rw [show f x = 0 from hfx, map_zero]

/-- A nonconservative observation cannot be repaired by any serial postprocessor. -/
theorem not_isConservativeOn_postprocess_of_not_isConservativeOn
    (f : E →ₗ[R] F) (g : F →ₗ[R] G) (S : Submodule R E)
    (hf : ¬ IsConservativeOn f S) :
    ¬ IsConservativeOn (g.comp f) S :=
  not_isConservativeOn_comp_of_not_isConservativeOn f g S hf

end

end GaloisForLFunctions.HTGeometry
