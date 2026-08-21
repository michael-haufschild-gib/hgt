import GaloisForLFunctions.HTGeometry.ConstitutiveLawHistoryDifferential
import GaloisForLFunctions.HTGeometry.ConstitutiveCarrierComposition

/-!
# The two pages of the local law-history differential

For composable linear laws `X --f--> Y --g--> Z` the transgression
`∂ : ker g → Y ⧸ range f` has canonical kernel and cokernel:

* its kernel is `ker (g ∘ f) ⧸ ker f`;
* its cokernel is `Y ⧸ (range f + ker g)`, canonically the kernel of
  `Z ⧸ range (g ∘ f) → Z ⧸ range g`.

In finite dimensions this yields the alternating-sum conservation law of the six-term sequence
and the two fine dimension identities that split composite kernel and composite cokernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {k : Type u} {X : Type v} {Y : Type w} {Z : Type x}
variable [Field k]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z]

/-- **The kernel page.**  The kernel of the transgression is the composite kernel modulo the
earlier kernel: `ker ∂ ≅ ker (g ∘ f) / ker f`, the earlier kernel being carried inside the
composite kernel by the canonical inclusion. -/
def kernelPageEquiv (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    (LinearMap.ker (g.comp f) ⧸ LinearMap.range (kernelToCompositeKernel f g))
      ≃ₗ[k] LinearMap.ker (lawHistoryDifferential f g) :=
  ((Submodule.quotEquivOfEq _ _ (range_kernelToCompositeKernel_eq_ker f g)).trans
    (LinearMap.quotKerEquivRange (compositeKernelToLaterKernel f g))).trans
    (LinearEquiv.ofEq _ _ (range_compositeKernelToLaterKernel_eq_ker f g))

/-- The earlier kernel is carried isomorphically onto its image in the composite kernel. -/
def kerEquivRangeKernelToCompositeKernel (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.ker f ≃ₗ[k] LinearMap.range (kernelToCompositeKernel f g) :=
  LinearEquiv.ofInjective _ (kernelToCompositeKernel_injective f g)

/-- The image of the transgression is the saturated sum read in the earlier cokernel. -/
theorem range_lawHistoryDifferential_eq_map (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range (lawHistoryDifferential f g)
      = Submodule.map (LinearMap.range f).mkQ (LinearMap.range f ⊔ LinearMap.ker g) := by
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, Submodule.mem_sup_right y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [lawHistoryDifferential_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    have : b - (a + b) = -a := by abel
    rw [this]
    exact Submodule.neg_mem _ ha

/-- **The cokernel page.**  The cokernel of the transgression is the secondary birth space
`Y / (range f + ker g)`. -/
def cokernelPageEquiv (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    ((Y ⧸ LinearMap.range f) ⧸ LinearMap.range (lawHistoryDifferential f g))
      ≃ₗ[k] (Y ⧸ (LinearMap.range f ⊔ LinearMap.ker g)) :=
  (Submodule.quotEquivOfEq _ _ (range_lawHistoryDifferential_eq_map f g)).trans
    (Submodule.quotientQuotientEquivQuotient (LinearMap.range f)
      (LinearMap.range f ⊔ LinearMap.ker g) le_sup_left)

/-- **The cokernel page is the outer kernel.**  The cokernel of the transgression is canonically
the kernel of `Z / range (g ∘ f) → Z / range g`. -/
def cokernelPageEquivKerOuter (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    ((Y ⧸ LinearMap.range f) ⧸ LinearMap.range (lawHistoryDifferential f g))
      ≃ₗ[k] LinearMap.ker (compositeToOuter f g) :=
  ((Submodule.quotEquivOfEq _ _ (range_lawHistoryDifferential_eq_ker f g)).trans
    (LinearMap.quotKerEquivRange (earlierCokerToCompositeCoker f g))).trans
    (LinearEquiv.ofEq _ _ (range_earlierCokerToCompositeCoker_eq_ker f g))

/-- **Secondary birth is the outer kernel.**  Combining the two descriptions of the cokernel page:
the secondary birth space is the kernel of the outer comparison of cokernels. -/
def secondaryBirthEquivKerOuter (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    (Y ⧸ (LinearMap.range f ⊔ LinearMap.ker g))
      ≃ₗ[k] LinearMap.ker (compositeToOuter f g) :=
  (cokernelPageEquiv f g).symm.trans (cokernelPageEquivKerOuter f g)

section FiniteDimensional

variable [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]

/-- **Alternating-sum conservation.**  The six-term sequence has vanishing Euler characteristic. -/
theorem lawHistory_alternating_sum_eq_zero (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    (Module.finrank k (LinearMap.ker f) : ℤ)
      - Module.finrank k (LinearMap.ker (g.comp f))
      + Module.finrank k (LinearMap.ker g)
      - Module.finrank k (Y ⧸ LinearMap.range f)
      + Module.finrank k (Z ⧸ LinearMap.range (g.comp f))
      - Module.finrank k (Z ⧸ LinearMap.range g) = 0 := by
  have h1 := finiteLawIndex_eq_finrank_sub f
  have h2 := finiteLawIndex_eq_finrank_sub (g.comp f)
  have h3 := finiteLawIndex_eq_finrank_sub g
  unfold finiteLawIndex at h1 h2 h3
  omega

omit [FiniteDimensional k Y] [FiniteDimensional k Z] in
/-- **Composite kernel splits.**  The composite kernel is the earlier kernel plus the kernel of
the transgression. -/
theorem finrank_ker_comp_eq (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Module.finrank k (LinearMap.ker (g.comp f))
      = Module.finrank k (LinearMap.ker f)
        + Module.finrank k (LinearMap.ker (lawHistoryDifferential f g)) := by
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (kernelToCompositeKernel f g))
  have hker : Module.finrank k (LinearMap.range (kernelToCompositeKernel f g))
      = Module.finrank k (LinearMap.ker f) :=
    ((kerEquivRangeKernelToCompositeKernel f g).finrank_eq).symm
  have hpage :
      Module.finrank k
          (LinearMap.ker (g.comp f) ⧸ LinearMap.range (kernelToCompositeKernel f g))
        = Module.finrank k (LinearMap.ker (lawHistoryDifferential f g)) :=
    (kernelPageEquiv f g).finrank_eq
  omega

omit [FiniteDimensional k X] [FiniteDimensional k Y] in
/-- **Composite cokernel splits.**  The composite cokernel is the cokernel of the transgression
plus the outer cokernel. -/
theorem finrank_quotient_range_comp_eq (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Module.finrank k (Z ⧸ LinearMap.range (g.comp f))
      = Module.finrank k
          ((Y ⧸ LinearMap.range f) ⧸ LinearMap.range (lawHistoryDifferential f g))
        + Module.finrank k (Z ⧸ LinearMap.range g) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (compositeToOuter f g)
  have hsurj : LinearMap.range (compositeToOuter f g) = ⊤ :=
    LinearMap.range_eq_top.2 (compositeToOuter_surjective f g)
  have htop : Module.finrank k (LinearMap.range (compositeToOuter f g))
      = Module.finrank k (Z ⧸ LinearMap.range g) := by
    rw [hsurj, finrank_top]
  have hpage : Module.finrank k
      ((Y ⧸ LinearMap.range f) ⧸ LinearMap.range (lawHistoryDifferential f g))
      = Module.finrank k (LinearMap.ker (compositeToOuter f g)) :=
    (cokernelPageEquivKerOuter f g).finrank_eq
  omega

end FiniteDimensional

end

end GaloisForLFunctions.HTGeometry
