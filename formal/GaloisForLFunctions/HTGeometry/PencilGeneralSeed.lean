import GaloisForLFunctions.HTGeometry.PencilSRRealization

/-!
# A pencil source with prescribed facet sources

The exponential seed of a periodic pencil plays no role in the annihilator half of the realization:
what matters is only that a step outside a facet is a period of that facet's phase.  So an arbitrary
choice of one source per facet gives a carrier annihilated by every nonface product, and the carrier
of a difference operator expands as a finite combination of translates of the individual facet
sources.

With joint hypertranscendence of those translates this gives the exact Stanley--Reisner annihilator
for the *same* source that carries the differential matroid.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α] {facets : Finset (Finset α)} {E : Type*} [AddCommMonoid E]

namespace PencilSeparation

/-- The phase composite of one facet with a prescribed source. -/
def facetSource (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ) (A : Finset α) : E → ℂ :=
  fun z => Ψ A (Complex.exp (S.phase A z))

/-- A general pencil source: one prescribed source per facet. -/
def genSeed (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ) : E → ℂ :=
  fun z => ∑ A ∈ facets, S.facetSource Ψ A z

omit [DecidableEq α] in
/-- A step outside a facet leaves that facet's source invariant. -/
theorem shiftAlgHom_stepVar_facetSource (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ)
    {A : Finset α} (hA : A ∈ facets) {v : α} (hv : v ∉ A) :
    shiftAlgHom (stepVar S.ω v) (S.facetSource Ψ A) = 0 := by
  funext z
  rw [shiftAlgHom_stepVar]
  show Ψ A (Complex.exp (S.phase A (z + S.ω v))) - Ψ A (Complex.exp (S.phase A z)) = 0
  rw [map_add, Complex.exp_add, S.outside A hA v hv, mul_one, sub_self]

/-- **The nonface products annihilate a general pencil source.** -/
theorem genSeedAnnihilates (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ) :
    SeedAnnihilates S.ω facets (S.genSeed Ψ) := by
  intro J hJ
  have hzero : ∀ A ∈ facets,
      shiftAlgHom (∏ v ∈ J, stepVar S.ω v) (S.facetSource Ψ A) = 0 := by
    intro A hA
    obtain ⟨v, hvJ, hvA⟩ : ∃ v ∈ J, v ∉ A := by
      by_contra hcon
      exact hJ ⟨A, Finset.mem_coe.mpr hA, by
        intro x hx
        by_contra hxA
        exact hcon ⟨x, hx, hxA⟩⟩
    have hfac : (∏ u ∈ J, stepVar S.ω u)
        = (∏ u ∈ J.erase v, stepVar S.ω u) * stepVar S.ω v := by
      rw [mul_comm, Finset.mul_prod_erase J _ hvJ]
    rw [hfac, map_mul]
    show shiftAlgHom (∏ u ∈ J.erase v, stepVar S.ω u)
      (shiftAlgHom (stepVar S.ω v) (S.facetSource Ψ A)) = 0
    rw [S.shiftAlgHom_stepVar_facetSource Ψ hA hvA, map_zero]
  have hfun : S.genSeed Ψ = ∑ A ∈ facets, S.facetSource Ψ A := by
    funext w
    rw [Finset.sum_apply]
    rfl
  show shiftAlgHom (∏ v ∈ J, stepVar S.ω v) (S.genSeed Ψ) = 0
  rw [hfun, map_sum]
  exact Finset.sum_eq_zero hzero

omit [DecidableEq α] in
/-- **The carrier of a difference operator is a finite combination of facet-source translates.** -/
theorem seedCarrierPoly_genSeed (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ)
    (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly S.ω (S.genSeed Ψ) P z =
      ∑ A ∈ facets, ∑ γ ∈ (polyShift S.ω P).coeff.support,
        (polyShift S.ω P).coeff γ *
          Ψ A (Complex.exp (S.phase A z) * Complex.exp (S.phase A γ)) := by
  have hfun : S.genSeed Ψ = fun w => ∑ A ∈ facets, S.facetSource Ψ A w := rfl
  rw [hfun, seedCarrierPoly_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [seedCarrierPoly, shiftAlgHom_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  show Ψ A (Complex.exp (S.phase A (z + γ))) = _
  rw [map_add, Complex.exp_add]

end PencilSeparation

end

end GaloisForLFunctions.HTGeometry
