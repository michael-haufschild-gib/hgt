import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonClosedRange

/-!
# The radial space is Fréchet and the cokernel is separated

The compatibility conditions defining the radial space are closed, so the radial space is a closed
subspace of a countable product of copies of `𝓢(ℝ, ℂ)` and therefore complete.  The image of the
Poisson operator is closed in it, so the cokernel `M_ζ` is a separated topological vector space and
the projection onto it is an open map: the Poisson sequence is a strict exact sequence.

* `deningerRadialCompat_isClosed` : the radial space is closed in the product.
* `instCompleteSpaceDeningerRadialCompat` : the radial space is complete.
* `deningerMZeta_t2Space` : **the cokernel is separated.**
* `deningerMZetaMk_isOpenMap` : **the projection onto the cokernel is open.**
-/

open scoped Real SchwartzMap Topology
open Filter Complex GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The radial space is closed in the product -/

/-- **The radial space is closed**: it is cut out by the continuous compatibility equations
`g_s(t) = e^{st} g_0(t)`. -/
theorem deningerRadialCompat_isClosed :
    IsClosed ((deningerRadialCompat : Submodule ℂ (∀ _ : ℤ, 𝓢(ℝ, ℂ))) :
      Set (∀ _ : ℤ, 𝓢(ℝ, ℂ))) := by
  have hset : ((deningerRadialCompat : Submodule ℂ (∀ _ : ℤ, 𝓢(ℝ, ℂ))) :
      Set (∀ _ : ℤ, 𝓢(ℝ, ℂ)))
      = ⋂ s : ℤ, ⋂ t : ℝ,
        {g : ∀ _ : ℤ, 𝓢(ℝ, ℂ) | g s t = Complex.exp ((s : ℂ) * t) * g 0 t} := by
    ext g
    constructor
    · intro hg
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro s t
      exact hg s t
    · intro hg s t
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hg s) t
  rw [hset]
  refine isClosed_iInter fun s => isClosed_iInter fun t => ?_
  have hleft : Continuous fun g : ∀ _ : ℤ, 𝓢(ℝ, ℂ) => (g s) t := by
    exact (deningerSchwartzEval t).continuous.comp (continuous_apply s)
  have hright : Continuous fun g : ∀ _ : ℤ, 𝓢(ℝ, ℂ) => Complex.exp ((s : ℂ) * t) * (g 0) t := by
    exact continuous_const.mul ((deningerSchwartzEval t).continuous.comp (continuous_apply 0))
  exact isClosed_eq hleft hright

instance instCompleteSpaceDeningerRadialCompat : CompleteSpace deningerRadialCompat := by
  have hcl : IsClosed ((deningerRadialCompat : Submodule ℂ (∀ _ : ℤ, 𝓢(ℝ, ℂ))) :
      Set (∀ _ : ℤ, 𝓢(ℝ, ℂ))) := deningerRadialCompat_isClosed
  exact hcl.isComplete.completeSpace_coe

/-! ## The cokernel is separated -/

theorem deningerPoisson_range_submodule_isClosed :
    IsClosed ((LinearMap.range (deningerPoissonLM) : Submodule ℂ deningerRadialCompat) :
      Set deningerRadialCompat) := by
  have hset : ((LinearMap.range (deningerPoissonLM) : Submodule ℂ deningerRadialCompat) :
      Set deningerRadialCompat) = Set.range deningerPoissonLM := by
    ext x
    exact LinearMap.mem_range
  rw [hset]
  exact deningerPoisson_range_isClosed

/-- **The cokernel of the Poisson operator is separated.** -/
theorem deningerMZeta_t2Space : T2Space DeningerMZeta := by
  haveI : IsClosed (((LinearMap.range (deningerPoissonLM) :
      Submodule ℂ deningerRadialCompat).toAddSubgroup) : Set deningerRadialCompat) :=
    deningerPoisson_range_submodule_isClosed
  infer_instance

/-- **The projection onto the cokernel is an open map**: the Poisson sequence is strict at the
radial space. -/
theorem deningerMZetaMk_isOpenMap : IsOpenMap (deningerMZetaMk) := by
  exact QuotientAddGroup.isOpenMap_coe

end RHTower

end
