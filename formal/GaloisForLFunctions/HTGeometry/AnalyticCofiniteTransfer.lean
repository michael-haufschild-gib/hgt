import GaloisForLFunctions.HTGeometry.GammaMonomialShift

/-!
# From a half plane to the cofinite filter

The functional equation of a Gamma monomial holds on a right half plane, not cofinitely: the poles
of `Γ` are infinite in number.  Every obstruction in this repository, on the other hand, consumes a
*cofinite* identity, because the orbit-mass argument has to see the whole orbit `a + ℤ`.

The transfer is the identity theorem.  Two functions analytic off a finite set, agreeing on some
nonempty open piece of the complement, agree on the whole complement — the complement of a finite
set in `ℂ` is connected because `ℂ` has real rank two — and hence cofinitely.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem isPreconnected_compl_finite {S : Set ℂ} (hS : S.Finite) : IsPreconnected (Sᶜ : Set ℂ) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (hS.countable.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected

/-- **Half plane to cofinite.**  Two functions analytic off a finite set that agree on a nonempty
open piece of the complement agree cofinitely. -/
theorem eventuallyEq_cofinite_of_analytic_compl_finite {S : Set ℂ} (hS : S.Finite)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Sᶜ) (hg : AnalyticOnNhd ℂ g Sᶜ)
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U ∩ Sᶜ)
    (heq : ∀ z ∈ U ∩ Sᶜ, f z = g z) :
    f =ᶠ[Filter.cofinite] g := by
  have hconn : IsPreconnected (Sᶜ : Set ℂ) := isPreconnected_compl_finite hS
  have hopen : IsOpen (U ∩ Sᶜ) := hU.inter hS.isClosed.isOpen_compl
  have hnb : f =ᶠ[nhds z₀] g := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz
    exact heq z hz
  have heqon := hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hz₀.2 hnb
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  refine Set.Finite.subset hS ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  by_contra hcon
  exact hz (heqon hcon)

end

end GaloisForLFunctions.HTGeometry
