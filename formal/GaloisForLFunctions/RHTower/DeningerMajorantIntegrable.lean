import GaloisForLFunctions.RHTower.DeningerAbelMajorant

/-!
# The Abel majorant is an integrable dominating function

The majorant has finite mass as an `ℝ≥0∞` integral, and it is measurable, so its real part is an
honest integrable function on the ray.  That is exactly the dominating function the dominated
convergence theorem needs in order to integrate the Abel series term by term.

* `deningerAbelMajorant_measurable` : the majorant is measurable.
* `deningerAbelMajorantReal` : its real form.
* `deningerAbelMajorantReal_integrable` : **it is integrable on the ray.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The majorant is measurable, being a countable sum of measurable terms. -/
theorem deningerAbelMajorant_measurable (h : 𝓢(ℝ, ℂ)) :
    Measurable (deningerAbelMajorant h) := by
  refine Measurable.tsum fun i => ?_
  exact (deningerAbelDifference_measurable h i).const_mul _

/-- The real form of the majorant. -/
def deningerAbelMajorantReal (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ :=
  (deningerAbelMajorant h x).toReal

/-- **The majorant is integrable on the ray**, so it dominates the Abel partial sums in the sense
the dominated convergence theorem requires. -/
theorem deningerAbelMajorantReal_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    IntegrableOn (deningerAbelMajorantReal h) (Set.Ioi 0) := by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact (deningerAbelMajorant_measurable h).aemeasurable
  · exact ne_of_lt (deningerAbelMajorant_mass_lt_top hh)

/-- The majorant is finite almost everywhere on the ray. -/
theorem deningerAbelMajorant_lt_top_ae {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), deningerAbelMajorant h x < ⊤ :=
  ae_lt_top (deningerAbelMajorant_measurable h)
    (ne_of_lt (deningerAbelMajorant_mass_lt_top hh))

end

end RHTower
