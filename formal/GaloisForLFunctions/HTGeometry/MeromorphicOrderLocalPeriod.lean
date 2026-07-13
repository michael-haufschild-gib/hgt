import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Meromorphic order under a punctured-local period

Meromorphic order ignores the value at the center. Consequently a functional period identity only
on a punctured neighborhood transports the order exactly, even when the displayed pointwise
functional equation is intentionally totalized at its poles.
-/

open Complex Filter Topology

namespace GaloisForLFunctions

noncomputable section

theorem meromorphicOrderAt_add_eq_of_eventually_periodic
    {f : ℂ → ℂ} {p t : ℂ}
    (hper : ∀ᶠ z in 𝓝[≠] p, f (z + t) = f z) :
    meromorphicOrderAt f (p + t) = meromorphicOrderAt f p := by
  let g : ℂ → ℂ := fun z => z + t
  have hg : AnalyticAt ℂ g p := analyticAt_id.add analyticAt_const
  have hgd : deriv g p ≠ 0 := by simp [g]
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hgd
  calc
    meromorphicOrderAt f (p + t) = meromorphicOrderAt (f ∘ g) p := by
      simpa [g] using hcomp.symm
    _ = meromorphicOrderAt f p := by
      apply meromorphicOrderAt_congr
      simpa [g, Function.comp_def] using hper

end

end GaloisForLFunctions
