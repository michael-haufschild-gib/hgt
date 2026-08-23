import GaloisForLFunctions.RHTower.BurnolQuotientContour
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The entire representative of `M(f)/ζ`

When `ζ` divides the continued Mellin transform at every point — which is what orthogonality to all
the evaluators says — the quotient `M(f)/ζ` has nonnegative meromorphic order everywhere.  In Lean
the quotient still carries junk values at the zeros of `ζ`, so the honest entire function is the
*meromorphic normal form* of the quotient; it agrees with the quotient at every point where the
latter is already analytic.

## Main results

* `burnolQuotientNF`
* `differentiable_burnolQuotientNF`
* `burnolQuotientNF_eq_of_analyticAt`
-/

open Complex Set Topology Filter

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The entire representative of `G/ζ`. -/
def burnolQuotientNF (G : ℂ → ℂ) : ℂ → ℂ := toMeromorphicNFOn (burnolQuotient G) Set.univ

theorem meromorphicOn_burnolQuotient {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) :
    MeromorphicOn (burnolQuotient G) Set.univ := fun z _ => meromorphicAt_burnolQuotient (hG z)

theorem burnolQuotientNF_eventuallyEq {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (z : ℂ) :
    burnolQuotientNF G =ᶠ[𝓝[≠] z] burnolQuotient G :=
  (meromorphicOn_burnolQuotient hG).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)

theorem meromorphicOrderAt_burnolQuotientNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (z : ℂ) :
    meromorphicOrderAt (burnolQuotientNF G) z = meromorphicOrderAt (burnolQuotient G) z :=
  meromorphicOrderAt_congr (burnolQuotientNF_eventuallyEq hG z)

/-- **The normal form is entire** as soon as every order is nonnegative. -/
theorem differentiable_burnolQuotientNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s)
    (hord : ∀ z : ℂ, 0 ≤ meromorphicOrderAt (burnolQuotient G) z) :
    Differentiable ℂ (burnolQuotientNF G) := by
  intro z
  have hNF : MeromorphicNFAt (burnolQuotientNF G) z :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ z)
  have hana : AnalyticAt ℂ (burnolQuotientNF G) z := by
    refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [meromorphicOrderAt_burnolQuotientNF hG z]
    exact hord z
  exact hana.differentiableAt

theorem burnolQuotientNF_eq_of_analyticAt {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {z : ℂ}
    (h : AnalyticAt ℂ (burnolQuotient G) z) :
    burnolQuotientNF G z = burnolQuotient G z := by
  have hmero := meromorphicOn_burnolQuotient hG
  simp [burnolQuotientNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

end

end RHTower
