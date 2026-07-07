import GaloisForLFunctions.RHTower.PrimeDivisorAtomsNoGo
import GaloisForLFunctions.RHTower.SigmaDivisorJet

/-!
# Exhaustion of the current pinned sigma-divisor sources

At one pinned strip zero, the currently available `{sigma_p}` source channels split into two
local forms:

* prime atoms coming from the local Euler factors themselves;
* multiplicative local deformations of the zeroed germ.

The first channel is zero because every finite Euler layer is a unit in the strip.  The second
channel is zero in the local divisor-jet algebra `R[X]/(X^m)`.  This module packages those two
formal facts in one pinned-annulus statement.
-/

noncomputable section

namespace RHTower

open Complex Finset Polynomial

/-- **The current pinned sigma-divisor sources are exhausted.**  At a strip zero of `xi`,
prime-local atom maps are zero, finite prime atlases have order `0`, the `xi` order is nonzero,
and multiplicative sigma deformations have no nontrivial local divisor jet.

This statement uses no character group and no positivity cone.  It says only that the source
data currently present in the pinned `{sigma_p}` lanes do not yield a divisor refinement finer
than multiplicity. -/
theorem pinnedSigmaDivisorSources_killed {R Sigma : Type*} [CommRing R] (m : ℕ)
    (u : Polynomial R) (hjet : Sigma → Polynomial R)
    {ρ : ℂ} (hs : 0 < ρ.re) (hz : xi ρ = 0)
    {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {A : ℕ → ℕ} (hA : SigmaSourceMap A ρ) :
    (∀ p, 2 ≤ p → A p = 0) ∧
      analyticOrderAt (eulerPartial P) ρ = 0 ∧
      analyticOrderAt xi ρ ≠ 0 ∧
      ¬ HasNontrivialSigmaJet m
        (fun p => (((Polynomial.X : Polynomial R) ^ m) * u) * hjet p) := by
  exact ⟨sigma_source_map_trivial hs hA,
    eulerPartial_orderAt_zero hP hs,
    xi_zero_order_ne_zero hz,
    no_nontrivialSigmaJet_of_unit_multiplicative m u hjet⟩

/-- The same exhaustion, with the additive Euler-Maclaurin split present: the additive
carrier sees at least one local zero atom, while every prime-local source map and every
multiplicative sigma jet remains zero. -/
theorem pinnedSigmaDivisorSources_mismatch_with_emSplit {R Sigma : Type*} [CommRing R] (m : ℕ)
    (u0 : Polynomial R) (hjet : Sigma → Polynomial R)
    {ρ : ℂ} (hs : 0 < ρ.re) (hz : xi ρ = 0)
    {A : ℕ → ℕ} (hA : SigmaSourceMap A ρ)
    {r₀ R₀ : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hdata : EMSplitData ρ r₀ R₀ N zs u) :
    (∀ p, 2 ≤ p → A p = 0) ∧
      1 ≤ zs.length ∧
      ¬ HasNontrivialSigmaJet m
        (fun p => (((Polynomial.X : Polynomial R) ^ m) * u0) * hjet p) := by
  exact ⟨sigma_source_map_trivial hs hA,
    emSplit_length_pos_at_xi_zero hz hdata,
    no_nontrivialSigmaJet_of_unit_multiplicative m u0 hjet⟩

end RHTower
