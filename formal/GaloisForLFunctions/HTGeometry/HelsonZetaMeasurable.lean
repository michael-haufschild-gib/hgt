import Mathlib
import GaloisForLFunctions.HTGeometry.HelsonEulerMultipliable
import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOneEquiv

/-!
# The Helson zeta value is a measurable function of the phase

For a fixed `s` with `Re s > 1` the Euler product converges for every phase, so

```text
Z(χ, s) = ∏_p (1 - χ_p p^{-s})⁻¹
```

is defined on the whole phase torus.  Enumerating the primes turns the product into a limit of finite
partial products, each of which is a continuous — hence measurable — function of `χ`, so the value is
measurable.

This is the first step any measurability statement about the continuation stratum needs: the object
whose continuation is in question must itself be a measurable function of the phase.
-/

open Complex Filter Topology MeasureTheory

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Helson zeta value at a point of the half plane of absolute convergence. -/
def helsonZetaValue (s : ℂ) (χ : PhaseTorus) : ℂ :=
  ∏' p : Nat.Primes, (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹

/-- Each Euler factor is a measurable function of the phase. -/
theorem measurable_eulerFactor (s : ℂ) (p : Nat.Primes) :
    Measurable (fun χ : PhaseTorus => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have hcoord : Measurable (fun χ : PhaseTorus => (χ p : ℂ)) :=
    (measurable_subtype_coe).comp (measurable_pi_apply p)
  exact ((measurable_const.sub (hcoord.mul measurable_const)).inv)

/-- **The Helson zeta value is measurable in the phase.** -/
theorem measurable_helsonZetaValue {s : ℂ} (hs : 1 < s.re) :
    Measurable (helsonZetaValue s) := by
  set e := natEquivPrimes with he
  have hpart : ∀ N : ℕ, Measurable (fun χ : PhaseTorus =>
      ∏ i ∈ Finset.range N, (1 - (χ (e i) : ℂ) * ((e i : ℕ) : ℂ) ^ (-s))⁻¹) := by
    intro N
    exact Finset.measurable_prod _ fun i _ => measurable_eulerFactor s (e i)
  refine measurable_of_tendsto_metrizable hpart ?_
  rw [tendsto_pi_nhds]
  intro χ
  have hunit : ∀ p : Nat.Primes, ‖(χ p : ℂ)‖ ≤ 1 := fun p => le_of_eq (χ p).2
  have hmul := multipliable_helsonEuler hunit hs
  have hhas := hmul.hasProd
  have hcomp : HasProd (fun i : ℕ => (1 - (χ (e i) : ℂ) * ((e i : ℕ) : ℂ) ^ (-s))⁻¹)
      (helsonZetaValue s χ) := by
    rw [helsonZetaValue]
    exact (Equiv.hasProd_iff e).2 hhas
  exact hcomp.tendsto_prod_nat

end GaloisForLFunctions.HTGeometry

end
