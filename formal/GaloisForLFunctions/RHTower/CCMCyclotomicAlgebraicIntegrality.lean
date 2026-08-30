import GaloisForLFunctions.RHTower.CCMCyclotomicLambertIntegrality

/-!
# Algebraic integrality of the concrete CCM cyclotomic ring

`CCMCyclotomicInteger` is deliberately concrete: a finite integral linear
combination of complex roots of unity.  The original CCM coefficient theorem
uses the standard algebraic-number-theoretic consequence that this concrete
ring consists of algebraic integers.  This leaf supplies that bridge directly:
a root of unity is integral because a positive power is one; integral elements
are closed under multiplication by integer scalars and finite addition.

The result is intentionally separate from the unresolved quadratic-field
intersection `ℚ(√2) ∩ ℤ^cyc[1/2] = ℤ[1/√2]`.  It is the exact integrality input
needed before that arithmetic intersection can be formalized.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every concrete complex root of unity is integral over `ℤ`. -/
theorem CCMRootOfUnity.isIntegral {z : ℂ} (hz : CCMRootOfUnity z) :
    IsIntegral ℤ z := by
  rcases hz with ⟨n, hn, hpow⟩
  apply IsIntegral.of_pow hn
  rw [hpow]
  exact isIntegral_one

/-- The concrete finite-sum realization of `ℤ^cyc` lies in the algebraic
integers of `ℂ`. -/
theorem CCMCyclotomicInteger.isIntegral {z : ℂ} (hz : CCMCyclotomicInteger z) :
    IsIntegral ℤ z := by
  rcases hz with ⟨ι, hι, c, ζ, hζ, hz⟩
  rw [hz]
  apply IsIntegral.sum
  intro i _
  apply IsIntegral.mul
  · exact isIntegral_algebraMap
  · exact (hζ i).isIntegral

/-- Cyclotomic containment implies the pre-existing dyadic algebraic
integrality predicate without re-proving the individual Lambert radical
estimates. -/
theorem CCMDyadicCyclotomicInteger.dyadicIntegral {z : ℂ}
    (hz : CCMDyadicCyclotomicInteger z) : CCMDyadicIntegral z := by
  rcases hz with ⟨d, hd⟩
  exact ⟨d, hd.isIntegral⟩

end

end RHTower
