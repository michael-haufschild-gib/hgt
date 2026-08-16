import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogPrimeHarmonicGenusOne
import GaloisForLFunctions.RHTower.XiCentralDiscBound

/-!
# SP-E prime-harmonic divisor identification no-go

The literal prime-harmonic genus-one determinant has a forced source zero at `z = 1`: it is the
positive balanced channel over the depth-zero prime `2`.  Centered Xi is already certified nonzero
on the closed unit disc, hence in particular at the same point.

Therefore the explicit SP-E genus-one determinant is neither Xi nor normalized Xi.  More strongly,
no pointwise scalar multiplier can weld it to either target: multiplication cannot remove the
forced zero at `1`.  Any surviving source-to-Xi transport must change the source divisor itself,
for example through a spectrum-moving operator coupling; an entire nonvanishing gauge, scalar
counterterm, or arbitrary total scalar correction is impossible.
-/

open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

private def routePPrimitiveGammaJuliaPrimeTwo : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

/-- The positive balanced channel over the depth-zero prime `2` has eigenvalue exactly one. -/
theorem routePPrimitiveGammaJuliaLogBalancedMultiplier_two_zero :
    routePPrimitiveGammaJuliaLogBalancedMultiplier
      (0, (routePPrimitiveGammaJuliaPrimeTwo, 0)) = 1 := by
  rw [routePPrimitiveGammaJuliaLogBalancedMultiplier,
    routePPrimitiveGammaJuliaLogBalancedSpectralSign,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
  norm_num [routePPrimitiveGammaJuliaPrimeTwo]

/-- The literal SP-E prime-harmonic genus-one determinant has a forced zero at `1`. -/
theorem routePPrimitiveGammaJuliaLogBalancedEntireDet2_one_eq_zero :
    routePPrimitiveGammaJuliaLogBalancedEntireDet2 1 = 0 := by
  rw [routePPrimitiveGammaJuliaLogBalancedEntireDet2_zero_iff]
  refine ⟨(0, (routePPrimitiveGammaJuliaPrimeTwo, 0)), ?_⟩
  rw [routePPrimitiveGammaJuliaLogBalancedMultiplier_two_zero]
  norm_num

/-- Centered Xi is nonzero at the forced first SP-E source zero. -/
theorem XiC_one_ne_zero_for_routePPrimitiveGammaJuliaLog : XiC 1 ≠ 0 := by
  apply XiC_ne_zero_of_norm_le_one
  norm_num

/-- The central normalizing value of Xi is nonzero. -/
theorem XiC_zero_ne_zero_for_routePPrimitiveGammaJuliaLog : XiC 0 ≠ 0 := by
  apply XiC_ne_zero_of_norm_le_one
  norm_num

/-- Direct identification of the explicit SP-E genus-one determinant with Xi is impossible. -/
theorem routePPrimitiveGammaJuliaLogBalancedEntireDet2_ne_XiC :
    routePPrimitiveGammaJuliaLogBalancedEntireDet2 ≠ XiC := by
  intro h
  have h1 := congrFun h 1
  rw [routePPrimitiveGammaJuliaLogBalancedEntireDet2_one_eq_zero] at h1
  exact XiC_one_ne_zero_for_routePPrimitiveGammaJuliaLog h1.symm

/-- No total pointwise scalar correction can turn the explicit SP-E determinant into Xi. -/
theorem not_exists_mul_routePPrimitiveGammaJuliaLogBalancedEntireDet2_eq_XiC :
    ¬ ∃ g : ℂ → ℂ, ∀ z : ℂ,
      g z * routePPrimitiveGammaJuliaLogBalancedEntireDet2 z = XiC z := by
  rintro ⟨g, hg⟩
  have h1 := hg 1
  rw [routePPrimitiveGammaJuliaLogBalancedEntireDet2_one_eq_zero, mul_zero] at h1
  exact XiC_one_ne_zero_for_routePPrimitiveGammaJuliaLog h1.symm

/-- The explicit SP-E determinant also differs from the canonically normalized Xi function. -/
theorem routePPrimitiveGammaJuliaLogBalancedEntireDet2_ne_normalized_XiC :
    routePPrimitiveGammaJuliaLogBalancedEntireDet2 ≠
      fun z => XiC z / XiC 0 := by
  intro h
  have h1 := congrFun h 1
  rw [routePPrimitiveGammaJuliaLogBalancedEntireDet2_one_eq_zero] at h1
  exact (div_ne_zero XiC_one_ne_zero_for_routePPrimitiveGammaJuliaLog
    XiC_zero_ne_zero_for_routePPrimitiveGammaJuliaLog) h1.symm

/-- No total pointwise scalar correction can produce normalized Xi either. -/
theorem not_exists_mul_routePPrimitiveGammaJuliaLogBalancedEntireDet2_eq_normalized_XiC :
    ¬ ∃ g : ℂ → ℂ, ∀ z : ℂ,
      g z * routePPrimitiveGammaJuliaLogBalancedEntireDet2 z = XiC z / XiC 0 := by
  rintro ⟨g, hg⟩
  have h1 := hg 1
  rw [routePPrimitiveGammaJuliaLogBalancedEntireDet2_one_eq_zero, mul_zero] at h1
  exact (div_ne_zero XiC_one_ne_zero_for_routePPrimitiveGammaJuliaLog
    XiC_zero_ne_zero_for_routePPrimitiveGammaJuliaLog) h1.symm

end

end RHTower
