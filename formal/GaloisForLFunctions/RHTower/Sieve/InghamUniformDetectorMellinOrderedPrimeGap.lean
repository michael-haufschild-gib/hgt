import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselEveryBase
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Route T ordered-prime gap consequence

The every-base Hoheisel supply is upgraded from an existential prime witness to a statement about
every sufficiently late genuine consecutive prime gap.  Minimality of the ordered prime enumeration
is the source-faithful bridge: any prime strictly above the `n`th prime bounds the `(n+1)`st prime.
-/

open Complex Filter Topology Set Finset

namespace RHTower.Sieve

noncomputable section

/-- Every sufficiently late ordered prime gap inherits the Route-T every-base exponent. -/
theorem eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase :
    ∀ᶠ n : ℕ in atTop,
      (RHTower.nthPrimeSubtype (n + 1) : ℝ) -
          (RHTower.nthPrimeSubtype n : ℝ) ≤
        (RHTower.nthPrimeSubtype n : ℝ) ^ routeTHoheiselEveryBaseExponent := by
  have hprime := exists_eventually_routeT_prime_in_every_base_window
  have htend : Tendsto (fun n : ℕ => (RHTower.nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp RHTower.nthPrimeSubtype_strictMono.tendsto_atTop
  filter_upwards [htend.eventually hprime] with n hn
  obtain ⟨q, hqPrime, hqLower, hqUpper⟩ := hn
  have hqLowerNat : (RHTower.nthPrimeSubtype n : ℕ) < q := by
    exact_mod_cast hqLower
  have hnextLe : (RHTower.nthPrimeSubtype (n + 1) : ℕ) ≤ q := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime (n + 1)
    change Nat.nth Nat.Prime (n + 1) ≤ q
    apply hleast.2
    refine ⟨hqPrime, ?_⟩
    intro k hk
    have hkn : k ≤ n := by omega
    have hmono : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime n :=
      Nat.nth_monotone Nat.infinite_setOf_prime hkn
    exact hmono.trans_lt (by simpa [RHTower.nthPrimeSubtype] using hqLowerNat)
  have hnextLeReal : (RHTower.nthPrimeSubtype (n + 1) : ℝ) ≤ q := by
    exact_mod_cast hnextLe
  linarith

/-- Every sufficiently late actual gap is strictly narrower than every upper-phase physical
window.  Thus genuine consecutive gaps eventually occupy only Route T's lower physical-slice
regime. -/
theorem eventually_nthPrimeSubtype_succ_gap_lt_routeT_upperPhase_width
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    ∀ᶠ n : ℕ in atTop,
      (RHTower.nthPrimeSubtype (n + 1) : ℝ) -
          (RHTower.nthPrimeSubtype n : ℝ) <
        (RHTower.nthPrimeSubtype n : ℝ) ^ (1 - 1 / mu) := by
  filter_upwards [eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase]
      with n hgap
  have hp1 : (1 : ℝ) < (RHTower.nthPrimeSubtype n : ℝ) := by
    exact_mod_cast (RHTower.nthPrimeSubtype n).prop.one_lt
  have hpow :
      (RHTower.nthPrimeSubtype n : ℝ) ^ routeTHoheiselEveryBaseExponent <
        (RHTower.nthPrimeSubtype n : ℝ) ^ (1 - 1 / mu) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1
      (routeTHoheiselEveryBaseExponent_lt_widthExponent hmu)
  exact hgap.trans_lt hpow

end

end RHTower.Sieve
