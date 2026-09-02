import GaloisForLFunctions.RHTower.JointAncestryGammaBooleanClosedCreation
import GaloisForLFunctions.RHTower.Sieve.KloostermanCoprimeProductPeriodCompletion

/-!
# Gamma-synchronized Kloosterman lcm interference no-go

The Gamma-sewn all-lcm source supplies a literal positive coefficient on every finite prime
support.  A tempting Route-E weld is to evaluate distinct-prime Kloosterman columns on the
squarefree lcm period selected by that same support.  At the first coupled rank `{p,r}`, however,
the lcm is `p*r`; CRT makes this a complete product period, so the entire cross-modulus current
vanishes for every pair of column labels.

The Gamma coefficient is strictly positive, hence cancellation does not arise by erasing source
coefficient provenance.  Complete lcm synchronization itself erases the interference.  Therefore
this weld cannot provide Route E's collective signed many-prime producer.  Its sharp positive
survivor is the incomplete product-shell boundary isolated in
`KloostermanCoprimeProductPeriodCompletion`.
-/

open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-- Literal Gamma-synchronized pair coefficient multiplying the Route-E cross-modulus current on
its squarefree lcm period. -/
def gammaSewnKloostermanPairCrossCurrent
    (x : ℝ) (p r : Nat.Primes) (n k : ℤ) : ℂ :=
  (gammaSewnSynchronizedLcmWeight x {p, r} : ℂ) *
    Sieve.kloostermanCrossModulusCorrelation
      (Finset.range ((p : ℕ) * (r : ℕ))) ((p : ℕ) - 1) ((r : ℕ) - 1) n k

/-- Source coefficient on the pair support remains strictly positive. -/
theorem gammaSewnKloostermanPairCoefficient_pos
    {x : ℝ} (hx : 0 < x) (p r : Nat.Primes) :
    0 < gammaSewnSynchronizedLcmWeight x {p, r} :=
  jasGammaSynchronizedLcmWeight_pos hx {p, r}

/-- Complete squarefree-lcm synchronization erases the entire distinct-prime Kloosterman
interference, coefficient-faithfully and for every pair of column labels. -/
theorem gammaSewnKloostermanPairCrossCurrent_eq_zero
    (x : ℝ) {p r : Nat.Primes} (hpr : p ≠ r) (n k : ℤ) :
    gammaSewnKloostermanPairCrossCurrent x p r n k = 0 := by
  have hp : 0 < (p : ℕ) - 1 := Nat.sub_pos_of_lt p.2.one_lt
  have hr : 0 < (r : ℕ) - 1 := Nat.sub_pos_of_lt r.2.one_lt
  have hcop : Nat.Coprime (((p : ℕ) - 1) + 1) (((r : ℕ) - 1) + 1) := by
    simpa [Nat.sub_add_cancel p.2.one_lt.le, Nat.sub_add_cancel r.2.one_lt.le] using
      (Nat.coprime_primes p.2 r.2).2 (Subtype.coe_ne_coe.mpr hpr)
  unfold gammaSewnKloostermanPairCrossCurrent
  rw [show Sieve.kloostermanCrossModulusCorrelation
      (Finset.range ((p : ℕ) * (r : ℕ))) ((p : ℕ) - 1) ((r : ℕ) - 1) n k = 0 by
    simpa [Nat.sub_add_cancel p.2.one_lt.le, Nat.sub_add_cancel r.2.one_lt.le] using
      Sieve.kloostermanCrossModulusCorrelation_range_mul_eq_zero
        ((p : ℕ) - 1) ((r : ℕ) - 1) hp hr hcop n k]
  exact mul_zero _

/-- Strong first-rank no-go: even a nonzero coefficient-faithful Gamma pair current is zero on
the synchronized lcm period. -/
theorem gammaSewnKloostermanPair_completeLcm_erases_interference
    {x : ℝ} (hx : 0 < x) {p r : Nat.Primes} (hpr : p ≠ r) (n k : ℤ) :
    gammaSewnSynchronizedLcmWeight x {p, r} ≠ 0 ∧
      gammaSewnKloostermanPairCrossCurrent x p r n k = 0 :=
  ⟨(gammaSewnKloostermanPairCoefficient_pos hx p r).ne',
    gammaSewnKloostermanPairCrossCurrent_eq_zero x hpr n k⟩

end

end RHTower
