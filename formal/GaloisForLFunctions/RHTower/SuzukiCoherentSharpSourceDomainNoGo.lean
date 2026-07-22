import GaloisForLFunctions.RHTower.SuzukiCoherentResponseGainNoGo
import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo

/-!
# The coherent Suzuki sharp source has no ordinary all-prime Hilbert vector

The observer-free wall amplitude used by the coherent causal weld is not a new summability
class.  At valuation depth zero it is exactly the critical rooted-Bianchi amplitude.  The latter
already has divergent squared prime norm.  Consequently exact recovery of the full sharp source
cannot land in an ordinary all-prime `ell^2` carrier, even through an unbounded graph; only finite
cutoffs followed by a genuinely renormalized or semifinite passage can survive.

No RH premise, Xi zero, numerical computation, or prime-number estimate is used.
-/

namespace RHTower

noncomputable section

/-- **Source identification.**  The depth-zero observer-free sharp-wall coordinate is exactly
the critical rooted-Bianchi coordinate, not merely asymptotic to it. -/
theorem suzukiCriticalEntryWallBareAmplitude_zero_eq_rootedBianchiAmplitude
    (p : Nat.Primes) :
    suzukiCriticalEntryWallBareAmplitude p 0 =
      suzukiCriticalRootedBianchiPrimeAmplitude p := by
  have hwall := sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt p 0
  have hroot := suzukiCriticalRootedBianchiPrimeAmplitude_sq p
  have hmass :
      suzukiCriticalRootedBianchiPrimeMass p =
        ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, 0)) /
          Real.sqrt (xiGammaEulerValuationNat (p, 0) : ℝ) := by
    simp [suzukiCriticalRootedBianchiPrimeMass, xiGammaEulerValuationNat]
  have hwallNonneg : 0 ≤ suzukiCriticalEntryWallBareAmplitude p 0 :=
    Real.sqrt_nonneg _
  have hrootNonneg : 0 ≤ suzukiCriticalRootedBianchiPrimeAmplitude p :=
    Real.sqrt_nonneg _
  have hsquares :
      suzukiCriticalEntryWallBareAmplitude p 0 ^ 2 =
        suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2 :=
    hwall.trans (hroot.trans hmass).symm
  nlinarith

/-- **Ordinary Hilbert-domain no-go.**  Exact depth-zero sharp-wall coordinates have divergent
squared norm over the primes. -/
theorem not_summable_sq_suzukiCriticalEntryWallBareAmplitude_zero :
    ¬ Summable (fun p : Nat.Primes =>
      suzukiCriticalEntryWallBareAmplitude p 0 ^ 2) := by
  intro hsum
  apply not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude
  exact hsum.congr fun p => by
    rw [suzukiCriticalEntryWallBareAmplitude_zero_eq_rootedBianchiAmplitude]

/-- No nonzero prime-independent scalar renormalization puts the exact sharp source in
`ell^2`.  A surviving completion must cancel or renormalize the prime coordinates jointly before
the cofinal limit. -/
theorem summable_const_mul_sq_suzukiCriticalEntryWallBareAmplitude_zero_iff
    (c : ℝ) :
    Summable (fun p : Nat.Primes =>
      (c * suzukiCriticalEntryWallBareAmplitude p 0) ^ 2) ↔ c = 0 := by
  simpa only [suzukiCriticalEntryWallBareAmplitude_zero_eq_rootedBianchiAmplitude] using
    summable_const_mul_sq_suzukiCriticalRootedBianchiPrimeAmplitude_iff c

/-- Abstract exact-recovery form: any real prime-coordinate family equal to the sharp source is
excluded from ordinary square summability. -/
theorem not_summable_sq_of_eq_suzukiCriticalEntryWallBareAmplitude_zero
    (source : Nat.Primes → ℝ)
    (hsource : ∀ p, source p = suzukiCriticalEntryWallBareAmplitude p 0) :
    ¬ Summable (fun p : Nat.Primes => source p ^ 2) := by
  intro hsum
  apply not_summable_sq_suzukiCriticalEntryWallBareAmplitude_zero
  exact hsum.congr fun p => by rw [hsource p]

end

end RHTower
