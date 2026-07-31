import GaloisForLFunctions.RHTower.GaussPairedChannelCriticalAsymptotic

/-!
# The Gauss-paired logarithmic residue, produced

The critical-asymptotic law produces a logarithmic Schatten residue at an arbitrary value.  The
Gauss-paired capstones consume it at one specific value, the channel residue, so the specialization
is recorded here as its own producer: an approximation-number asymptotic with the Gauss channel
residue as its constant yields exactly the certificate those capstones ask for.
-/

open Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Gauss-paired channel residue is realized as a logarithmic Schatten residue by the
corresponding critical approximation-number asymptotic. -/
theorem hasSchattenLogResidue_gaussPairedChannelResidue
    {J : Type*} [Fintype J] {m : ℕ} (prime : J → Nat.Primes) {T : H →L[ℂ] H}
    (hasymp : Tendsto
      (fun n : ℕ => approxNumber T n ^ ((2 * m : ℕ) : ℝ) * ((n : ℝ) + 1)) atTop
      (nhds (gaussPairedChannelResidue m prime))) :
    HasSchattenLogResidue ((2 * m : ℕ) : ℝ) T (gaussPairedChannelResidue m prime) :=
  hasSchattenLogResidue_of_tendsto_mul_succ hasymp

/-- The same at a cutoff depth, the form the cofinal exclusion law consumes. -/
theorem hasSchattenLogResidue_gaussPairedCriticalDepth
    (N : ℕ) (prime : Fin (Nat.primeCounting N) → Nat.Primes) {T : H →L[ℂ] H}
    (hasymp : Tendsto
      (fun n : ℕ =>
        approxNumber T n ^ ((gaussPairedCriticalDepth N : ℕ) : ℝ) * ((n : ℝ) + 1))
      atTop (nhds (gaussPairedChannelResidue (Nat.primeCounting N) prime))) :
    HasSchattenLogResidue ((gaussPairedCriticalDepth N : ℕ) : ℝ) T
      (gaussPairedChannelResidue (Nat.primeCounting N) prime) :=
  hasSchattenLogResidue_of_tendsto_mul_succ hasymp

end

end RHTower
