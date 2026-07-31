import GaloisForLFunctions.RHTower.SchattenCriticalAsymptotic
import GaloisForLFunctions.RHTower.FinitePrimeApertureCensusUniversalityLaw

/-!
# The Gauss-paired endpoint from a single asymptotic

The Gauss-paired Schatten capstones take two independent analytic inputs: a weak endpoint bound and
an honest logarithmic residue.  Both are consequences of one pointwise asymptotic of the
approximation numbers at the critical exponent, so each capstone is restated here with that single
hypothesis in place of the pair.
-/

open Complex Metric Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact Gauss-paired depth from the critical approximation-number asymptotic. -/
theorem gaussPairedChannel_exact_schattenDepth_of_asymptotic
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) {T : H →L[ℂ] H}
    (hasymp : Tendsto
      (fun n : ℕ => approxNumber T n ^ ((2 * m : ℕ) : ℝ) * ((n : ℝ) + 1)) atTop
      (nhds (gaussPairedChannelResidue m prime))) :
    (∀ q : ℝ, 0 < q → q ≤ (2 * m : ℕ) → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, (2 * m : ℕ) < q → MemSchattenClass q T) :=
  gaussPairedChannel_exact_schattenDepth hm prime
    (memWeakSchattenClass_of_tendsto_mul_succ hasymp)
    (hasSchattenLogResidue_of_tendsto_mul_succ hasymp)

/-- The `Fin m`-channel form, from the same single asymptotic. -/
theorem gaussPairedFinChannel_exact_schattenDepth_of_asymptotic
    {m : ℕ} (hm : 1 ≤ m) (prime : Fin m → Nat.Primes) {T : H →L[ℂ] H}
    (hasymp : Tendsto
      (fun n : ℕ => approxNumber T n ^ ((2 * m : ℕ) : ℝ) * ((n : ℝ) + 1)) atTop
      (nhds (gaussPairedChannelResidue m prime))) :
    (∀ q : ℝ, 0 < q → q ≤ (2 * m : ℕ) → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, (2 * m : ℕ) < q → MemSchattenClass q T) :=
  gaussPairedFinChannel_exact_schattenDepth hm prime
    (memWeakSchattenClass_of_tendsto_mul_succ hasymp)
    (hasSchattenLogResidue_of_tendsto_mul_succ hasymp)

/-- The cofinal exclusion law needs only one asymptotic per cutoff. -/
theorem exists_cutoff_not_memSchattenClass_of_asymptotic
    (T : ℕ → H →L[ℂ] H)
    (prime : ∀ N, Fin (Nat.primeCounting N) → Nat.Primes)
    (hasymp : ∀ N, Nat.primeCounting N ≠ 0 →
      Tendsto (fun n : ℕ =>
          approxNumber (T N) n ^ ((gaussPairedCriticalDepth N : ℕ) : ℝ) * ((n : ℝ) + 1))
        atTop (nhds (gaussPairedChannelResidue (Nat.primeCounting N) (prime N))))
    (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ¬ MemSchattenClass q (T N) :=
  exists_cutoff_not_memSchattenClass T prime
    (fun N hN => memWeakSchattenClass_of_tendsto_mul_succ (hasymp N hN))
    (fun N hN => hasSchattenLogResidue_of_tendsto_mul_succ (hasymp N hN)) q hq

/-- The finite-prime aperture census law, with its two endpoint certificates replaced by the
single critical asymptotic of the approximation numbers. -/
theorem finitePrimeAperture_cuspDivisorSchattenRankUniversality_of_asymptotic
    (N : ℕ) (hm : 1 ≤ Nat.primeCounting N)
    (prime : Fin (Nat.primeCounting N) → Nat.Primes)
    (T : H →L[ℂ] H)
    (hasymp : Tendsto
      (fun n : ℕ =>
        approxNumber T n ^ ((gaussPairedCriticalDepth N : ℕ) : ℝ) * ((n : ℝ) + 1))
      atTop (nhds (gaussPairedChannelResidue (Nat.primeCounting N) prime)))
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (hfc : f c ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → f (Real.log p) = 0)
    (hN : 2 ≤ N)
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (kappa : ℕ) (V D : Submodule ℚ E)
    (hV : Module.finrank ℚ ↥V = Nat.primeCounting N)
    (hstate : Module.finrank ℚ (↥V ⧸ Submodule.comap V.subtype D) ≤ 2 * kappa) :
    analyticOrderAt (finitePrimeCuspDenominator N) 0 = Nat.primeCounting N ∧
      meromorphicOrderAt (finitePrimeCuspDenominator N)⁻¹ 0 =
        -((Nat.primeCounting N : ℤ) : WithTop ℤ) ∧
      (Nat.primeCounting N : ℤ) ≤
        ∑ᶠ u, (MeromorphicOn.divisor f
          (closedBall c (1 + ‖c‖ + Real.log N))) u ∧
      gaussPairedCriticalDepth N = 2 * Nat.primeCounting N ∧
      ((∀ q : ℝ, 0 < q → q ≤ gaussPairedCriticalDepth N →
          ¬ MemSchattenClass q T) ∧
        (∀ q : ℝ, gaussPairedCriticalDepth N < q → MemSchattenClass q T)) ∧
      Nat.primeCounting N ≤ Module.finrank ℚ ↥(V ⊓ D) + 2 * kappa :=
  finitePrimeAperture_cuspDivisorSchattenRankUniversality N hm prime T
    (memWeakSchattenClass_of_tendsto_mul_succ hasymp)
    (hasSchattenLogResidue_of_tendsto_mul_succ hasymp)
    hf c hfc hprime hN kappa V D hV hstate

end

end RHTower
