import GaloisForLFunctions.RHTower.GaussPairedChannelSchattenCapstone
import GaloisForLFunctions.RHTower.PrimeLogExponentialTypeUniqueness
import GaloisForLFunctions.RHTower.ThetaCuspMellinPole

/-!
# Finite-prime aperture census universality

The same finite prime census controls four terminal geometries: theta-cusp order, divisor mass of
prime-log zero sets, exact Gauss-paired Schatten depth, and coefficient/state rank capacity.
-/

open Complex Metric

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- **Finite-prime aperture census universality law.** At one finite aperture, `π(N)` is exactly
the theta-cusp vanishing order and pole magnitude, a lower bound for every entire prime-log zero
divisor census, half the exact Gauss-paired Schatten transition, and the common prime-state rank
entering the coefficient/complement capacity bound. -/
theorem finitePrimeAperture_cuspDivisorSchattenRankUniversality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (hm : 1 ≤ Nat.primeCounting N)
    (prime : Fin (Nat.primeCounting N) → Nat.Primes)
    (T : H →L[ℂ] H)
    (hweak : MemWeakSchattenClass ((gaussPairedCriticalDepth N : ℕ) : ℝ) T)
    (hres : HasSchattenLogResidue ((gaussPairedCriticalDepth N : ℕ) : ℝ) T
      (gaussPairedChannelResidue (Nat.primeCounting N) prime))
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
      Nat.primeCounting N ≤ Module.finrank ℚ ↥(V ⊓ D) + 2 * kappa := by
  have hspectral := gaussPairedFinChannel_exact_schattenDepth hm prime hweak hres
  refine ⟨finitePrimeCuspDenominator_analyticOrderAt_zero N,
    finitePrimeCuspDenominator_inv_meromorphicOrderAt_zero N,
    primeCounting_le_sum_divisor_of_primeLog_zeros hf hfc hprime hN,
    rfl, ?_,
    primeCounting_le_coefficientRank_add_twice_stateCapacity N kappa V D hV hstate⟩
  simpa [gaussPairedCriticalDepth] using hspectral

end

end RHTower
