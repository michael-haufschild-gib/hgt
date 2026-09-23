import GaloisForLFunctions.HTGeometry.ContinuumPrimeCoherenceSaturation
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Order-pointed continuum prime coherence saturation

The all-positive prime orientation is the unique positive-definite vertical
trace, yet every coherence neighborhood around it contains the continuum-rank
differentially independent sparse family.  This is the exact order-pointed,
information-nonisolated conclusion of the coherence-local saturation card.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive definiteness on a convergence line identifies the all-positive
orientation as an actual function, not merely through a named predicate. -/
theorem signedPrimeVerticalTrace_positiveDefinite_iff_eq_allPositive
    (epsilon : Nat.Primes → Bool) {x : ℝ} (hx : 1 < x) :
    PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon x) ↔
      epsilon = fun _ => false := by
  rw [signedPrimeVerticalTrace_positiveDefinite_iff_allPositive epsilon hx]
  constructor
  · intro h
    funext p
    exact h p
  · intro h p
    rw [h]

/-- **Order-pointed, information-nonisolated zeta tail.**  At every positive
coherence exponent and radius, a continuum-rank free differential building
lies around the all-positive orientation, while positive definiteness on every
convergence line still singles out that orientation uniquely in the full
Boolean prime cube. -/
theorem exists_orderPointedContinuumPrimeCoherenceSaturation
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2) ∧
      Algebra.trdeg finitePrimeRationalCoefficientField
        (GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range fun z : ℕ → Bool =>
            signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation (fun _ => false) e z) 0)) =
        Cardinal.continuum ∧
      (∀ z, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation (fun _ => false) e z)
        (fun _ => false) < eta ^ (2 : ℕ)) ∧
      (∀ z w, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation (fun _ => false) e z)
        (continuumSparsePrimeOrientation (fun _ => false) e w) < eta ^ (2 : ℕ)) ∧
      ∀ epsilon : Nat.Primes → Bool,
        PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon x) ↔
          epsilon = fun _ => false := by
  obtain ⟨e, hdiff, htrdeg, hbase, hpair⟩ :=
    exists_continuumPrimeCoherenceLocalDifferentialSaturation
      sigma eta hsigma heta (fun _ => false)
  exact ⟨e, hdiff, htrdeg, hbase, hpair,
    fun epsilon => signedPrimeVerticalTrace_positiveDefinite_iff_eq_allPositive epsilon hx⟩

end

end GaloisForLFunctions.HTGeometry
