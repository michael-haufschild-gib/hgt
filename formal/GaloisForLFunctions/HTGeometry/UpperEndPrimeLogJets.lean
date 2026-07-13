import GaloisForLFunctions.HTGeometry.TwoEndedReflection
import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetDerivatives
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Actual prime-log jets in the upper-end differential field

The abstract differential-field jet of a translated prime-log element is the meromorphic image of
the genuine iterated complex derivative of the translated Herglotz function.  This is the first
evaluation bridge from the upper-end field back to the functional jet packets used by the Baire
freeness theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Function
open scoped Differential

noncomputable section

/-- Every iterated derivative of an analytic function remains analytic on the same domain. -/
theorem analyticOnNhd_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- The genuine `n`th derivative of a prime-log source as an upper-end analytic germ. -/
def primeLogHerglotzUpperEndAnalyticJet
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (n : ℕ) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (iteratedDeriv n (primeLogHerglotz u)),
    iteratedDeriv n (primeLogHerglotz u), 0,
    analyticOnNhd_iteratedDeriv
      (analyticOnNhd_primeLogHerglotz_upperHalfPlane u C hu) n, rfl⟩

@[simp]
theorem primeLogHerglotzUpperEndAnalyticJet_zero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    primeLogHerglotzUpperEndAnalyticJet u C hu 0 =
      primeLogHerglotzUpperEndAnalytic u C hu := by
  rfl

/-- Analytic-germ differentiation advances the genuine prime-log jet. -/
theorem upperEndAnalyticDeriv_primeLogHerglotzJet
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (n : ℕ) :
    upperEndAnalyticDeriv (primeLogHerglotzUpperEndAnalyticJet u C hu n) =
      primeLogHerglotzUpperEndAnalyticJet u C hu (n + 1) := by
  apply Subtype.ext
  change (deriv (iteratedDeriv n (primeLogHerglotz u)) : Germ upperEndFilter ℂ) =
    (iteratedDeriv (n + 1) (primeLogHerglotz u) : Germ upperEndFilter ℂ)
  rw [iteratedDeriv_succ]

/-- Differential-field jets of the source are exactly its genuine analytic derivative germs. -/
theorem differentialJet_primeLogHerglotzUpperEndMero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (primeLogHerglotzUpperEndMero u C hu) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (primeLogHerglotzUpperEndAnalyticJet u C hu n) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_primeLogHerglotzJet]

/-- Translation commutes with every differential-field jet of the prime-log source. -/
theorem differentialJet_translatedPrimeLogHerglotzUpperEndMero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (h : ℂ) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (translatedPrimeLogHerglotzUpperEndMero u C hu h) =
      upperEndTranslationMeroEquiv h
        (algebraMap upperEndAnalyticSubring upperEndMeroField
          (primeLogHerglotzUpperEndAnalyticJet u C hu n)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        ← upperEndTranslationMeroEquiv_deriv,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_primeLogHerglotzJet]

/-- The translated jet is the field image of the genuinely translated analytic derivative germ. -/
theorem differentialJet_translatedPrimeLogHerglotzUpperEndMero_algebraMap
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (h : ℂ) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (translatedPrimeLogHerglotzUpperEndMero u C hu h) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndTranslationAnalyticEquiv h
          (primeLogHerglotzUpperEndAnalyticJet u C hu n)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  rw [differentialJet_translatedPrimeLogHerglotzUpperEndMero,
    upperEndTranslationMeroEquiv_algebraMap]

end

end GaloisForLFunctions.HTGeometry
