import GaloisForLFunctions.RHTower.XiShiftRootedStarCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianRadicalConnector

/-!
# Gaussian and canonical valuation realization of the rooted-star Xi phase

The collision-free/nonloop phase of a raw even-shift Xi defect packet already controls corrected
defect and rooted-star pair reconstruction after every injective zero-preserving reparametrization.
This module identifies that same phase with the existing one-prime canonical valuation recovery,
finite valuation Gram, completed valuation--Szegő Gram, cofinite prime-jet Gram, and nonlinear
Gaussian valuation metric.

All equivalences are unconditional phase classifications assembled from existing exact theorems.
No sampling nodes, dual coefficients, positivity certificate, or independence assumption enters
an interface.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Raw Xi reconstruction is equivalent to canonical one-prime valuation recovery after every
injective zero-preserving corrected-shift reparametrization. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p := by
  calc
    _ ↔ XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
        (embed ∘ grade) :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero
    _ ↔ _ :=
      xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        (embed ∘ grade) p

/-- The same reparametrization-invariant phase is strict positivity of the finite one-prime
valuation Gram. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_valuationGramReparam_posDef
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      (xiTransversePrimeValuationGramMatrix (embed ∘ grade) p).PosDef := by
  calc
    _ ↔ XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
        grade embed hinj hzero p
    _ ↔ _ :=
      xiTransversePrimeValuationCanonicalReconstruction_iff_valuationGram_posDef
        (embed ∘ grade) p

/-- Completed valuation--Szegő positivity has the identical universal reparametrized phase. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_completedSzegoGramReparam_posDef
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      (xiTransversePrimeValuationSzegoGramMatrix (embed ∘ grade) p).PosDef := by
  calc
    _ ↔ XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
        grade embed hinj hzero p
    _ ↔ _ :=
      xiTransversePrimeValuationCanonicalReconstruction_iff_completedSzegoGram_posDef
        (embed ∘ grade) p

/-- Raw analytic reconstruction is equivalent to positive square realization of every
reparametrized prime-jet packet after every finite prime deletion. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureGramReparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : Fin d × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (embed ∘ grade) m forbidden points).PosDef := by
  calc
    _ ↔ XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
        grade embed hinj hzero p
    _ ↔ _ :=
      xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureGram
        (embed ∘ grade) p m

/-- **Raw-Xi/exact prime-aperture connector.**  After any injective zero-preserving shift
reparametrization, raw defect reconstruction is equivalent to exact dual recovery of every
prime-jet coefficient after every finite prime deletion.  The auxiliary prime used by canonical
valuation recovery is discharged internally. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureHilbertReconstructionReparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (m : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction
        (embed ∘ grade) m := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔ XiTransversePrimeValuationCanonicalReconstruction
        (embed ∘ grade) p :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
        grade embed hinj hzero p
    _ ↔ _ :=
      xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
        (embed ∘ grade) p m

/-- **Raw-Xi/Gaussian Hilbert connector.** Raw cofinite reconstruction is exactly nonlinear
Gaussian separation of the first valuation coordinate together with exclusion of the zero grade.
The Gaussian metric discharges every collision hypothesis. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_firstValuationGaussian_posDef_and_ne_zero
    {d : ℕ} (grade : Fin d → ℕ) (p : Nat.Primes) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix grade p).PosDef ∧
        ∀ i, grade i ≠ 0 := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- Corrected rooted-star pair reconstruction after arbitrary injective zero-preserving
reparametrization is equivalent to the raw Gaussian/nonloop phase. -/
theorem
    xiTransverseShiftPairDifferenceRootedStarCofiniteHilbertReconstruction_iff_rawGaussian
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel (embed ∘ grade))
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix grade p).PosDef ∧
        ∀ i, grade i ≠ 0 := by
  calc
    _ ↔ XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
        (embed ∘ grade) :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        (embed ∘ grade)
    _ ↔ XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).symm
    _ ↔ _ :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_firstValuationGaussian_posDef_and_ne_zero
        grade p

/-- **Universal rooted-star Gaussian/canonical Hilbert phase.** One raw analytic reconstruction
interface simultaneously supplies corrected rooted-star reconstruction, canonical one-prime dual
recovery, both finite Hilbert Grams, nonlinear Gaussian separation with the exact zero radical,
and cofinite prime-jet positivity after every finite deletion. -/
theorem xiRootedStarGaussianCanonicalCofiniteHilbertPhase_reparam_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (p : Nat.Primes) (m : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          (xiShiftRootedStarLabel (embed ∘ grade))
          xiShiftRootedStarTail xiShiftRootedStarHead ∧
        XiTransversePrimeValuationCanonicalReconstruction (embed ∘ grade) p ∧
        (xiTransversePrimeValuationGramMatrix (embed ∘ grade) p).PosDef ∧
        (xiTransversePrimeValuationSzegoGramMatrix (embed ∘ grade) p).PosDef ∧
        ((xiTransversePrimeFirstValuationGaussianGramMatrix grade p).PosDef ∧
          ∀ i, grade i ≠ 0) ∧
        (∀ forbidden : Set Nat.Primes, forbidden.Finite →
          ∃ points : Fin d × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
            (xiTransversePrimeJetApertureGram
              (embed ∘ grade) m forbidden points).PosDef) := by
  constructor
  · intro hraw
    have hcorrected :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).1 hraw
    exact ⟨
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        (embed ∘ grade)).2 hcorrected,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReparam
        grade embed hinj hzero p).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_valuationGramReparam_posDef
        grade embed hinj hzero p).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_completedSzegoGramReparam_posDef
        grade embed hinj hzero p).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_firstValuationGaussian_posDef_and_ne_zero
        grade p).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_cofiniteApertureGramReparam
        grade embed hinj hzero p m).1 hraw⟩
  · rintro ⟨hstar, _hcanonical, _hvaluation, _hszego, _hgaussian, _hcofinite⟩
    have hcorrected :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        (embed ∘ grade)).1 hstar
    exact
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).2 hcorrected

end

end RHTower
