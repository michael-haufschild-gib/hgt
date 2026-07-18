import GaloisForLFunctions.HTGeometry.CofiniteTailGramPolarization
import GaloisForLFunctions.RHTower.XiTransverseShiftAllValuationLayerRank

/-!
# A Hilbert metric for the transverse Xi prime-source aperture

The transverse differential-rank theorem has a concrete Hilbert realization. For every finite
family of distinct positive integral shifts, every finite logarithmic jet depth, and every finite
set of forbidden prime rays, one can evaluate the complete shift-jet rectangle on a square packet
of remaining primes so that its Hermitian Gram matrix is strictly positive definite.

Thus the aperture parameter is not only a differential-matroid coordinate: it carries a
deletion-robust positive Hilbert metric whose rank is exactly the number of shift-jet channels.
This is a source-side metric. It does not assert convergence of the separate constrained-prolate
CCM aperture Gram and does not constrain Xi zeros.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

/-- Prime coefficient of one transverse shift/logarithmic-jet channel. -/
def xiTransversePrimeJetApertureCoefficient
    {A : Type*} (shift : A → ℕ) (m : ℕ)
    (ak : A × Fin (m + 1)) (p : Nat.Primes) : ℂ :=
  primeProfileJetSource
    (fun a => xiTransverseShiftArithmetic (shift a)) m ak p

/-- Hermitian Hilbert Gram of a square transverse aperture packet outside a forbidden prime set. -/
def xiTransversePrimeJetApertureGram
    {A : Type*} [Fintype A] (shift : A → ℕ) (m : ℕ)
    (forbidden : Set Nat.Primes)
    (points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden}) :
    Matrix (A × Fin (m + 1)) (A × Fin (m + 1)) ℂ :=
  cofiniteEvaluationGram
    (xiTransversePrimeJetApertureCoefficient shift m) forbidden points

/-- **True transverse source-aperture Hilbert metric.** After deleting any finite prime packet,
distinct positive integral shifts and all jets through any prescribed order possess a square
strictly positive Hilbert Gram on the surviving prime source. -/
theorem exists_xiTransversePrimeJetApertureGram_posDef
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ)
    (forbidden : Set Nat.Primes) (hfinite : forbidden.Finite) :
    ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
      (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  have htail : TailCoefficientIndependent
      (xiTransversePrimeJetApertureCoefficient shift m) := by
    simpa only [xiTransversePrimeJetApertureCoefficient] using
      xiTransverseShift_primeJets_tailIndependent shift hpos hinj m
  obtain ⟨points, hgram⟩ :=
    htail.exists_cofinite_posDef_evaluationGram
      (xiTransversePrimeJetApertureCoefficient shift m) forbidden hfinite
  exact ⟨points, hgram⟩

/-- Every such aperture packet has a strictly positive Gram determinant, so its Hilbert rank is
the full shift-times-jet cardinality. -/
theorem exists_xiTransversePrimeJetApertureGram_det_pos
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift : A → ℕ) (hpos : ∀ a, 0 < shift a)
    (hinj : Function.Injective shift) (m : ℕ)
    (forbidden : Set Nat.Primes) (hfinite : forbidden.Finite) :
    ∃ points : A × Fin (m + 1) → {p : Nat.Primes // p ∉ forbidden},
      0 < (xiTransversePrimeJetApertureGram shift m forbidden points).det := by
  obtain ⟨points, hgram⟩ :=
    exists_xiTransversePrimeJetApertureGram_posDef
      shift hpos hinj m forbidden hfinite
  exact ⟨points, hgram.det_pos⟩

end

end RHTower
