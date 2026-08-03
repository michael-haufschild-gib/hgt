import GaloisForLFunctions.RHTower.DeningerCompletedXiHellingerGammaResolvedProvenanceCoface
import GaloisForLFunctions.RHTower.DeningerGreenResolvedDefectLaw

/-!
# Actual Green defect in the resolved Hellinger--Gamma provenance quotient

The abstract resolved-provenance coface retains an arbitrary completed Xi
incidence vector.  This file identifies its retained vector with the actual
two-channel Deninger Green covariance defect.

Divisor-copy indices and analytic jet indices use independently named but
equal multiplicities, so we first construct their canonical equivalence.
The resulting coefficient-faithful map embeds the semisimple divisor carrier
into completed cross-prime incidence.  Under this embedding the actual Green
resolved defect remains exactly antidiagonal and vanishes exactly when the
original algebraic defect vanishes.

Consequently, its class in the resolved Hellinger--Gamma coface quotient is
zero exactly when the actual Green defect is zero.  Universal vanishing of
these quotient classes is equivalent to RH, while a single divisor-copy class
is nonzero exactly off the critical line.  These are unconditional
identifications; they do not prove the source-continuous singular descent
needed to force the quotient classes to vanish.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open CompletedXiHellingerGammaPureHodgeCoface

/-- The divisor-copy and source-jet coordinate sets carry the same multiplicities,
but through independently named definitions. -/
def xiZeroCopyEquivDeningerArithmeticJetCoordinate :
    XiZeroCopy ≃ DeningerArithmeticJetCoordinate where
  toFun r :=
    ⟨r.1, ⟨r.2.1, by
      simpa [xiSupportMultiplicity] using r.2.2⟩⟩
  invFun j :=
    ⟨j.1, ⟨j.2.1, by
      simpa [xiSupportMultiplicity] using j.2.2⟩⟩
  left_inv r := by
    rcases r with ⟨rho, k⟩
    congr
  right_inv j := by
    rcases j with ⟨rho, k⟩
    congr

/-- Canonical reindexing from semisimple divisor copies to analytic source-jet coordinates. -/
def deningerArithmeticGradedH1EquivJetTest :
    DeningerArithmeticGradedH1 ≃ₗ[ℂ] DeningerArithmeticJetTest :=
  deningerArithmeticGradedH1EquivSourceJets.trans
    (Finsupp.domLCongr xiZeroCopyEquivDeningerArithmeticJetCoordinate)

def deningerCrossPrimeIncidenceCompletionOfGradedJet
    (p q : Nat.Primes) (hpq : p ≠ q)
    : DeningerArithmeticGradedH1 →ₗ[ℂ]
        DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq).toLinearMap.comp
    (deningerArithmeticJetTestToHilbert.comp
      deningerArithmeticGradedH1EquivJetTest.toLinearMap)

theorem deningerCrossPrimeIncidenceCompletionOfGradedJet_injective
    (p q : Nat.Primes) (hpq : p ≠ q) :
    Function.Injective (deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq) := by
  intro a b hab
  have hhilbert :=
    (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq).injective hab
  change deningerArithmeticJetTestToHilbert
      (deningerArithmeticGradedH1EquivJetTest a) =
    deningerArithmeticJetTestToHilbert
      (deningerArithmeticGradedH1EquivJetTest b) at hhilbert
  apply deningerArithmeticGradedH1EquivJetTest.injective
  ext idx
  simpa only [deningerArithmeticJetTestToHilbert_apply] using
      congrArg (fun z : DeningerArithmeticJetHilbert => z idx) hhilbert

@[simp]
theorem deningerCrossPrimeIncidenceCompletionOfGradedJet_zero
    (p q : Nat.Primes) (hpq : p ≠ q) :
    deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq 0 = 0 := by
  exact map_zero _

@[simp]
theorem deningerCrossPrimeIncidenceCompletionOfGradedJet_neg
    (p q : Nat.Primes) (hpq : p ≠ q)
    (a : DeningerArithmeticGradedH1) :
    deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq (-a) =
      -deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq a := by
  exact map_neg _ a

def deningerCompletedCrossPrimeGreenResolvedDefect
    (p q : Nat.Primes) (hpq : p ≠ q)
    (a : DeningerArithmeticGradedH1) :
    HellingerGammaPureHodgeXiCofaceCompletion p q hpq :=
  (deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq
      (deningerArithmeticGreenResolvedDefect a).1,
    deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq
      (deningerArithmeticGreenResolvedDefect a).2)

def deningerCompletedCrossPrimeGreenResolvedProvenance
    (p q : Nat.Primes) (hpq : p ≠ q)
    (a : DeningerArithmeticGradedH1) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq
    (deningerArithmeticGradedHodgeCovarianceDefect
      (deningerArithmeticGradedRieszConjugation a))

theorem deningerCompletedCrossPrimeGreenResolvedDefect_eq_antidiagonal
    (p q : Nat.Primes) (hpq : p ≠ q)
    (a : DeningerArithmeticGradedH1) :
    deningerCompletedCrossPrimeGreenResolvedDefect p q hpq a =
      resolvedDefectAntidiagonal (R := ℂ)
        (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq a) := by
  rw [deningerCompletedCrossPrimeGreenResolvedDefect,
    deningerCompletedCrossPrimeGreenResolvedProvenance,
    deningerArithmeticGreenResolvedDefect_eq_antidiagonal]
  apply Prod.ext
  · rfl
  · exact deningerCrossPrimeIncidenceCompletionOfGradedJet_neg p q hpq _

theorem deningerCompletedCrossPrimeGreenResolvedDefect_eq_zero_iff
    (p q : Nat.Primes) (hpq : p ≠ q)
    (a : DeningerArithmeticGradedH1) :
    deningerCompletedCrossPrimeGreenResolvedDefect p q hpq a = 0 ↔
      deningerArithmeticGreenResolvedDefect a = 0 := by
  constructor
  · intro hzero
    apply Prod.ext
    · apply deningerCrossPrimeIncidenceCompletionOfGradedJet_injective p q hpq
      simpa [deningerCompletedCrossPrimeGreenResolvedDefect] using congrArg Prod.fst hzero
    · apply deningerCrossPrimeIncidenceCompletionOfGradedJet_injective p q hpq
      simpa [deningerCompletedCrossPrimeGreenResolvedDefect] using congrArg Prod.snd hzero
  · intro hzero
    have hfst := congrArg Prod.fst hzero
    have hsnd := congrArg Prod.snd hzero
    apply Prod.ext
    · simpa [deningerCompletedCrossPrimeGreenResolvedDefect] using
        congrArg (deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq) hfst
    · simpa [deningerCompletedCrossPrimeGreenResolvedDefect] using
        congrArg (deningerCrossPrimeIncidenceCompletionOfGradedJet p q hpq) hsnd

theorem deningerCompletedCrossPrimeGreenResolvedDefect_single_eq_zero_iff
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    deningerCompletedCrossPrimeGreenResolvedDefect p q hpq
        (Finsupp.single r 1) = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  rw [deningerCompletedCrossPrimeGreenResolvedDefect_eq_zero_iff,
    deningerArithmeticGreenResolvedDefect_single_eq_zero_iff]

def deningerGreenResolvedHellingerGammaProvenanceVertex
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (u : DeningerArithmeticGradedH1) :
    HellingerGammaResolvedProvenanceCofaceCompletion p q hpq :=
  hellingerGammaResolvedProvenanceVertex hpq a n
    (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u)

theorem deningerGreenResolvedHellingerGammaProvenanceVertex_defect
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (u : DeningerArithmeticGradedH1) :
    resolvedDefectAntidiagonal (R := ℂ)
        (hellingerGammaResolvedProvenanceProjection
          (deningerGreenResolvedHellingerGammaProvenanceVertex
            p q hpq a n u)) =
      deningerCompletedCrossPrimeGreenResolvedDefect p q hpq u := by
  rw [deningerGreenResolvedHellingerGammaProvenanceVertex]
  change resolvedDefectAntidiagonal (R := ℂ)
      (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u) = _
  exact (deningerCompletedCrossPrimeGreenResolvedDefect_eq_antidiagonal
    p q hpq u).symm

/-- The descended provenance class vanishes exactly when the actual resolved
Green defect vanishes.  No critical-line or continuity hypothesis enters. -/
theorem deningerGreenResolvedHellingerGammaProvenanceQuotient_eq_zero_iff
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (u : DeningerArithmeticGradedH1) :
    hellingerGammaResolvedProvenanceQuotientSource hpq a
        (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u) = 0 ↔
      deningerArithmeticGreenResolvedDefect u = 0 := by
  rw [← deningerCompletedCrossPrimeGreenResolvedDefect_eq_zero_iff]
  constructor
  · intro hquot
    have hprov :
        deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u = 0 :=
      hellingerGammaResolvedProvenanceQuotientSource_injective hpq a
        (by simpa using hquot)
    rw [deningerCompletedCrossPrimeGreenResolvedDefect_eq_antidiagonal, hprov]
    simp [resolvedDefectAntidiagonal]
  · intro hdefect
    have hprov :
        deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u = 0 := by
      have hant := deningerCompletedCrossPrimeGreenResolvedDefect_eq_antidiagonal
        p q hpq u
      have := congrArg Prod.fst (hant.symm.trans hdefect)
      simpa [resolvedDefectAntidiagonal] using this
    rw [hprov]
    exact map_zero _

/-- Universal vanishing of the actual Green-provenance quotient class is
equivalent to the Riemann hypothesis. -/
theorem deningerGreenResolvedHellingerGammaProvenanceQuotient_vanishes_iff_riemannHypothesis
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    (∀ u : DeningerArithmeticGradedH1,
      hellingerGammaResolvedProvenanceQuotientSource hpq a
          (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq u) = 0) ↔
        RiemannHypothesis := by
  rw [← deningerArithmeticGreenResolvedDefect_vanishes_iff_riemannHypothesis]
  constructor
  · intro h u
    exact (deningerGreenResolvedHellingerGammaProvenanceQuotient_eq_zero_iff
      p q hpq a u).mp (h u)
  · intro h u
    exact (deningerGreenResolvedHellingerGammaProvenanceQuotient_eq_zero_iff
      p q hpq a u).mpr (h u)

theorem deningerGreenResolvedHellingerGammaProvenanceQuotient_single_ne_zero_iff
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) (r : XiZeroCopy) :
    hellingerGammaResolvedProvenanceQuotientSource hpq a
        (deningerCompletedCrossPrimeGreenResolvedProvenance p q hpq
          (Finsupp.single r 1)) ≠ 0 ↔
      (r.1 : ℂ).re ≠ 1 / 2 := by
  rw [ne_eq, not_congr
    (deningerGreenResolvedHellingerGammaProvenanceQuotient_eq_zero_iff
      p q hpq a (Finsupp.single r 1)),
    deningerArithmeticGreenResolvedDefect_single_eq_zero_iff]

end

end RHTower
