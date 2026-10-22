import GaloisForLFunctions.RHTower.SourceSelectedGammaWardSharedGhostDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittOrientationTransgressionCompleteness

/-!
# Source/Gamma naturality produces the shared inverse-oriented ghost

Every normalized prime orientation and the independent archimedean orientation represent the same
retained top class of the actual all-prime Calderón--Witt source.  Their difference has an explicit
Green primitive.  A coefficient-faithful inverse-Gamma reporter evaluates that genuine boundary as
`p⁻ᵗ - c`, where `c` is its single archimedean component.

Consequently, naturality on only the selected prime-two and prime-three Green boundaries constructs
one positive prime-independent ghost satisfying both inverse-oriented Ward equations.  Conversely,
the unique shared ghost makes both source squares natural.  This is source-selected rather than
global boundary blindness, and neither prime-local countercharacters nor a common determinant
correction occurs.

No source/Gamma naturality premise is asserted.  The final equivalences identify that remaining
producer exactly.
-/

open Complex
open scoped DirectSum

namespace RHTower

noncomputable section

/-- Explicit Green primitive comparing the prime-labelled orientation presentation with the
single archimedean orientation presentation of the same retained top source class. -/
def deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
    (p : Nat.Primes) :
    ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  deningerCalderonWittGlobalOrientedTopGreenLift
    (deningerCalderonWittGlobalPrimeOrientationCochain p -
      deningerCalderonWittGlobalOrientationInclusion 1)

/-- The prime and archimedean presentations differ by a literal source boundary. -/
theorem deningerCalderonWittGlobalOrientedBoundary_primeArchWitness
    (p : Nat.Primes) :
    deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness p) =
      deningerCalderonWittGlobalPrimeOrientationCochain p -
        deningerCalderonWittGlobalOrientationInclusion 1 := by
  have h := deningerCalderonWittGlobalOrientedTopGreenDecomposition
    (deningerCalderonWittGlobalPrimeOrientationCochain p -
      deningerCalderonWittGlobalOrientationInclusion 1)
  have htrace :
      deningerCalderonWittGlobalOrientedTrace
          (deningerCalderonWittGlobalPrimeOrientationCochain p -
            deningerCalderonWittGlobalOrientationInclusion 1) = 0 := by
    rw [map_sub, deningerCalderonWittGlobalOrientedTrace_primeOrientationCochain]
    simp [deningerCalderonWittGlobalOrientedTrace,
      deningerCalderonWittGlobalOrientationInclusion]
  simpa [deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness,
    htrace] using h

/-- Coefficient-faithful inverse-Gamma reporter with one archimedean source component. -/
def deningerCalderonWittInverseGammaGhostReporter
    (t c : ℝ) :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] ℂ :=
  ((DirectSum.toModule ℂ Nat.Primes ℂ
      (fun p =>
        ((primeGammaLocalInverseOrientedGhost t p : ℂ) •
          deningerCalderonWittAlgebraicCenterTrace p))).comp
    (LinearMap.fst ℂ DeningerCalderonWittAlgebraicGlobalDegreeTwo ℂ)) +
      (c : ℂ) •
        (LinearMap.snd ℂ DeningerCalderonWittAlgebraicGlobalDegreeTwo ℂ)

@[simp] theorem deningerCalderonWittInverseGammaGhostReporter_prime
    (t c : ℝ) (p : Nat.Primes) :
    deningerCalderonWittInverseGammaGhostReporter t c
        (deningerCalderonWittGlobalPrimeOrientationCochain p) =
      (primeGammaLocalInverseOrientedGhost t p : ℂ) := by
  simp [deningerCalderonWittInverseGammaGhostReporter,
    deningerCalderonWittGlobalPrimeOrientationCochain,
    deningerCalderonWittGlobalPrimeCenterOrientationSection]

@[simp] theorem deningerCalderonWittInverseGammaGhostReporter_arch
    (t c : ℝ) :
    deningerCalderonWittInverseGammaGhostReporter t c
        (deningerCalderonWittGlobalOrientationInclusion 1) = (c : ℂ) := by
  simp [deningerCalderonWittInverseGammaGhostReporter,
    deningerCalderonWittGlobalOrientationInclusion]

/-- The naturality defect on the genuine prime--archimedean source boundary is exactly the
difference between the fitted local inverse-Gamma ghost and the single archimedean component. -/
theorem deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary
    (t c : ℝ) (p : Nat.Primes) :
    deningerCalderonWittInverseGammaGhostReporter t c
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness p)) =
      (primeGammaLocalInverseOrientedGhost t p : ℂ) - c := by
  rw [deningerCalderonWittGlobalOrientedBoundary_primeArchWitness, map_sub]
  simp

/-- Source-selected Gamma naturality: one archimedean component makes the inverse-Gamma reporter
blind to the two genuine prime--archimedean Green boundaries at primes two and three. -/
def PrimeGammaTwoThreeSourceNaturalInverseGhost (t : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    deningerCalderonWittInverseGammaGhostReporter t c
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo)) = 0 ∧
    deningerCalderonWittInverseGammaGhostReporter t c
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeThree)) = 0

/-- Genuine source/Gamma datum.  Unlike `PrimeGammaTwoThreeSourceNaturalInverseGhost`, this
structure does not contain a proposed shared scalar.  Its reporter is only required to have the
prescribed inverse-Gamma coefficients at the two selected prime presentations, a positive real
archimedean readout, and naturality on the two literal source boundaries. -/
structure PrimeGammaTwoThreeSourceNaturalReporter (t : ℝ) where
  reporter :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] ℂ
  prime_two :
    reporter (deningerCalderonWittGlobalPrimeOrientationCochain
      deningerCalderonWittPrimeTwo) =
        (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo : ℂ)
  prime_three :
    reporter (deningerCalderonWittGlobalPrimeOrientationCochain
      deningerCalderonWittPrimeThree) =
        (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree : ℂ)
  arch_real :
    (reporter (deningerCalderonWittGlobalOrientationInclusion 1)).im = 0
  arch_pos :
    0 < (reporter (deningerCalderonWittGlobalOrientationInclusion 1)).re
  natural_two :
    reporter
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo)) = 0
  natural_three :
    reporter
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeThree)) = 0

/-- The shared ghost is forced, rather than supplied: it is the real archimedean readout of an
arbitrary coefficient-faithful source-natural reporter. -/
theorem primeGammaTwoThreeSharedGhost_of_naturalReporter
    {t : ℝ} (h : PrimeGammaTwoThreeSourceNaturalReporter t) :
    PrimeGammaTwoThreeSharedInverseOrientedGhostWard t := by
  let c : ℝ :=
    (h.reporter (deningerCalderonWittGlobalOrientationInclusion 1)).re
  have harch :
      h.reporter (deningerCalderonWittGlobalOrientationInclusion 1) = (c : ℂ) := by
    apply Complex.ext
    · simp [c]
    · simpa [c] using h.arch_real
  have htwo := h.natural_two
  rw [deningerCalderonWittGlobalOrientedBoundary_primeArchWitness,
    map_sub, h.prime_two, harch] at htwo
  have hthree := h.natural_three
  rw [deningerCalderonWittGlobalOrientedBoundary_primeArchWitness,
    map_sub, h.prime_three, harch] at hthree
  have htwo' :
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo = c := by
    exact_mod_cast sub_eq_zero.mp htwo
  have hthree' :
      primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree = c := by
    exact_mod_cast sub_eq_zero.mp hthree
  refine ⟨c, h.arch_pos, ?_, ?_⟩
  · exact (primeGammaInverseOrientedGhostWardEquation_iff
      h.arch_pos t deningerCalderonWittPrimeTwo).2 htwo'.symm
  · exact (primeGammaInverseOrientedGhostWardEquation_iff
      h.arch_pos t deningerCalderonWittPrimeThree).2 hthree'.symm

/-- Genuine source/Gamma naturality constructs the prime-independent shared ghost. -/
theorem primeGammaTwoThreeSharedGhost_of_sourceNaturality
    {t : ℝ} (h : PrimeGammaTwoThreeSourceNaturalInverseGhost t) :
    PrimeGammaTwoThreeSharedInverseOrientedGhostWard t := by
  rcases h with ⟨c, hc, htwo, hthree⟩
  have htwo' : primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo = c := by
    rw [deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary] at htwo
    exact_mod_cast sub_eq_zero.mp htwo
  have hthree' : primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree = c := by
    rw [deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary] at hthree
    exact_mod_cast sub_eq_zero.mp hthree
  refine ⟨c, hc, ?_, ?_⟩
  · exact (primeGammaInverseOrientedGhostWardEquation_iff
      hc t deningerCalderonWittPrimeTwo).2 htwo'.symm
  · exact (primeGammaInverseOrientedGhostWardEquation_iff
      hc t deningerCalderonWittPrimeThree).2 hthree'.symm

/-- Conversely, a shared ghost supplies the unique common archimedean component on both selected
source boundaries. -/
theorem sourceNaturality_of_primeGammaTwoThreeSharedGhost
    {t : ℝ} (h : PrimeGammaTwoThreeSharedInverseOrientedGhostWard t) :
    PrimeGammaTwoThreeSourceNaturalInverseGhost t := by
  rcases h with ⟨c, hc, htwo, hthree⟩
  have htwo' : c = primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo :=
    primeGammaLocalInverseOrientedGhost_unique hc t deningerCalderonWittPrimeTwo htwo
  have hthree' : c = primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree :=
    primeGammaLocalInverseOrientedGhost_unique hc t deningerCalderonWittPrimeThree hthree
  refine ⟨c, hc, ?_, ?_⟩
  · rw [deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary]
    exact_mod_cast sub_eq_zero.mpr htwo'.symm
  · rw [deningerCalderonWittInverseGammaGhostReporter_primeArchBoundary]
    exact_mod_cast sub_eq_zero.mpr hthree'.symm

/-- A source-natural inverse-Gamma ghost gives a genuine reporter.  This converse proves that the
reporter formulation adds no hidden determinant or contractible correction. -/
theorem primeGammaTwoThreeNaturalReporter_nonempty_of_sourceNaturalInverseGhost
    {t : ℝ} (h : PrimeGammaTwoThreeSourceNaturalInverseGhost t) :
    Nonempty (PrimeGammaTwoThreeSourceNaturalReporter t) := by
  rcases h with ⟨c, hc, htwo, hthree⟩
  exact ⟨
    { reporter := deningerCalderonWittInverseGammaGhostReporter t c
      prime_two := by simp
      prime_three := by simp
      arch_real := by simp
      arch_pos := by simpa using hc
      natural_two := htwo
      natural_three := hthree }⟩

theorem primeGammaTwoThreeSourceNaturalInverseGhost_iff_sharedGhost (t : ℝ) :
    PrimeGammaTwoThreeSourceNaturalInverseGhost t ↔
      PrimeGammaTwoThreeSharedInverseOrientedGhostWard t :=
  ⟨primeGammaTwoThreeSharedGhost_of_sourceNaturality,
    sourceNaturality_of_primeGammaTwoThreeSharedGhost⟩

theorem primeGammaTwoThreeSourceNaturalReporter_nonempty_iff (t : ℝ) :
    Nonempty (PrimeGammaTwoThreeSourceNaturalReporter t) ↔
      PrimeGammaTwoThreeSourceNaturalInverseGhost t := by
  constructor
  · rintro ⟨h⟩
    exact sourceNaturality_of_primeGammaTwoThreeSharedGhost
      (primeGammaTwoThreeSharedGhost_of_naturalReporter h)
  · exact primeGammaTwoThreeNaturalReporter_nonempty_of_sourceNaturalInverseGhost

theorem primeGammaTwoThreeSourceNaturalInverseGhost_iff (t : ℝ) :
    PrimeGammaTwoThreeSourceNaturalInverseGhost t ↔ t = 0 := by
  rw [primeGammaTwoThreeSourceNaturalInverseGhost_iff_sharedGhost,
    primeGammaTwoThreeSharedInverseOrientedGhostWard_iff]

/-- Pointwise producer on an actual Xi divisor support, preserving divisor multiplicity. -/
def FrankensteinSourceGammaNaturalSharedGhostDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  Nonempty
    (PrimeGammaTwoThreeSourceNaturalReporter (2 * (rho : ℂ).re - 1))

theorem frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff_sharedGhost
    (rho : XiDivisorSupport) :
    FrankensteinSourceGammaNaturalSharedGhostDescendsAt rho ↔
      FrankensteinSourceSelectedGammaWardSharedGhostDescendsAt rho := by
  rw [FrankensteinSourceGammaNaturalSharedGhostDescendsAt,
    primeGammaTwoThreeSourceNaturalReporter_nonempty_iff]
  exact primeGammaTwoThreeSourceNaturalInverseGhost_iff_sharedGhost _

theorem frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinSourceGammaNaturalSharedGhostDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff_sharedGhost,
    frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff]

def EveryFrankensteinSourceGammaNaturalSharedGhostDescends : Prop :=
  ∀ rho : XiDivisorSupport, FrankensteinSourceGammaNaturalSharedGhostDescendsAt rho

theorem everyFrankensteinSourceGammaNaturalSharedGhostDescends_iff_riemannHypothesis :
    EveryFrankensteinSourceGammaNaturalSharedGhostDescends ↔ RiemannHypothesis := by
  rw [← everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis]
  unfold EveryFrankensteinSourceGammaNaturalSharedGhostDescends
    EveryFrankensteinSourceSelectedGammaWardSharedGhostDescends
  apply forall_congr'
  exact frankensteinSourceGammaNaturalSharedGhostDescendsAt_iff_sharedGhost

end

end RHTower
