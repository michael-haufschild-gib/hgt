import GaloisForLFunctions.RHTower.SourceGammaChannelPositiveHermitianScalarizationNoGo

/-!
# Coherent joint quadratic source/Gamma scalarization no-go

The channel-resolved prime--Gamma reporter has two genuine source-boundary outputs
`(0,d(t))` and `(-d(t),0)`, where `d(t)=2⁻ᵗ-3⁻ᵗ`.  Positive Hermitian scalarization of the
separate outputs was already known to be nonselective.  This file closes the coherent escape:
concatenate both boundaries and allow one arbitrary fixed complex `4×4` quadratic observable,
including indefinite, non-Hermitian, off-channel, and cross-boundary terms.

The coherent four-vector is exactly

`d(t) * (0,1,-1,0)`.

Hence every quadratic observable compresses to

`kappa(A) * normSq(d(t))`,

where `kappa(A)=Re(A₁₁-A₁₂-A₂₁+A₂₂)`.  If `kappa(A)=0`, the observable is blind at every
horizontal grade.  Otherwise its zero locus is exactly `t=0`; on actual Xi support, universal
darkness is both RH and the shared HB/FZZ-P/PW-B/RBH Ward endpoint.

**Route killed.** Fixed coherent quadratic postprocessing cannot supply the producer in

`source/Gamma coherent mixing -> shared four-route Ward extinction -> RH`.

The exact positive survivor is the rank-one compression invariant `kappa(A)`.  A viable producer
must introduce another independent source feature, use a genuinely nonlinear/source-adaptive law,
or derive the cross-prime leak itself to vanish from dynamics.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- The two genuine prime--archimedean boundaries, retained coherently in one four-coordinate
joint channel. -/
def primeGammaTwoThreeCoherentJointBoundaryVector (t : ℝ) : Fin 4 → ℂ :=
  let two :=
    deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeTwo))
  let three :=
    deningerCalderonWittChannelResolvedInverseGammaReporter t
      (deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
          deningerCalderonWittPrimeThree))
  ![two.1, two.2, three.1, three.2]

/-- Both genuine source boundaries lie on one exact coherent complex line. -/
theorem primeGammaTwoThreeCoherentJointBoundaryVector_eq (t : ℝ) :
    primeGammaTwoThreeCoherentJointBoundaryVector t =
      ![0, primeGammaTwoThreeChannelGhostMismatch t,
        -primeGammaTwoThreeChannelGhostMismatch t, 0] := by
  rw [primeGammaTwoThreeCoherentJointBoundaryVector,
    deningerCalderonWittChannelResolvedInverseGammaReporter_twoBoundary,
    deningerCalderonWittChannelResolvedInverseGammaReporter_threeBoundary]
  funext i
  fin_cases i <;> simp [primeGammaTwoThreeChannelGhostMismatch]

/-- Arbitrary fixed complex quadratic observable on the coherent pair of source boundaries. -/
def primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable
    (A : Matrix (Fin 4) (Fin 4) ℂ) (t : ℝ) : ℝ :=
  let v := primeGammaTwoThreeCoherentJointBoundaryVector t
  (star v ⬝ᵥ A *ᵥ v).re

/-- Compression of a joint quadratic observable to the actual one-dimensional boundary orbit. -/
def primeGammaTwoThreeCoherentJointQuadraticCompression
    (A : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  (A 1 1 - A 1 2 - A 2 1 + A 2 2).re

/-- **Exact rank-one compression.**  No positivity, Hermiticity, or channel-separation
hypothesis is needed. -/
theorem primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq
    (A : Matrix (Fin 4) (Fin 4) ℂ) (t : ℝ) :
    primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable A t =
      primeGammaTwoThreeCoherentJointQuadraticCompression A *
        Complex.normSq (primeGammaTwoThreeChannelGhostMismatch t) := by
  rw [primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable,
    primeGammaTwoThreeCoherentJointBoundaryVector_eq]
  simp [primeGammaTwoThreeCoherentJointQuadraticCompression, dotProduct, mulVec,
    Fin.sum_univ_four, Complex.normSq_apply]
  ring

/-- A compression-blind observable vanishes at every horizontal grade. -/
theorem primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq_zero_of_compression_eq_zero
    {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : primeGammaTwoThreeCoherentJointQuadraticCompression A = 0) (t : ℝ) :
    primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable A t = 0 := by
  rw [primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq, hA, zero_mul]

/-- Every nonblind arbitrary joint quadratic observable has the exact shared-Ward zero locus. -/
theorem primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq_zero_iff
    {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : primeGammaTwoThreeCoherentJointQuadraticCompression A ≠ 0) (t : ℝ) :
    primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable A t = 0 ↔ t = 0 := by
  rw [primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq]
  constructor
  · intro h
    have hnorm : Complex.normSq (primeGammaTwoThreeChannelGhostMismatch t) = 0 :=
      (mul_eq_zero.mp h).resolve_left hA
    exact (primeGammaTwoThreeChannelGhostMismatch_eq_zero_iff t).mp
      (Complex.normSq_eq_zero.mp hnorm)
  · intro ht
    rw [(primeGammaTwoThreeChannelGhostMismatch_eq_zero_iff t).mpr ht]
    simp

/-- Universal coherent joint quadratic darkness over actual Xi support. -/
def EveryFrankensteinCoherentJointQuadraticBoundaryObservableZero
    (A : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ rho : XiDivisorSupport,
    primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable A
      (2 * (rho : ℂ).re - 1) = 0

/-- Every nonblind arbitrary joint quadratic observable is exactly an RH receiver. -/
theorem everyFrankensteinCoherentJointQuadraticBoundaryObservableZero_iff_riemannHypothesis
    {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : primeGammaTwoThreeCoherentJointQuadraticCompression A ≠ 0) :
    EveryFrankensteinCoherentJointQuadraticBoundaryObservableZero A ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht :=
        (primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq_zero_iff
          hA (2 * (rho : ℂ).re - 1)).mp (h rho)
      linarith
  · intro h rho
    apply
      (primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq_zero_iff
        hA (2 * (rho : ℂ).re - 1)).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

/-- The same darkness law is exactly the shared HB/FZZ-P/PW-B/RBH Ward endpoint. -/
theorem everyFrankensteinCoherentJointQuadraticBoundaryObservableZero_iff_sharedFourRouteWardEndpoint
    {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : primeGammaTwoThreeCoherentJointQuadraticCompression A ≠ 0) :
    EveryFrankensteinCoherentJointQuadraticBoundaryObservableZero A ↔
      SharedFourRouteWardEndpoint := by
  have hshared : SharedFourRouteWardEndpoint ↔ RiemannHypothesis :=
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.symm.trans
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis
  exact
    (everyFrankensteinCoherentJointQuadraticBoundaryObservableZero_iff_riemannHypothesis
      hA).trans hshared.symm

/-- Closed classification of every fixed complex quadratic observable on the coherent pair. -/
def SharedWardCoherentJointQuadraticScalarizationRouteKilled : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℂ,
    ((primeGammaTwoThreeCoherentJointQuadraticCompression A = 0 ∧
        ∀ t : ℝ,
          primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable A t = 0) ∨
      (primeGammaTwoThreeCoherentJointQuadraticCompression A ≠ 0 ∧
        (EveryFrankensteinCoherentJointQuadraticBoundaryObservableZero A ↔
          SharedFourRouteWardEndpoint) ∧
        (EveryFrankensteinCoherentJointQuadraticBoundaryObservableZero A ↔
          RiemannHypothesis)))

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Arbitrary coherent cross-boundary quadratic mixing is
blind or an exact four-route/RH receiver; it cannot manufacture the missing source law. -/
theorem sharedWardCoherentJointQuadraticScalarizationRouteKilled :
    SharedWardCoherentJointQuadraticScalarizationRouteKilled := by
  intro A
  by_cases hA : primeGammaTwoThreeCoherentJointQuadraticCompression A = 0
  · left
    exact ⟨hA,
      primeGammaTwoThreeCoherentJointQuadraticBoundaryObservable_eq_zero_of_compression_eq_zero
        hA⟩
  · right
    exact ⟨hA,
      everyFrankensteinCoherentJointQuadraticBoundaryObservableZero_iff_sharedFourRouteWardEndpoint
        hA,
      everyFrankensteinCoherentJointQuadraticBoundaryObservableZero_iff_riemannHypothesis hA⟩

end

end RHTower
