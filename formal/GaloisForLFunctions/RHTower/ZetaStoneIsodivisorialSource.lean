import GaloisForLFunctions.HTGeometry.IsodivisorialPrimeWalshStoneSaturation
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# Zeta sources with arbitrary pointed Stone tail geometry

Every pointed compact metrizable Stone space is realized by a sparse Boolean prime system.  The
associated sign phase is an exponent-zero Euler gauge, so multiplying the Riemann zeta function
by its canonical Euler-ratio unit gives a meromorphic source with exactly the same complete signed
divisor throughout the positive half-plane.  The distinguished Stone anchor gives zeta itself.

The final theorem records the precise reconstruction obstruction: every observable depending only
on the complete positive-half-plane divisor is constant on all source coordinates of every such
Stone realization.
-/

open CategoryTheory Topology TopologicalSpace

namespace RHTower

open Complex Set
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sparse prime orientation attached to one coordinate of a pointed Stone realization. -/
def zetaStonePrimeOrientation
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) : Nat.Primes → Bool :=
  sparseClosedConstraintPrimeOrientation (pointedStoneConstraint S base) j

/-- Exponent-zero prime phase attached to one coordinate of a pointed Stone realization. -/
def zetaStonePrimePhase
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) : PrimePhase Nat.Primes :=
  boolOrientationPrimePhase (zetaStonePrimeOrientation S base j)

/-- Canonical same-divisor continuation of the Stone-coordinate Euler source. -/
def zetaStoneContinuedSource
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) : ℂ → ℂ :=
  exponentZeroGaugeContinuedSource (1 : PrimePhase Nat.Primes)
    (zetaStonePrimePhase S base j) riemannZeta

/-- Every Stone-coordinate phase is an exponent-zero Euler gauge. -/
theorem zetaStonePrimePhase_isExponentZeroEulerGauge
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) :
    IsExponentZeroEulerGauge natPrimeSize (zetaStonePrimePhase S base j) := by
  exact sparseClosedConstraintPrimePhase_isExponentZeroEulerGauge
    (pointedStoneConstraint S base) j

/-- Riemann zeta is meromorphic throughout the positive half-plane. -/
theorem meromorphicOn_riemannZeta_positiveHalfPlane :
    MeromorphicOn riemannZeta positiveHalfPlane := by
  intro z hz
  by_cases hz1 : z = 1
  · subst z
    exact meromorphicAt_riemannZeta_one
  · exact (analyticOn_riemannZeta z hz1).meromorphicAt

/-- Every Stone-coordinate continued source is meromorphic on the positive half-plane. -/
theorem meromorphicOn_zetaStoneContinuedSource
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) :
    MeromorphicOn (zetaStoneContinuedSource S base j) positiveHalfPlane := by
  exact meromorphicOn_exponentZeroGaugeContinuedSource
    (1 : PrimePhase Nat.Primes) (zetaStonePrimePhase S base j)
    (zetaStonePrimePhase_isExponentZeroEulerGauge S base j)
    meromorphicOn_riemannZeta_positiveHalfPlane

/-- Every Stone-coordinate continued source has exactly the complete zeta divisor, including
multiplicity, at every point of the positive half-plane. -/
theorem zetaStone_completePositiveHalfPlaneDivisor_eq
    (S : LightProfinite) (base : S)
    (j : Unit ⊕ Clopens (lightToProfinite.obj S)) :
    ∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt (zetaStoneContinuedSource S base j) z =
        meromorphicOrderAt riemannZeta z := by
  exact sparseClosedConstraint_completePositiveHalfPlaneDivisor_eq
    (pointedStoneConstraint S base) (1 : PrimePhase Nat.Primes) riemannZeta j

/-- The distinguished anchor coordinate is exactly zeta on the positive half-plane. -/
theorem zetaStone_anchor_eq_riemannZeta
    (S : LightProfinite) (base : S) :
    ∀ z ∈ positiveHalfPlane,
      zetaStoneContinuedSource S base (Sum.inl ()) z = riemannZeta z := by
  exact sparseClosedConstraint_anchor_eq_base
    (pointedStoneConstraint S base) (Sum.inl ())
    (pointedStoneConstraint_anchor S base)
    (1 : PrimePhase Nat.Primes) riemannZeta

/-- The recurring prime-tail pattern chamber of the source family is the prescribed pointed Stone
space, in its canonical Boolean realization. -/
theorem zetaStone_recurringPatternChamber_eq
    (S : LightProfinite) (base : S) (pi : ℕ ≃ Nat.Primes) :
    primeRecurringPatternChamber pi (zetaStonePrimeOrientation S base) =
      pointedStoneConstraint S base := by
  exact pointedStoneConstraint_sparsePrime_realization S base pi

/-- An observable is a positive-half-plane divisor profile when it depends only on the complete
signed meromorphic-order function on that half-plane. -/
def IsPositiveHalfPlaneDivisorProfile {Y : Type*}
    (observable : (ℂ → ℂ) → Y) : Prop :=
  ∀ f g : ℂ → ℂ,
    (∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt f z = meromorphicOrderAt g z) →
    observable f = observable g

/-- **Zeta--Stone divisor-profile constancy law.**  Every complete-divisor observable is constant
on all source coordinates of every pointed compact metrizable Stone realization. -/
theorem zetaStone_divisorProfile_constant
    {Y : Type*} (observable : (ℂ → ℂ) → Y)
    (hobservable : IsPositiveHalfPlaneDivisorProfile observable)
    (S : LightProfinite) (base : S)
    (j k : Unit ⊕ Clopens (lightToProfinite.obj S)) :
    observable (zetaStoneContinuedSource S base j) =
      observable (zetaStoneContinuedSource S base k) := by
  apply hobservable
  intro z hz
  exact (zetaStone_completePositiveHalfPlaneDivisor_eq S base j z hz).trans
    (zetaStone_completePositiveHalfPlaneDivisor_eq S base k z hz).symm

end

end RHTower
