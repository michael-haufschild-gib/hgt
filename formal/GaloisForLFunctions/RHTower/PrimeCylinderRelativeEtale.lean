import GaloisForLFunctions.HTGeometry.AlgebraicGroupJet
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Etale.Pi

/-!
# Relative formal étaleness of finite prime cylinders

An internal Xi jet is allowed to be nonreduced.  Fix its truncated arc algebra as base ring.
A finite prime-valuation cylinder is then a finite product of copies of that base, one for each
valuation configuration.  It is formally étale over the internal jet ring.

Consequently one reduced finite-cylinder source map cannot split into two distinct lifts across an
additional nilpotent ideal.  Internal multiplicity survives in the base; only a new transverse
infinitesimal branch is forbidden.  This is the finite-stage non-bifurcation law needed by the
derived arithmetic-completion route.  It makes no claim that the infinite Möbius--theta completion
preserves formal étaleness.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Valuation labels on one finite prime support with a common finite depth cutoff. -/
abbrev FinitePrimeValuationConfiguration
    (P : Finset Nat.Primes) (depth : ℕ) :=
  (p : P) → Fin (depth + 1)

/-- Finite prime-cylinder observables valued in the order-`jetOrder` internal jet algebra. -/
abbrev InternalJetPrimeCylinderAlgebra
    (P : Finset Nat.Primes) (depth jetOrder : ℕ) :=
  FinitePrimeValuationConfiguration P depth →
    TruncatedArcAlgebra ℂ jetOrder

/-- Finite discrete occupation labels add no infinitesimal direction relative to the internal jet.
Equivalently, every finite cylinder is formally étale over its internal nonreduced base. -/
instance internalJetPrimeCylinderAlgebra_formallyEtale
    (P : Finset Nat.Primes) (depth jetOrder : ℕ) :
    Algebra.FormallyEtale (TruncatedArcAlgebra ℂ jetOrder)
      (InternalJetPrimeCylinderAlgebra P depth jetOrder) := by
  dsimp [InternalJetPrimeCylinderAlgebra]
  infer_instance

/-- A transverse bifurcation is a pair of distinct finite-cylinder lifts which become equal after
discarding one nilpotent target ideal.  The nilpotents already present in the internal jet base are
not discarded and therefore are not classified as transverse. -/
def ArithmeticCylinderTransverseBifurcation
    (P : Finset Nat.Primes) (depth jetOrder : ℕ)
    (B : Type*) [CommRing B]
    [Algebra (TruncatedArcAlgebra ℂ jetOrder) B]
    (I : Ideal B) : Prop :=
  ∃ forward reflected :
      InternalJetPrimeCylinderAlgebra P depth jetOrder →ₐ[
        TruncatedArcAlgebra ℂ jetOrder] B,
    forward ≠ reflected ∧
      (Ideal.Quotient.mkₐ (TruncatedArcAlgebra ℂ jetOrder) I).comp forward =
        (Ideal.Quotient.mkₐ (TruncatedArcAlgebra ℂ jetOrder) I).comp reflected

/-- **Finite-stage arithmetic non-bifurcation.**  No finite prime cylinder can acquire two
different reflection-normal lifts which agree after a nilpotent transverse quotient. -/
theorem no_arithmeticCylinderTransverseBifurcation
    (P : Finset Nat.Primes) (depth jetOrder : ℕ)
    (B : Type*) [CommRing B]
    [Algebra (TruncatedArcAlgebra ℂ jetOrder) B]
    (I : Ideal B) (hI : IsNilpotent I) :
    ¬ ArithmeticCylinderTransverseBifurcation P depth jetOrder B I := by
  rintro ⟨forward, reflected, hne, hagree⟩
  apply hne
  exact Algebra.FormallyUnramified.lift_unique I hI forward reflected hagree

end

end RHTower
