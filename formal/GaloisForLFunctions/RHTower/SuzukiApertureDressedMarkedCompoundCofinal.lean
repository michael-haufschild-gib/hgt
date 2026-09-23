import GaloisForLFunctions.RHTower.SuzukiApertureDressedWallLightCompletion
import GaloisForLFunctions.RHTower.SuzukiGlobalLocalCompoundBezoutianWeld
import GaloisForLFunctions.RHTower.SuzukiWallFieldProjectiveDensitySeparationLaw

/-!
# Cofinal aperture dressing of Suzuki's marked compound carrier

The bare critical wall amplitude performs two jobs in the Suzuki frontier: its positive diagonal
pays the sharp marked-secant halfgap debt, while its quadratic determinant-line density carries
the far prime current.  Bare all-prime mass diverges, so these two jobs cannot be assembled by
first forming an ordinary critical Hilbert vector.

The actual cubic aperture innovation resolves both jobs before the cofinal limit.  This module
proves, for one fixed marked base packet:

* squares of the dressed boundary atoms are absolutely summable over prime and valuation depth;
* the sharp rooted completion built from their norms is a nonnegative summable family;
* the complete division-free marked local--global compound term factors through the same atom
  square, is absolutely summable, and has an exact cofinal sum.

Thus halfgap completion and determinant-line cofinalization do not require two copies of the wall
mass.  They are two quadratic faces of the same pre-split dressed source.  This does not identify
the resulting cofinal compound with the rectangular Xi/Robin/Gamma/holonomy trace; that occurrence
and its remaining Schur comparison are still the RH-bearing gate.

No RH premise, Xi-zero hypothesis, computation, or infinite subtraction is used.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-- Squaring the actual aperture-dressed boundary atom preserves absolute summability over the
complete prime--valuation carrier. -/
theorem summable_sq_suzukiCriticalApertureBoundaryAtom_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 ^ (2 : ℕ)) := by
  have hs := summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  apply Summable.of_norm
  refine hs.congr ?_
  intro pe
  rw [Complex.normSq_eq_norm_sq, norm_pow]

/-- Sharp marked halfgap block carried by the norm of one dressed boundary atom. -/
def suzukiCriticalApertureDressedMarkedRootedCompletion
    (h a t m d r s : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  let omega := ‖suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2‖
  suzukiMarkedSecantSymmetricForm m d
      (omega * r) (omega * s) (omega * r) (omega * s) +
    d ^ (2 : ℕ) * (omega * s) ^ (2 : ℕ)

/-- The dressed marked block is exactly the atom energy times the centered rank-one square. -/
theorem suzukiCriticalApertureDressedMarkedRootedCompletion_eq
    (h a t m d r s : ℝ) (pe : Nat.Primes × ℕ) :
    suzukiCriticalApertureDressedMarkedRootedCompletion h a t m d r s pe =
      Complex.normSq (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) *
        (r - m * s) ^ (2 : ℕ) := by
  rw [suzukiCriticalApertureDressedMarkedRootedCompletion]
  rw [suzukiMarkedSecant_minimalRootedCompletion_eq_square]
  rw [Complex.normSq_eq_norm_sq]
  ring

/-- Every dressed marked rooted-completion cell is nonnegative. -/
theorem suzukiCriticalApertureDressedMarkedRootedCompletion_nonneg
    (h a t m d r s : ℝ) (pe : Nat.Primes × ℕ) :
    0 ≤ suzukiCriticalApertureDressedMarkedRootedCompletion h a t m d r s pe := by
  rw [suzukiCriticalApertureDressedMarkedRootedCompletion_eq]
  exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

/-- The complete dressed halfgap completion is summable over primes and valuation depths. -/
theorem summable_suzukiCriticalApertureDressedMarkedRootedCompletion_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t m d r s : ℝ) :
    Summable (suzukiCriticalApertureDressedMarkedRootedCompletion h a t m d r s) := by
  have hs := summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  refine (hs.mul_right ((r - m * s) ^ (2 : ℕ))).congr ?_
  intro pe
  exact
    (suzukiCriticalApertureDressedMarkedRootedCompletion_eq
      h a t m d r s pe).symm

/-- One aperture-dressed, division-free marked local--global compound cell.  All five local
marked coordinates use the same actual boundary atom, so numerator and denominator retain the
same determinant-line density before projective division. -/
def suzukiCriticalApertureDressedMarkedCompoundTerm
    (h a t : ℝ) (alpha beta x X y Y c S T : ℂ)
    (pe : Nat.Primes × ℕ) : ℂ :=
  let omega := suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2
  suzukiGlobalLocalCompoundNumerator
    (suzukiProjectiveAffineSecantTensor alpha beta
      (omega * x) (omega * X) (omega * y) (omega * Y) (omega * c))
    (suzukiProjectiveAffineSecantDenominator alpha beta
      (omega * y) (omega * Y)) S T

/-- Homogeneity of both local projective coordinates makes the full compound cell one dressed
atom square times the undressed marked compound.  No separate counterterm is present. -/
theorem suzukiCriticalApertureDressedMarkedCompoundTerm_eq
    (h a t : ℝ) (alpha beta x X y Y c S T : ℂ)
    (pe : Nat.Primes × ℕ) :
    suzukiCriticalApertureDressedMarkedCompoundTerm
        h a t alpha beta x X y Y c S T pe =
      suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 ^ (2 : ℕ) *
        suzukiGlobalLocalCompoundNumerator
          (suzukiProjectiveAffineSecantTensor alpha beta x X y Y c)
          (suzukiProjectiveAffineSecantDenominator alpha beta y Y) S T := by
  rw [suzukiCriticalApertureDressedMarkedCompoundTerm]
  rw [suzukiProjectiveAffineSecantTensor_commonScale,
    suzukiProjectiveAffineSecantDenominator_commonScale]
  simp only [suzukiGlobalLocalCompoundNumerator]
  ring

/-- Aperture dressing makes the complete division-free marked compound family absolutely
summable on the joint prime--valuation carrier. -/
theorem summable_suzukiCriticalApertureDressedMarkedCompoundTerm_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ)
    (alpha beta x X y Y c S T : ℂ) :
    Summable (suzukiCriticalApertureDressedMarkedCompoundTerm
      h a t alpha beta x X y Y c S T) := by
  have hs := summable_sq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  refine (hs.mul_right
    (suzukiGlobalLocalCompoundNumerator
      (suzukiProjectiveAffineSecantTensor alpha beta x X y Y c)
      (suzukiProjectiveAffineSecantDenominator alpha beta y Y) S T)).congr ?_
  intro pe
  exact
    (suzukiCriticalApertureDressedMarkedCompoundTerm_eq
      h a t alpha beta x X y Y c S T pe).symm

/-- Exact cofinal compound law: the completed marked carrier is the scalar dressed determinant
line times the undressed local--global compound. -/
theorem tsum_suzukiCriticalApertureDressedMarkedCompoundTerm_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ)
    (alpha beta x X y Y c S T : ℂ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedCompoundTerm
        h a t alpha beta x X y Y c S T pe) =
      (∑' pe : Nat.Primes × ℕ,
        suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 ^ (2 : ℕ)) *
        suzukiGlobalLocalCompoundNumerator
          (suzukiProjectiveAffineSecantTensor alpha beta x X y Y c)
          (suzukiProjectiveAffineSecantDenominator alpha beta y Y) S T := by
  have hs := summable_sq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  rw [show (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedMarkedCompoundTerm
        h a t alpha beta x X y Y c S T pe) =
      ∑' pe : Nat.Primes × ℕ,
        suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2 ^ (2 : ℕ) *
          suzukiGlobalLocalCompoundNumerator
            (suzukiProjectiveAffineSecantTensor alpha beta x X y Y c)
            (suzukiProjectiveAffineSecantDenominator alpha beta y Y) S T by
      apply tsum_congr
      intro pe
      exact suzukiCriticalApertureDressedMarkedCompoundTerm_eq
        h a t alpha beta x X y Y c S T pe]
  exact hs.tsum_mul_right _

end

end RHTower
