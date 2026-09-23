import GaloisForLFunctions.HTGeometry.HelsonFiniteEulerGauge
import GaloisForLFunctions.RHTower.PrimeEulerOrientationNorm

/-!
# Exact analytic Euler modes of a projective prime tail

The signed prime tail quotient remembers a Boolean orientation only up to finite changes and global
complement.  This file realizes both alternatives by actual Helson Dirichlet series.  Same tails
differ by a finite Euler gauge; opposite tails have product `ζ(2s)` times the finite defect gauge.
The final equivalence has no third analytic lifting mode.
-/

noncomputable section

open Complex ArithmeticFunction LSeries
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-- Canonical square-one complex phase attached to a Boolean prime orientation. -/
def booleanPrimePhase (ε : Nat.Primes → Bool) (n : ℕ) : ℂ :=
  if hn : Nat.Prime n then primeDirichletSign (ε ⟨n, hn⟩) else 1

@[simp]
theorem booleanPrimePhase_prime (ε : Nat.Primes → Bool) (p : Nat.Primes) :
    booleanPrimePhase ε (p : ℕ) = primeDirichletSign (ε p) := by
  simp [booleanPrimePhase, p.2]

theorem norm_booleanPrimePhase_prime (ε : Nat.Primes → Bool) (p : ℕ)
    (hp : Nat.Prime p) : ‖booleanPrimePhase ε p‖ = 1 := by
  cases hε : ε ⟨p, hp⟩ <;> simp [booleanPrimePhase, hp, hε, primeDirichletSign]

theorem sq_booleanPrimePhase_prime (ε : Nat.Primes → Bool) (p : ℕ)
    (hp : Nat.Prime p) : booleanPrimePhase ε p ^ (2 : ℕ) = 1 := by
  cases hε : ε ⟨p, hp⟩ <;> norm_num [booleanPrimePhase, hp, hε, primeDirichletSign]

/-- Helson Dirichlet series of a Boolean prime orientation. -/
def booleanPrimeHelsonLSeries (ε : Nat.Primes → Bool) (s : ℂ) : ℂ :=
  LSeries (fun n => phaseChar (booleanPrimePhase ε) n) s

/-- Finite same-sheet gauge between two Boolean orientations. -/
def booleanPrimeFiniteEulerGauge
    (P : Finset Nat.Primes) (ε δ : Nat.Primes → Bool) (s : ℂ) : ℂ :=
  GaloisForLFunctions.finiteEulerGaugeRatio P
    (fun p : Nat.Primes => ((p : ℕ) : ℝ))
    (fun p : Nat.Primes => booleanPrimePhase ε (p : ℕ))
    (fun p : Nat.Primes => booleanPrimePhase δ (p : ℕ)) s

/-- Finite gauge from the complement of `ε` to `δ`. -/
def booleanPrimeOppositeFiniteEulerGauge
    (P : Finset Nat.Primes) (ε δ : Nat.Primes → Bool) (s : ℂ) : ℂ :=
  GaloisForLFunctions.finiteEulerGaugeRatio P
    (fun p : Nat.Primes => ((p : ℕ) : ℝ))
    (fun p : Nat.Primes => -booleanPrimePhase ε (p : ℕ))
    (fun p : Nat.Primes => booleanPrimePhase δ (p : ℕ)) s

/-- Same-sheet mode: eventual equality plus its exact analytic finite-gauge identity. -/
def BooleanPrimeSameSheetAnalyticMode (ε δ : Nat.Primes → Bool) : Prop :=
  ∃ P : Finset Nat.Primes,
    (∀ p : Nat.Primes, p ∉ P → ε p = δ p) ∧
    ∀ s : ℂ, 1 < s.re →
      booleanPrimeHelsonLSeries δ s =
        booleanPrimeHelsonLSeries ε s * booleanPrimeFiniteEulerGauge P ε δ s

/-- Opposite-sheet mode: eventual opposition plus its exact analytic norm identity. -/
def BooleanPrimeOppositeSheetAnalyticMode (ε δ : Nat.Primes → Bool) : Prop :=
  ∃ P : Finset Nat.Primes,
    (∀ p : Nat.Primes, p ∉ P → ε p ≠ δ p) ∧
    ∀ s : ℂ, 1 < s.re →
      booleanPrimeHelsonLSeries ε s * booleanPrimeHelsonLSeries δ s =
        riemannZeta (2 * s) * booleanPrimeOppositeFiniteEulerGauge P ε δ s

/-- **Exact tail-field/Euler-gauge correspondence.**  Projective dependence of Boolean prime
tails is equivalent to exactly two realized analytic modes: finite same-sheet gauge equivalence or
finite-defect opposite-sheet norm complementarity. -/
theorem primeOrientationTailPairDependent_iff_analyticEulerModes
    (ε δ : Nat.Primes → Bool) :
    PrimeOrientationTailPairDependent ε δ ↔
      BooleanPrimeSameSheetAnalyticMode ε δ ∨
        BooleanPrimeOppositeSheetAnalyticMode ε δ := by
  constructor
  · intro hdep
    rcases (primeOrientationTailPairDependent_iff_eulerModes ε δ).mp hdep with hsame | hopp
    · have hfin := (primeEulerTailGaugeEquivalent_iff_eventuallyEqual ε δ).mp hsame
      let P : Finset Nat.Primes := hfin.toFinset
      have hP : ∀ p : Nat.Primes, p ∉ P → ε p = δ p := by
        intro p hp
        by_contra hne
        exact hp (hfin.mem_toFinset.mpr hne)
      refine Or.inl ⟨P, hP, ?_⟩
      intro s hs
      have hphase : ∀ p : Nat.Primes, p ∉ P →
          booleanPrimePhase ε (p : ℕ) = booleanPrimePhase δ (p : ℕ) := by
        intro p hp
        simp [hP p hp]
      exact LSeries_phaseChar_eq_mul_finiteEulerGaugeRatio_of_eq_off_finset
        (fun p hp => norm_booleanPrimePhase_prime ε p hp)
        (fun p hp => norm_booleanPrimePhase_prime δ p hp) P hphase hs
    · have hfin := (primeEulerTailNormComplementary_iff_eventuallyOpposite ε δ).mp hopp
      let P : Finset Nat.Primes := hfin.toFinset
      have hP : ∀ p : Nat.Primes, p ∉ P → ε p ≠ δ p := by
        intro p hp heq
        exact hp (hfin.mem_toFinset.mpr heq)
      refine Or.inr ⟨P, hP, ?_⟩
      intro s hs
      have hphase : ∀ p : Nat.Primes, p ∉ P →
          booleanPrimePhase δ (p : ℕ) = -booleanPrimePhase ε (p : ℕ) := by
        intro p hp
        simpa using primeDirichletSign_eq_neg_of_ne (hP p hp)
      exact
        LSeries_phaseChar_mul_eq_riemannZeta_two_mul_mul_finiteEulerGaugeRatio_of_opposite_off_finset
          (fun p hp => norm_booleanPrimePhase_prime ε p hp)
          (fun p hp => norm_booleanPrimePhase_prime δ p hp)
          (fun p hp => sq_booleanPrimePhase_prime ε p hp) P hphase hs
  · rintro (⟨P, hP, _⟩ | ⟨P, hP, _⟩)
    · apply (primeOrientationTailPairDependent_iff_eulerModes ε δ).mpr
      left
      apply (primeEulerTailGaugeEquivalent_iff_eventuallyEqual ε δ).mpr
      refine P.finite_toSet.subset ?_
      intro p hne
      by_contra hp
      exact hne (hP p hp)
    · apply (primeOrientationTailPairDependent_iff_eulerModes ε δ).mpr
      right
      apply (primeEulerTailNormComplementary_iff_eventuallyOpposite ε δ).mpr
      refine P.finite_toSet.subset ?_
      intro p heq
      by_contra hp
      exact hP p hp heq

end GaloisForLFunctions.RHTower
