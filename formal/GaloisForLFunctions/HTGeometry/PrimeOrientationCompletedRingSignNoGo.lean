import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationCompactOpen

/-!
# The completed prime-orientation ring cannot classify Herglotz sign

Compact-open completion erases the Boolean prime-residue orientation: every orientation generates
the same completed common-atom ring.  Herglotz positivity, however, selects exactly the
all-positive orientation.  This file records the resulting exact classifier no-go and its
positive survivor: unequal orientations are still separated by a pointed simple-pole residue.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Herglotz positivity for the universal prime-orientation carrier. -/
def IsHerglotzPrimeOrientation (ε : Nat.Primes → Bool) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientationLimit ε z).im

theorem isHerglotzPrimeOrientation_iff_allPositive (ε : Nat.Primes → Bool) :
    IsHerglotzPrimeOrientation ε ↔ ε = fun _ => false := by
  exact universalPrimeOrientationLimit_nonneg_iff_allPositive ε

/-- One explicit pair of opposite Herglotz status has exactly the same completed common-atom
ring.  Thus completion has forgotten the sign needed by the analytic order. -/
theorem exists_primeOrientation_completedRing_collision_oppositeHerglotz :
    ∃ ε δ : Nat.Primes → Bool,
      ε ≠ δ ∧
      primeOrientationCompletedRing ε = primeOrientationCompletedRing δ ∧
      IsHerglotzPrimeOrientation ε ∧
      ¬ IsHerglotzPrimeOrientation δ := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let ε : Nat.Primes → Bool := fun _ => false
  let δ : Nat.Primes → Bool := fun q => decide (q = p)
  refine ⟨ε, δ, ?_, primeOrientationCompletedRing_eq ε δ, ?_, ?_⟩
  · intro hεδ
    have hp := congrFun hεδ p
    simp [ε, δ] at hp
  · exact (isHerglotzPrimeOrientation_iff_allPositive ε).2 rfl
  · intro hδ
    have hall := (isHerglotzPrimeOrientation_iff_allPositive δ).1 hδ
    have hp := congrFun hall p
    simp [δ] at hp

/-- No predicate of the completed common-atom ring can recover Herglotz positivity. -/
theorem no_primeOrientationCompletedRing_HerglotzClassifier :
    ¬ ∃ P : Subring C(PrimeOrientationDomain, ℂ) → Prop,
      ∀ ε : Nat.Primes → Bool,
        P (primeOrientationCompletedRing ε) ↔ IsHerglotzPrimeOrientation ε := by
  rintro ⟨P, hP⟩
  obtain ⟨ε, δ, _, hring, hε, hδ⟩ :=
    exists_primeOrientation_completedRing_collision_oppositeHerglotz
  have hpε : P (primeOrientationCompletedRing ε) := (hP ε).2 hε
  have hpδ : P (primeOrientationCompletedRing δ) := by
    rw [← hring]
    exact hpε
  exact hδ ((hP δ).1 hpδ)

/-- Positive survivor of the completion no-go: before quotienting by the common completed ring,
the pointed simple-pole residues separate every pair of unequal prime orientations. -/
theorem exists_primeOrientation_residue_separation_of_ne
    {ε δ : Nat.Primes → Bool} (hεδ : ε ≠ δ) :
    ∃ p : Nat.Primes,
      -(universalPrimeOrientationWeight ε p : ℂ) ≠
          -(universalPrimeOrientationWeight δ p : ℂ) ∧
      HasSimplePoleAt
        (universalPrimeOrientationLimit ε)
        (primeLogSupport p : ℂ)
        (-(universalPrimeOrientationWeight ε p : ℂ)) ∧
      HasSimplePoleAt
        (universalPrimeOrientationLimit δ)
        (primeLogSupport p : ℂ)
        (-(universalPrimeOrientationWeight δ p : ℂ)) := by
  have hcoord : ∃ p : Nat.Primes, ε p ≠ δ p := by
    by_contra h
    push Not at h
    exact hεδ (funext h)
  obtain ⟨p, hp⟩ := hcoord
  refine ⟨p, ?_, hasSimplePoleAt_universalPrimeOrientationLimit ε p,
    hasSimplePoleAt_universalPrimeOrientationLimit δ p⟩
  have hweight : universalPrimeOrientationWeight ε p ≠
      universalPrimeOrientationWeight δ p := by
    cases hεp : ε p <;> cases hδp : δ p <;>
      simp_all [universalPrimeOrientationWeight] <;>
      nlinarith [universalPrimeWeight_pos p]
  exact fun h => hweight (Complex.ofReal_injective (neg_injective h))

end

end GaloisForLFunctions.HTGeometry
