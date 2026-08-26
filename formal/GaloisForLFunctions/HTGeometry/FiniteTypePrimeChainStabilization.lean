import GaloisForLFunctions.HTGeometry.NoetherNormalizationKrullDim

/-!
# Stabilization of prime chains in finite-type algebras

Finite Krull dimension rules out an infinite strictly descending chain of prime ideals.  This file
packages that consequence in the sequence form used by iterated algebraic images.
-/

namespace GaloisForLFunctions.HTGeometry

open Order

/-- Every antitone sequence of prime ideals in a finite-type algebra over a field has two equal
consecutive terms. -/
theorem exists_eq_succ_of_antitone_prime
    {k R : Type*} [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R]
    (P : ℕ → Ideal R) (hprime : ∀ m, (P m).IsPrime)
    (hanti : Antitone P) :
    ∃ m, P (m + 1) = P m := by
  obtain ⟨s, hdim⟩ := exists_ringKrullDim_eq_of_finiteType k R
  by_contra hnone
  push Not at hnone
  have hlt (m : ℕ) : P (m + 1) < P m :=
    lt_of_le_of_ne (hanti (Nat.le_succ m)) (hnone m)
  let l : LTSeries (PrimeSpectrum R) :=
    { length := s + 1
      toFun := fun i => ⟨P (s + 1 - i.val), hprime _⟩
      step := fun i => by
        change P (s + 1 - i.val) < P (s + 1 - (i.val + 1))
        have hi := i.isLt
        have hleft : s + 1 - i.val = (s - i.val) + 1 := by omega
        have hright : s + 1 - (i.val + 1) = s - i.val := by omega
        rw [hleft, hright]
        exact hlt (s - i.val) }
  have hle := LTSeries.length_le_krullDim l
  change (l.length : WithBot ℕ∞) ≤ ringKrullDim R at hle
  rw [hdim] at hle
  have hnat : s + 1 ≤ s := by
    exact_mod_cast (show ((s + 1 : ℕ) : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) by
      simpa [l] using hle)
  omega

end GaloisForLFunctions.HTGeometry
