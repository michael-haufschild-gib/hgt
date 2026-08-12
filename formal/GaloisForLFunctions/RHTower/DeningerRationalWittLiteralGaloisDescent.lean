import GaloisForLFunctions.RHTower.DeningerRationalWittAlgebraicallyClosedRing
import GaloisForLFunctions.RHTower.DeningerRationalWittGaloisFixedDescent

/-!
# Literal rational-Witt Galois/Frobenius descent over the prime-field closure

The earlier fixed-point theorem lived only on the complexified monoid-algebra presentation.  This
module first proves the integral theorem on `ℤ[(AlgebraicClosure 𝔽_p)ˣ]`, then conjugates it through
the literal rational-Witt ring equivalence.  The final theorem is therefore a statement about
actual normalized rational functions with Witt multiplication.

It proves that arithmetic-Frobenius invariance is exactly absolute-Galois invariance.  The
subsequent `DeningerRationalWittBaseFieldDescent` module identifies that fixed ring with the image
of literal `W_rat(𝔽_p)`.
-/

namespace RHTower

noncomputable section

/-- Absolute Galois action on the integral reduced monoid algebra. -/
noncomputable def deningerPrimeIntegralRationalWittGaloisAction
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p) :
    MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ ≃+*
      MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ :=
  (MonoidAlgebra.domCongr ℤ ℤ
    (Units.mapEquiv g.toRingEquiv.toMulEquiv)).toRingEquiv

@[simp] theorem deningerPrimeIntegralRationalWittGaloisAction_single
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (x : (DeningerPrimeArithmeticClosure p)ˣ) (c : ℤ) :
    deningerPrimeIntegralRationalWittGaloisAction p g
        (MonoidAlgebra.single x c) =
      MonoidAlgebra.single
        (Units.mapEquiv g.toRingEquiv.toMulEquiv x) c := by
  simp [deningerPrimeIntegralRationalWittGaloisAction]

theorem deningerPrimeIntegralRationalWittGaloisAction_atomSum
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (s : Multiset (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimeIntegralRationalWittGaloisAction p g
        (deningerRationalWittAtomSum s) =
      deningerRationalWittAtomSum
        (s.map (Units.mapEquiv g.toRingEquiv.toMulEquiv)) := by
  induction s using Multiset.induction_on with
  | empty => simp [deningerRationalWittAtomSum]
  | @cons a s ih =>
      rw [show deningerRationalWittAtomSum (a ::ₘ s) =
        MonoidAlgebra.single a 1 + deningerRationalWittAtomSum s by
          simp [deningerRationalWittAtomSum]]
      rw [map_add, deningerPrimeIntegralRationalWittGaloisAction_single, ih]
      simp [deningerRationalWittAtomSum]

theorem deningerPrimeIntegralRationalWittGaloisAction_mul_apply
    (p : Nat.Primes) (g h : DeningerPrimeArithmeticGalois p)
    (w : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimeIntegralRationalWittGaloisAction p (g * h) w =
      deningerPrimeIntegralRationalWittGaloisAction p g
        (deningerPrimeIntegralRationalWittGaloisAction p h w) := by
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add x c w _hx _hc ih =>
      simp only [map_add, ih,
        deningerPrimeIntegralRationalWittGaloisAction_single]
      congr 1

theorem deningerPrimeIntegralRationalWittGaloisAction_one_apply
    (p : Nat.Primes)
    (w : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimeIntegralRationalWittGaloisAction p 1 w = w := by
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add x c w _hx _hc ih =>
      simp only [map_add, ih,
        deningerPrimeIntegralRationalWittGaloisAction_single]
      congr 1

/-- Arithmetic Frobenius on the integral reduced monoid algebra. -/
noncomputable def deningerPrimeIntegralRationalWittFrobenius
    (p : Nat.Primes) :
    MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ ≃+*
      MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ :=
  deningerPrimeIntegralRationalWittGaloisAction p
    (deningerPrimeArithmeticFrobenius p)

theorem deningerPrimeIntegralRationalWittGaloisAction_frobeniusPow_fixed
    (p : Nat.Primes)
    (w : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ)
    (hw : deningerPrimeIntegralRationalWittFrobenius p w = w) :
    ∀ n : ℕ,
      deningerPrimeIntegralRationalWittGaloisAction p
          ((deningerPrimeArithmeticFrobenius p) ^ n) w = w := by
  change deningerPrimeIntegralRationalWittGaloisAction p
      (deningerPrimeArithmeticFrobenius p) w = w at hw
  intro n
  induction n with
  | zero =>
      exact deningerPrimeIntegralRationalWittGaloisAction_one_apply p w
  | succ n ih =>
      rw [pow_succ,
        deningerPrimeIntegralRationalWittGaloisAction_mul_apply]
      rw [hw, ih]

/-- Integral Frobenius fixed points are exactly absolute-Galois fixed points. -/
theorem deningerPrimeIntegralRationalWitt_frobenius_fixed_iff_galois_fixed
    (p : Nat.Primes)
    (w : MonoidAlgebra ℤ (DeningerPrimeArithmeticClosure p)ˣ) :
    deningerPrimeIntegralRationalWittFrobenius p w = w ↔
      ∀ g : DeningerPrimeArithmeticGalois p,
        deningerPrimeIntegralRationalWittGaloisAction p g w = w := by
  classical
  constructor
  · intro hw g
    obtain ⟨s, t, hst⟩ :=
      deningerRationalWitt_exists_atomSum_sub_atomSum w
    let u := (s + t).toFinset
    obtain ⟨n, hn⟩ :=
      deningerPrimeArithmeticGalois_exists_frobeniusPow_eq_on_finiteFamily p g
        (fun x : u => ((x.1 : (DeningerPrimeArithmeticClosure p)ˣ) :
          DeningerPrimeArithmeticClosure p))
    have hu : ∀ x : (DeningerPrimeArithmeticClosure p)ˣ,
        x ∈ s + t →
        Units.mapEquiv g.toRingEquiv.toMulEquiv x =
          Units.mapEquiv
            ((deningerPrimeArithmeticFrobenius p) ^ n).toRingEquiv.toMulEquiv x := by
      intro x hx
      apply Units.ext
      exact hn ⟨x, by simpa [u] using hx⟩
    have hs :
        deningerPrimeIntegralRationalWittGaloisAction p g
            (deningerRationalWittAtomSum s) =
          deningerPrimeIntegralRationalWittGaloisAction p
            ((deningerPrimeArithmeticFrobenius p) ^ n)
            (deningerRationalWittAtomSum s) := by
      rw [deningerPrimeIntegralRationalWittGaloisAction_atomSum,
        deningerPrimeIntegralRationalWittGaloisAction_atomSum]
      congr 1
      apply Multiset.map_congr rfl
      intro x hx
      exact hu x (by simp [hx])
    have ht :
        deningerPrimeIntegralRationalWittGaloisAction p g
            (deningerRationalWittAtomSum t) =
          deningerPrimeIntegralRationalWittGaloisAction p
            ((deningerPrimeArithmeticFrobenius p) ^ n)
            (deningerRationalWittAtomSum t) := by
      rw [deningerPrimeIntegralRationalWittGaloisAction_atomSum,
        deningerPrimeIntegralRationalWittGaloisAction_atomSum]
      congr 1
      apply Multiset.map_congr rfl
      intro x hx
      exact hu x (by simp [hx])
    calc
      deningerPrimeIntegralRationalWittGaloisAction p g w =
          deningerPrimeIntegralRationalWittGaloisAction p g
            (deningerRationalWittAtomSum s -
              deningerRationalWittAtomSum t) :=
        congrArg (deningerPrimeIntegralRationalWittGaloisAction p g) hst
      _ = deningerPrimeIntegralRationalWittGaloisAction p
          ((deningerPrimeArithmeticFrobenius p) ^ n)
          (deningerRationalWittAtomSum s -
            deningerRationalWittAtomSum t) := by
        rw [map_sub, map_sub, hs, ht]
      _ = deningerPrimeIntegralRationalWittGaloisAction p
          ((deningerPrimeArithmeticFrobenius p) ^ n) w :=
        congrArg _ hst.symm
      _ = w :=
        deningerPrimeIntegralRationalWittGaloisAction_frobeniusPow_fixed
          p w hw n
  · intro hw
    exact hw (deningerPrimeArithmeticFrobenius p)

/-- Absolute Galois action transported to the literal rational-Witt ring. -/
noncomputable def deningerPrimeLiteralRationalWittGaloisAction
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p) :
    DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) ≃+*
      DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) :=
  ((deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p).symm.trans
    (deningerPrimeIntegralRationalWittGaloisAction p g)).trans
      (deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p)

/-- Arithmetic Frobenius transported to the literal rational-Witt ring. -/
noncomputable def deningerPrimeLiteralRationalWittFrobenius
    (p : Nat.Primes) :
    DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) ≃+*
      DeningerRationalWittRing (DeningerPrimeArithmeticClosure p) :=
  deningerPrimeLiteralRationalWittGaloisAction p
    (deningerPrimeArithmeticFrobenius p)

/-- Literal rational-Witt Frobenius invariance is equivalent to absolute-Galois invariance. -/
theorem deningerPrimeLiteralRationalWitt_frobenius_fixed_iff_galois_fixed
    (p : Nat.Primes)
    (w : DeningerRationalWittRing (DeningerPrimeArithmeticClosure p)) :
    deningerPrimeLiteralRationalWittFrobenius p w = w ↔
      ∀ g : DeningerPrimeArithmeticGalois p,
        deningerPrimeLiteralRationalWittGaloisAction p g w = w := by
  constructor
  · intro hw
    have hw' := congrArg
      (deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p).symm hw
    simp [deningerPrimeLiteralRationalWittFrobenius,
      deningerPrimeLiteralRationalWittGaloisAction] at hw'
    intro g
    apply (deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p).symm.injective
    simp [deningerPrimeLiteralRationalWittGaloisAction]
    exact (deningerPrimeIntegralRationalWitt_frobenius_fixed_iff_galois_fixed
      p _).mp hw' g
  · intro hw
    apply (deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p).symm.injective
    simp [deningerPrimeLiteralRationalWittFrobenius,
      deningerPrimeLiteralRationalWittGaloisAction]
    apply (deningerPrimeIntegralRationalWitt_frobenius_fixed_iff_galois_fixed
      p _).mpr
    intro g
    have hg := hw g
    have hg' := congrArg
      (deningerPrimeRationalWittReducedMonoidAlgebraRingEquiv p).symm hg
    simpa [deningerPrimeLiteralRationalWittGaloisAction] using hg'

end

end RHTower
