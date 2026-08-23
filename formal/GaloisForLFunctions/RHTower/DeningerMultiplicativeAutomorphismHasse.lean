import GaloisForLFunctions.RHTower.DeningerPrimeMultiplicativeAutomorphismComparison

/-!
# Hasse descent for multiplicative automorphisms

Full multiplicative automorphisms of the arithmetic closure units are determined on every finite
away-prime cyclotomic stage.  Conversely, a compatible family of finite-stage automorphisms glues
to one unique global multiplicative automorphism.
-/

namespace RHTower

noncomputable section

/-- Two global multiplicative automorphisms agree exactly when all finite cyclotomic-stage
restrictions agree. -/
theorem deningerPrimeArithmeticMulAutTower_congr_hasse_iff
    (p : Nat.Primes) (f g : DeningerPrimeArithmeticMulAut p) :
    (∀ (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ),
      (deningerPrimeArithmeticMulAutTowerRestriction p f).val l k =
        (deningerPrimeArithmeticMulAutTowerRestriction p g).val l k) ↔ f = g := by
  constructor
  · intro h
    apply deningerPrimeArithmeticMulAutTowerRestriction_injective p
    apply Subtype.ext
    funext l k
    exact h l k
  · rintro rfl l k
    rfl

/-- Every compatible family of finite cyclotomic-stage automorphisms glues to one unique full
automorphism of the arithmetic closure units. -/
theorem deningerCompatibleCyclotomicTower_existsUnique_arithmeticMulAut_hasse
    (p : Nat.Primes) (A : DeningerPrimeCompatibleCyclotomicTowerAut p) :
    ∃! f : DeningerPrimeArithmeticMulAut p,
      ∀ (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)}) (k : ℕ),
        (deningerPrimeArithmeticMulAutTowerRestriction p f).val l k = A.val l k := by
  refine ⟨deningerPrimeMulAut_compatibleTowerMulAut p A, ?_, ?_⟩
  · intro l k
    have h := deningerPrimeArithmeticMulAutTowerRestriction_rightInverse p A
    exact congrFun (congrFun (congrArg Subtype.val h) l) k
  · intro f hf
    apply deningerPrimeArithmeticMulAutTowerRestriction_injective p
    rw [deningerPrimeArithmeticMulAutTowerRestriction_rightInverse p A]
    apply Subtype.ext
    funext l k
    exact hf l k

end


end RHTower
