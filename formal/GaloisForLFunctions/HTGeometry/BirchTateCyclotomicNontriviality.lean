import GaloisForLFunctions.HTGeometry.BirchTateWTwop
import GaloisForLFunctions.HTGeometry.BirchTateCyclotomicImage
import GaloisForLFunctions.HTGeometry.BirchTateDegreeGrowth
import GaloisForLFunctions.HTGeometry.PrimeCyclotomicFieldEscape
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Nontriviality of the squared cyclotomic character

For every number field and every rational prime, some absolute Galois element has nontrivial
square under the p-adic cyclotomic character. If every square were trivial, the conjugates of a
primitive root of order `p ^ (n + 3)` would inject into the square-one units modulo that order.
There are at most four such units, while rational cyclotomic degrees grow without bound.
-/

namespace GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F]

/-- Vanishing of `χ_p(g)^(2 : ℕ) - 1` places every finite cyclotomic reduction of `g` in the
square-one kernel. -/
theorem modularCyclotomicCharacter_mem_squareOneKernel_of_cyclotomicSquare_eq_zero
    (g : Field.absoluteGaloisGroup F)
    (hg : cyclotomicSquareMinusOne p F g = 0) (n : ℕ) :
    modularCyclotomicCharacter (AlgebraicClosure F)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity
          (AlgebraicClosure F) (p ^ n)) g.toRingEquiv ∈
      (powMonoidHom 2 : (ZMod (p ^ n))ˣ →* (ZMod (p ^ n))ˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  have hchar :
      (((cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv) ^ 2 :
        (ℤ_[p])ˣ) : ℤ_[p]) = 1 := by
    exact sub_eq_zero.mp hg
  have hmod := congrArg (PadicInt.toZModPow n) hchar
  simpa [map_pow, cyclotomicCharacter.toZModPow] using hmod

/-- If every squared cyclotomic value is trivial, every primitive `p ^ (n + 3)` root has
minimal-polynomial degree at most four over the number field. -/
theorem minpoly_natDegree_le_four_of_cyclotomicSquare_eq_zero
    (n : ℕ) (ζ : AlgebraicClosure F)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 3)))
    (hall : ∀ g : Field.absoluteGaloisGroup F,
      cyclotomicSquareMinusOne p F g = 0) :
    (minpoly F ζ).natDegree ≤ 4 := by
  let roots := (minpoly F ζ).rootSet (AlgebraicClosure F)
  let σ : ∀ y : roots, Field.absoluteGaloisGroup F := fun y =>
    Classical.choose (minpoly.exists_algEquiv_of_root'
      (K := F) (L := AlgebraicClosure F)
      (Algebra.IsAlgebraic.isAlgebraic ζ)
      ((Polynomial.mem_rootSet.mp y.2).2))
  have hσ (y : roots) : (σ y).toRingEquiv ζ = y.1 :=
    Classical.choose_spec (minpoly.exists_algEquiv_of_root'
      (K := F) (L := AlgebraicClosure F)
      (Algebra.IsAlgebraic.isAlgebraic ζ)
      ((Polynomial.mem_rootSet.mp y.2).2))
  let sq : (ZMod (p ^ (n + 3)))ˣ →* (ZMod (p ^ (n + 3)))ˣ := powMonoidHom 2
  let f : roots → sq.ker := fun y =>
    ⟨modularCyclotomicCharacter (AlgebraicClosure F)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity
          (AlgebraicClosure F) (p ^ (n + 3))) (σ y).toRingEquiv,
      modularCyclotomicCharacter_mem_squareOneKernel_of_cyclotomicSquare_eq_zero
        p F (σ y) (hall (σ y)) (n + 3)⟩
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hu :
        modularCyclotomicCharacter (AlgebraicClosure F)
            (HasEnoughRootsOfUnity.natCard_rootsOfUnity
              (AlgebraicClosure F) (p ^ (n + 3))) (σ y).toRingEquiv =
          modularCyclotomicCharacter (AlgebraicClosure F)
            (HasEnoughRootsOfUnity.natCard_rootsOfUnity
              (AlgebraicClosure F) (p ^ (n + 3))) (σ z).toRingEquiv := by
      exact congrArg Subtype.val hyz
    have hred :
        (cyclotomicCharacter (AlgebraicClosure F) p
            (σ y).toRingEquiv).val.toZModPow (n + 3) =
          (cyclotomicCharacter (AlgebraicClosure F) p
            (σ z).toRingEquiv).val.toZModPow (n + 3) := by
      rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
      exact congrArg Units.val hu
    have hspecy := cyclotomicCharacter.spec p (n := n + 3)
      (σ y).toRingEquiv ζ hζ.pow_eq_one
    have hspecz := cyclotomicCharacter.spec p (n := n + 3)
      (σ z).toRingEquiv ζ hζ.pow_eq_one
    exact (hσ y).symm.trans (hspecy.trans <|
      (congrArg (fun e : ZMod (p ^ (n + 3)) => ζ ^ e.val) hred).trans <|
        hspecz.symm.trans (hσ z))
  have hroot : Nat.card roots ≤ Nat.card sq.ker :=
    Nat.card_le_card_of_injective f hf
  have hker : Nat.card sq.ker ≤ 4 := by
    by_cases hp2 : p = 2
    · subst p
      exact card_squareOneUnits_twoPow_le_four n
    · exact (card_squareOneUnits_oddPrimePow_le_two p (n + 3)
        (Fact.out : p.Prime) hp2).trans (by omega)
  have hsplit :
      ((minpoly F ζ).map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits _
  have hcard := Polynomial.card_rootSet_eq_natDegree
    (PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral ζ))) hsplit
  rw [← hcard]
  simpa only [Nat.card_eq_fintype_card] using hroot.trans hker

/-- The square of the p-adic cyclotomic character is nontrivial on the absolute Galois group of
every number field. -/
theorem exists_cyclotomicSquare_ne_one :
    ∃ g : Field.absoluteGaloisGroup F,
      cyclotomicSquareMinusOne p F g ≠ 0 := by
  by_contra h
  push Not at h
  let d := Module.finrank ℚ F
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 4 * d < p ^ n :=
    pow_unbounded_of_one_lt (4 * d) (Fact.out : p.Prime).one_lt
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure F) (p ^ (n + 3))
  have hF : (minpoly F ζ).natDegree ≤ 4 :=
    minpoly_natDegree_le_four_of_cyclotomicSquare_eq_zero p F n ζ hζ h
  have hQ : (minpoly ℚ ζ).natDegree ≤ d * (minpoly F ζ).natDegree :=
    minpoly_natDegree_tower_lower_bound ζ (by
      letI : Algebra.IsIntegral ℚ F := Algebra.IsIntegral.of_finite ℚ F
      exact isIntegral_trans ζ (Algebra.IsIntegral.isIntegral (R := F) ζ))
  have htot : (p ^ (n + 3)).totient ≤ 4 * d := by
    rw [← minpoly_natDegree_of_isPrimitiveRoot
      (pow_pos (Fact.out : p.Prime).pos _) hζ]
    exact hQ.trans (by
      dsimp [d]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Module.finrank ℚ F) hF)
  have hpow : p ^ n ≤ p ^ (n + 2) * (p - 1) := by
    rw [show p ^ (n + 2) * (p - 1) = p ^ n * (p ^ 2 * (p - 1)) by ring]
    exact Nat.le_mul_of_pos_right _
      (Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _)
        (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
  have htotLower : p ^ n ≤ (p ^ (n + 3)).totient := by
    rw [Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)]
    simpa using hpow
  exact (Nat.not_lt_of_ge (htotLower.trans htot)) hn

/-- The p-primary Tate-twist fixed module of a number field is finite, unconditionally. -/
theorem finite_padicTateTwistTwoInvariants :
    Finite (padicTateTwistTwoInvariants p F) := by
  obtain ⟨g, hg⟩ := exists_cyclotomicSquare_ne_one p F
  exact finite_padicTateTwistTwoInvariants_of_cyclotomicSquare_ne_one p F g hg

/-- The p-primary contribution to `w₂(F)` is a power of `p`, unconditionally. -/
theorem wTwoPrimary_eq_prime_pow :
    ∃ k : ℕ, wTwoPrimary p F = p ^ k := by
  obtain ⟨g, hg⟩ := exists_cyclotomicSquare_ne_one p F
  obtain ⟨k, _, hk⟩ := wTwoPrimary_eq_prime_pow_of_cyclotomicSquare_ne_one p F g hg
  exact ⟨k, hk⟩

end GaloisForLFunctions.HTGeometry
