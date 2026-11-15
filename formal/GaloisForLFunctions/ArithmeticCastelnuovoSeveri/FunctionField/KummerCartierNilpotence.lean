import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularCyclicCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularCartierIterates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.DiagonalCharacterWeightDescent
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedAdditiveNilpotence

/-!
# Cartier nilpotence by strict cyclic character descent

Regular monomial weights increase under multiplication by `q^r`
modulo `N(q-1)`. Cartier's `q^r` scalar law and naturality reverse
those character edges. The corresponding Cartier block therefore
strictly lowers every nonzero coefficient weight, and finitely many
blocks annihilate the actual global regular differential space.

The argument uses the primitive roots already in the stated square
constant field and works for every nonzero branch coefficient.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "G" => globalRegularDifferentials K L
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "e" => (d + 1) * r

/-- The Cartier block extracting `q^r`th scalar roots strictly descends full cyclic character weights. -/
theorem primePowerKummerRegularCartier_block_nilpotent (ω : G) :
    (squareKummerRegularCartierIterate p s c d r e : G → G)^[M] ω = 0 := by
  classical
  let A := p ^ e
  let B := squareKummerRegularMonomialBasis p s c d r
  let weight := squareKummerRegularWeight p s d r
  let T := squareKummerRegularCartierIterate p s c d r e
  have hM : 0 < M := primePowerKummerCyclicDegree_pos p d n
  obtain ⟨ζ, hζ'⟩ := squareConstantField_threePoint_primitiveRoots p d n
  have hζ : IsPrimitiveRoot ζ M := (mem_primitiveRoots hM).mp hζ'
  have hroot : (ζ ^ A) ^ M = 1 := by
    calc
      (ζ ^ A) ^ M = ζ ^ (A * M) := (pow_mul ζ A M).symm
      _ = ζ ^ (M * A) := congrArg (fun j : ℕ => ζ ^ j) (Nat.mul_comm A M)
      _ = (ζ ^ M) ^ A := pow_mul ζ M A
      _ = 1 := by rw [hζ.pow_eq_one, one_pow]
  let S := squareKummerRegularScaling p s c d r (ζ ^ A) hroot
  have hdiag (i : SquareKummerRegularIndex p s d r) :
      S (B i) = ζ ^ (A * weight i) • B i := by
    calc
      S (B i) = (ζ ^ A) ^ weight i • B i :=
        squareKummerRegularScaling_basis p s c d r (ζ ^ A) hroot i
      _ = _ := congrArg (fun a : K => a • B i) (pow_mul ζ A (weight i)).symm
  have hbound (i : SquareKummerRegularIndex p s d r) : weight i < M :=
    (squareKummerRegularWeight_bounds p s d r i).2
  have hrise (i : SquareKummerRegularIndex p s d r) :
      weight i < (A * weight i) % M := by
    have hA : A = (p ^ (d + 1)) ^ r := pow_mul p (d + 1) r
    rw [hA]
    exact squareKummerRegularWeight_frobenius_rise p s d r i
  have himage (j : SquareKummerRegularIndex p s d r) :
      S (T (B j)) = ζ ^ weight j • T (B j) := by
    calc
      S (T (B j)) = T (S (B j)) :=
        squareKummerRegularCartierIterate_aut p s c d r e
          (squareKummerCyclicScalingAut p s c d r (ζ ^ A) hroot) (B j)
      _ = T ((ζ ^ weight j) ^ A • B j) := by
        have hpower : ζ ^ (A * weight j) = (ζ ^ weight j) ^ A :=
          (congrArg (fun k : ℕ => ζ ^ k) (Nat.mul_comm A (weight j))).trans
            (pow_mul ζ (weight j) A)
        rw [hdiag, hpower]
      _ = ζ ^ weight j • T (B j) :=
        squareKummerRegularCartierIterate_frobenius_smul p s c d r e (ζ ^ weight j) (B j)
  have hlower (j i : SquareKummerRegularIndex p s d r) (hji : weight j ≤ weight i) :
      B.repr (T (B j)) i = 0 :=
    diagonal_character_weight_descent B S.toLinearMap M A hM ζ hζ weight hdiag hrise
      (T (B j)) (weight j) (hbound j) (himage j) i hji
  exact additive_basis_weight_descent_nilpotent B T weight
    (squareKummerRegularCartierIterate_scalar_line p s c d r e) hlower M hbound ω

/-- An explicit Cartier iterate annihilates every intrinsic global regular differential. -/
theorem primePowerKummerCartier_iterate_eq_zero (ω : G) :
    squareKummerCartierIterate p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
      (e * M) ω.val = 0 := by
  have h := congrArg Subtype.val (primePowerKummerRegularCartier_block_nilpotent p d n r c ω)
  rw [squareKummerRegularCartierIterate_iterate] at h
  exact h

/-- The canonical Cartier endomorphism of actual global regular differentials is nilpotent. -/
theorem primePowerKummerRegularCartier_nilpotent (ω : G) :
    (squareKummerRegularCartier p s c d r : G → G)^[e * M] ω = 0 := by
  apply Subtype.ext
  have h := squareKummerRegularCartierIterate_iterate p s c d r 1 (e * M) ω
  rw [one_mul, primePowerKummerCartier_iterate_eq_zero p d n r c ω] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
