import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointModel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality


/-!
# Cyclicity of the three-point cover

The degree `(Q+1)(q-1)` divides the constant multiplicative group order.
The three-point radical extension is therefore cyclic Galois, with
relative automorphism group of exactly this order.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)

/-- Degree of the three-point cyclic presentation of the prime-power Kummer family. -/
def primePowerKummerCyclicDegree : ℕ :=
  (p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 1)

/-- The three-point covering degree is positive. -/
theorem primePowerKummerCyclicDegree_pos : 0 < primePowerKummerCyclicDegree p d n :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt))

/-- The full three-point covering degree divides the constant multiplicative group order. -/
theorem primePowerKummerCyclicDegree_dvd :
    primePowerKummerCyclicDegree p d n ∣ Nat.card (SquareConstantField p (kummerSquareIndex d n)) - 1 := by
  let q := p ^ (d + 1)
  let Q := p ^ (kummerSquareIndex d n + 1)
  have hQ : Q = q ^ (n + 1) := by
    dsimp only [q, Q]
    rw [kummerSquareIndex_succ, pow_mul]
  have hsmall : q - 1 ∣ Q - 1 := by
    rw [hQ]
    exact Nat.sub_one_dvd_pow_sub_one q (n + 1)
  have hQpos : 1 ≤ Q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hQsub := Nat.sub_add_cancel hQpos
  have hfactor : Nat.card (SquareConstantField p (kummerSquareIndex d n)) - 1 = (Q + 1) * (Q - 1) := by
    rw [squareConstantField_card, Nat.mul_comm 2 (kummerSquareIndex d n + 1), pow_mul, pow_two]
    change Q * Q - 1 = (Q + 1) * (Q - 1)
    have h : (Q + 1) * (Q - 1) + 1 = Q * Q := by nlinarith only [hQsub]
    omega
  rw [hfactor]
  exact Nat.mul_dvd_mul_left (Q + 1) hsmall

/-- The constants contain primitive roots of the full three-point covering degree. -/
theorem squareConstantField_threePoint_primitiveRoots :
    (primitiveRoots (primePowerKummerCyclicDegree p d n)
      (SquareConstantField p (kummerSquareIndex d n))).Nonempty := by
  classical
  let K := SquareConstantField p (kummerSquareIndex d n)
  let M := primePowerKummerCyclicDegree p d n
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hprim : IsPrimitiveRoot (g : K) (Nat.card Kˣ) := by
    rw [← hg]
    exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf g)
  obtain ⟨k, hk⟩ := primePowerKummerCyclicDegree_dvd p d n
  have hfactor : Nat.card Kˣ = k * M := by rw [Nat.card_units, hk, Nat.mul_comm]
  exact ⟨(g : K) ^ k, (mem_primitiveRoots (primePowerKummerCyclicDegree_pos p d n)).mpr
    (hprim.pow Nat.card_pos hfactor)⟩

/-- The three-point index agrees with `(Q+1)(q-1)`. -/
theorem primePowerKummer_threePoint_index :
    (p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1 + 1 =
      primePowerKummerCyclicDegree p d n := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]
  exact Nat.sub_add_cancel (primePowerKummerCyclicDegree_pos p d n)

private theorem threePoint_rational_primitiveRoots :
    (primitiveRoots
      ((p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1 + 1)
      (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])).Nonempty := by
  rw [primePowerKummer_threePoint_index]
  obtain ⟨ζ, hζ⟩ := squareConstantField_threePoint_primitiveRoots p d n
  let f := algebraMap (SquareConstantField p (kummerSquareIndex d n))
    (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
  exact ⟨f ζ, (mem_primitiveRoots (primePowerKummerCyclicDegree_pos p d n)).mpr
    (((mem_primitiveRoots (primePowerKummerCyclicDegree_pos p d n)).mp hζ).map_of_injective f.injective)⟩

/-- The three-point presentation of the prime-power family is a Galois extension. -/
theorem primePowerKummerThreePoint_isGalois
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) (R : ℕ) :
    IsGalois (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
      (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))) := by
  have hi := kummerBranch_fraction_irreducible (c ^ (p ^ (d + 1) - 2 + 1)) 0
    (R * (p ^ (d + 1) - 2 + 1))
    ((p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1)
  letI : IsSplittingField
      (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
      (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1)))
      (X ^ ((p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1 + 1) -
        C (algebraMap (SquareConstantField p (kummerSquareIndex d n))[X]
          (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
          (kummerBranch (c ^ (p ^ (d + 1) - 2 + 1)) 0 (R * (p ^ (d + 1) - 2 + 1))))) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C (threePoint_rational_primitiveRoots p d n) hi
  exact isGalois_of_isSplittingField_X_pow_sub_C (threePoint_rational_primitiveRoots p d n) hi _

/-- The three-point relative automorphism group is cyclic. -/
theorem primePowerKummerThreePoint_isCyclic
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) (R : ℕ) :
    IsCyclic (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))
      ≃ₐ[FractionRing (SquareConstantField p (kummerSquareIndex d n))[X]]
        KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))) := by
  have hi := kummerBranch_fraction_irreducible (c ^ (p ^ (d + 1) - 2 + 1)) 0
    (R * (p ^ (d + 1) - 2 + 1))
    ((p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1)
  letI : IsSplittingField
      (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
      (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1)))
      (X ^ ((p ^ (kummerSquareIndex d n + 1) + 1) * (p ^ (d + 1) - 2 + 1) - 1 + 1) -
        C (algebraMap (SquareConstantField p (kummerSquareIndex d n))[X]
          (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
          (kummerBranch (c ^ (p ^ (d + 1) - 2 + 1)) 0 (R * (p ^ (d + 1) - 2 + 1))))) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C (threePoint_rational_primitiveRoots p d n) hi
  exact isCyclic_of_isSplittingField_X_pow_sub_C (threePoint_rational_primitiveRoots p d n) hi _

/-- The three-point automorphism group has exactly `(Q+1)(q-1)` elements. -/
theorem primePowerKummerThreePoint_card_aut
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) (R : ℕ) :
    Nat.card (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))
      ≃ₐ[FractionRing (SquareConstantField p (kummerSquareIndex d n))[X]]
        KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))) =
      primePowerKummerCyclicDegree p d n := by
  letI : FiniteDimensional (FractionRing (SquareConstantField p (kummerSquareIndex d n))[X])
      (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))) :=
    (monic_X_pow_sub_C _ (Nat.succ_ne_zero _)).finite_adjoinRoot
  letI := primePowerKummerThreePoint_isGalois p d n c R
  rw [IsGalois.card_aut_eq_finrank, kummerBranchField_finrank, primePowerKummer_threePoint_index]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
