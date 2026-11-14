import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerRamificationCorrection
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.RelationFiberCounts

/-!
# Zero fibers of the normalized Kummer equation

The branch polynomial vanishes exactly on the small Frobenius fixed field.
These ordinates supply the section `z=0`, disjoint from both nonzero norm
families. Counting this section strengthens the affine lower bound by the
full number of branch zeros.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

variable (p : ℕ) [Fact p.Prime]

/-- The branch zeros are precisely the elements fixed by the small Frobenius. -/
theorem normalizedKummerBranch_eq_zero_iff (s d r : ℕ) (y : SquareConstantField p s) :
    (normalizedKummerBranch p s d r).eval y = 0 ↔ y ^ p ^ (d + 1) = y := by
  constructor
  · intro hy
    by_contra hn
    exact normalizedKummerBranch_ne_zero_of_not_fixed p s d r y hn hy
  · intro hy
    rw [normalizedKummerBranch_eval]
    by_cases hy0 : y = 0
    · rw [hy0, mul_zero, zero_mul]
    · have hpow : y ^ (p ^ (d + 1) - 1) = 1 := by
        apply mul_right_cancel₀ hy0
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos),
          one_mul, hy]
      have hR : kummerExponent (p ^ (d + 1)) (r + 1) ≠ 0 := by
        rw [kummerExponent, geom_sum_succ]
        omega
      rw [hpow, sub_self, zero_pow hR, mul_zero]

/-- The zero locus is the actual small Frobenius fixed field inside the constants. -/
def kummerBranchZeroEquiv (s d r : ℕ) :
    {y : SquareConstantField p s // (normalizedKummerBranch p s d r).eval y = 0} ≃
      KummerAuxiliaryField p s (d + 1) where
  toFun y := ⟨y.val, (normalizedKummerBranch_eq_zero_iff p s d r y.val).mp y.property⟩
  invFun y := ⟨y.val, (normalizedKummerBranch_eq_zero_iff p s d r y.val).mpr y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of affine branch zeros is a fixed-field gcd count. -/
theorem normalizedKummerBranch_zero_card (s d r : ℕ) :
    Nat.card {y : SquareConstantField p s // (normalizedKummerBranch p s d r).eval y = 0} =
      p ^ Nat.gcd (2 * (s + 1)) (d + 1) := by
  rw [Nat.card_congr (kummerBranchZeroEquiv p s d r), kummerAuxiliaryField_card]

/-- Every ordinate in either nonzero family has the full norm-fiber size. -/
theorem kummerConstructedOrdinate_fiber_card (s d r : ℕ) (i : KummerOrdinateParameters p s d r) :
    Nat.card {z : SquareConstantField p s |
      z ^ (p ^ (s + 1) + 1) =
        (normalizedKummerBranch p s d r).eval (kummerConstructedOrdinate p s d r i)} =
      p ^ (s + 1) + 1 := by
  cases i with
  | inl x => exact kummerTraceFamilyPoint_fiber_card p s d r x.1 x.2
  | inr x => exact kummerSignedParameter_fiber_card p s d r x

/-- The two constructed norm families avoid the branch-zero section. -/
theorem kummerConstructedOrdinate_branch_ne_zero (s d r : ℕ) (i : KummerOrdinateParameters p s d r) :
    (normalizedKummerBranch p s d r).eval (kummerConstructedOrdinate p s d r i) ≠ 0 := by
  intro hz
  have hc := kummerConstructedOrdinate_fiber_card p s d r i
  rw [squareConstantField_norm_fiber_card, if_pos hz] at hc
  have hp := Nat.one_le_pow (s + 1) p (Fact.out : p.Prime).pos
  omega

/-- Adding all branch zeros strengthens the two-family affine count. -/
theorem normalizedKummer_affine_card_lower_bound_with_zeros (s d r : ℕ) :
    Nat.card (KummerOrdinateParameters p s d r) * (p ^ (s + 1) + 1) +
      p ^ Nat.gcd (2 * (s + 1)) (d + 1) ≤
        Nat.card (NormalizedKummerAffinePoints p s d r) := by
  have hc := card_relation_lower_bound_add_section
    (fun y z : SquareConstantField p s =>
      z ^ (p ^ (s + 1) + 1) = (normalizedKummerBranch p s d r).eval y)
    (kummerConstructedOrdinate p s d r)
    (fun y : KummerAuxiliaryField p s (d + 1) => y.val)
    (kummerConstructedOrdinate_injective p s d r) Subtype.val_injective
    (fun i y h => kummerConstructedOrdinate_branch_ne_zero p s d r i (by
      rw [h]
      exact (normalizedKummerBranch_eq_zero_iff p s d r y.val).mpr y.property))
    (fun _ => 0) (fun y => by
      rw [zero_pow (Nat.succ_ne_zero _),
        (normalizedKummerBranch_eq_zero_iff p s d r y.val).mpr y.property])
    (p ^ (s + 1) + 1) (kummerConstructedOrdinate_fiber_card p s d r)
  rw [kummerAuxiliaryField_card] at hc
  exact hc

/-- The prime-power family has at least the two full norm families plus all `q` zero points. -/
theorem normalizedKummer_primePower_affine_card_lower_bound_with_zeros (d n r : ℕ) :
    (p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
      (p ^ (d + 1) - 1) *
        Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
          (kummerExponent (p ^ (d + 1)) (r + 1))) *
      (p ^ (kummerSquareIndex d n + 1) + 1) + p ^ (d + 1) ≤
        Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) := by
  have hd : d + 1 ∣ 2 * (kummerSquareIndex d n + 1) := by
    apply dvd_mul_of_dvd_right
    rw [kummerSquareIndex_succ]
    exact dvd_mul_right _ _
  have hc := normalizedKummer_affine_card_lower_bound_with_zeros p (kummerSquareIndex d n) d r
  rwa [kummerOrdinateParameters_primePower_card, Nat.gcd_eq_right hd] at hc

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
