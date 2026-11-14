import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerOrdinateReconstruction
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.RelationFiberCover

/-!
# Exact affine point counts for the Kummer family

The trace and signed constructions exhaust the nonzero soluble fibers.
Each contributes the norm degree, and every branch zero contributes one
point. Thus the previously constructed lower bound is the exact number
of solutions of the literal affine equation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

variable (p : ℕ) [Fact p.Prime]

/-- The explicit parameters biject with all nonzero soluble ordinates. -/
def kummerConstructedOrdinateEquiv (s d r : ℕ) :
    KummerOrdinateParameters p s d r ≃
      {y : SquareConstantField p s // (normalizedKummerBranch p s d r).eval y ≠ 0 ∧
        ((normalizedKummerBranch p s d r).eval y) ^ p ^ (s + 1) =
          (normalizedKummerBranch p s d r).eval y} :=
  Equiv.ofBijective
    (fun i => ⟨kummerConstructedOrdinate p s d r i,
      kummerConstructedOrdinate_branch_ne_zero p s d r i,
      kummerConstructedOrdinate_branch_fixed p s d r i⟩)
    ⟨fun i j h => kummerConstructedOrdinate_injective p s d r (congrArg Subtype.val h),
      fun y => by
        obtain ⟨i, hi⟩ := (exists_kummerConstructedOrdinate_iff p s d r y.val).mpr y.property
        exact ⟨i, Subtype.ext hi⟩⟩

/-- Every affine point is counted exactly once by a full norm fiber or the zero section. -/
theorem normalizedKummer_affine_card (s d r : ℕ) :
    Nat.card (NormalizedKummerAffinePoints p s d r) =
      Nat.card (KummerOrdinateParameters p s d r) * (p ^ (s + 1) + 1) +
        p ^ Nat.gcd (2 * (s + 1)) (d + 1) := by
  apply Nat.le_antisymm
  · have hc := card_relation_upper_bound_add_section
      (fun y z : SquareConstantField p s =>
        z ^ (p ^ (s + 1) + 1) = (normalizedKummerBranch p s d r).eval y)
      (kummerConstructedOrdinate p s d r)
      (fun y : KummerAuxiliaryField p s (d + 1) => y.val)
      (fun _ => 0) (fun y => by
        rw [zero_pow (Nat.succ_ne_zero _),
          (normalizedKummerBranch_eq_zero_iff p s d r y.val).mpr y.property])
      (fun y z hyz => by
        rcases (normalizedKummer_soluble_ordinate_iff p s d r y).mp ⟨z, hyz⟩ with hy | hi
        · right
          refine ⟨⟨y, hy⟩, rfl, ?_⟩
          have hz : z ^ (p ^ (s + 1) + 1) = 0 :=
            hyz.trans ((normalizedKummerBranch_eq_zero_iff p s d r y).mpr hy)
          exact ((pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hz).symm
        · exact Or.inl hi)
      (p ^ (s + 1) + 1) (kummerConstructedOrdinate_fiber_card p s d r)
    rw [kummerAuxiliaryField_card] at hc
    exact hc
  · exact normalizedKummer_affine_card_lower_bound_with_zeros p s d r

/-- The exact affine count contains only prime powers and the branch-multiplicity gcd. -/
theorem normalizedKummer_primePower_affine_card (d n r : ℕ) :
    Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) =
      (p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
        (p ^ (d + 1) - 1) *
          Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1))) *
        (p ^ (kummerSquareIndex d n + 1) + 1) + p ^ (d + 1) := by
  have hd : d + 1 ∣ 2 * (kummerSquareIndex d n + 1) := by
    apply dvd_mul_of_dvd_right
    rw [kummerSquareIndex_succ]
    exact dvd_mul_right _ _
  rw [normalizedKummer_affine_card, kummerOrdinateParameters_primePower_card, Nat.gcd_eq_right hd]

/-- The number of all nonzero soluble ordinates is the same explicit gcd expression. -/
theorem normalizedKummer_primePower_nonzero_ordinate_card (d n r : ℕ) :
    Nat.card {y : SquareConstantField p (kummerSquareIndex d n) //
      (normalizedKummerBranch p (kummerSquareIndex d n) d r).eval y ≠ 0 ∧
      ((normalizedKummerBranch p (kummerSquareIndex d n) d r).eval y) ^
        p ^ (kummerSquareIndex d n + 1) =
        (normalizedKummerBranch p (kummerSquareIndex d n) d r).eval y} =
      p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
        (p ^ (d + 1) - 1) *
          Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
            (kummerExponent (p ^ (d + 1)) (r + 1)) := by
  rw [← Nat.card_congr (kummerConstructedOrdinateEquiv p (kummerSquareIndex d n) d r),
    kummerOrdinateParameters_primePower_card]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
