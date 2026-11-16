import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleSpaceCoordinates

/-!
# The one-point pole semigroup of a Kummer normalization

Reduced radical monomials realize the weights `i+(q-1)(iR mod N)`.
Multiplication by powers of the rational coordinate adds multiples of
`N`. Separation of character orders proves that these are all pole
orders of nonzero functions regular away from infinity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Every weighted radical monomial realizes its prescribed infinity pole order. -/
theorem squareKummer_exists_weighted_pole
    (i : Fin (p ^ (s + 1) + 1)) (k : ℕ) :
    ∃ x : SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r),
      IsIntegral (SquareConstantField p s)[X] x ∧
      squareKummerInfinityValuation p s c d r x =
        WithZero.exp (((p ^ (s + 1) + 1) * k +
          (i.val + (p ^ (d + 1) - 1) *
            (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) : ℕ) : ℤ) := by
  refine ⟨algebraMap (SquareConstantField p s)[X]
    (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) (X ^ k) *
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val, ?_, ?_⟩
  · exact isIntegral_algebraMap.mul (kummerIntegralMonomial_integral _ _ _ _ _)
  · simpa only [natDegree_X_pow] using
      squareKummerInfinityValuation_polynomialMonomial p s c d r (X ^ k)
        (pow_ne_zero k X_ne_zero) i

/-- Every nonzero polynomial expansion has the pole order of one of its nonzero characters. -/
theorem squareKummerPolynomialExpansion_pole_order
    (a : Fin (p ^ (s + 1) + 1) → (SquareConstantField p s)[X]) (m : ℕ)
    (ha : squareKummerInfinityValuation p s c d r (squareKummerPolynomialExpansion p s c d r a) =
      WithZero.exp (m : ℤ)) :
    ∃ i : Fin (p ^ (s + 1) + 1), a i ≠ 0 ∧
      (p ^ (s + 1) + 1) * (a i).natDegree +
        (i.val + (p ^ (d + 1) - 1) *
          (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) = m := by
  classical
  let S := Finset.univ.filter (fun i => a i ≠ 0)
  let w := fun i : Fin (p ^ (s + 1) + 1) =>
    (p ^ (s + 1) + 1) * (a i).natDegree +
      (i.val + (p ^ (d + 1) - 1) *
        (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)))
  have hS : S.Nonempty := by
    by_contra h
    have hz : ∀ i, a i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hx : squareKummerPolynomialExpansion p s c d r a = 0 := by
      simp only [squareKummerPolynomialExpansion, hz, map_zero, zero_mul, Finset.sum_const_zero]
    rw [hx, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S w hS
  have hj0 : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hup : w j ≤ m :=
    (squareKummerPolynomialExpansion_pole_bound_iff p s c d r a m).mp ha.le j hj0
  have hlo : m ≤ w j := by
    have hb : squareKummerInfinityValuation p s c d r (squareKummerPolynomialExpansion p s c d r a) ≤
        WithZero.exp (w j : ℤ) :=
      (squareKummerPolynomialExpansion_pole_bound_iff p s c d r a (w j)).mpr
        (fun i hi => hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
    rw [ha, WithZero.exp_le_exp] at hb
    exact_mod_cast hb
  exact ⟨j, hj0, le_antisymm hup hlo⟩

/-- The actual infinity pole semigroup is exactly the union of the reduced radical arithmetic progressions. -/
theorem squareKummer_exists_integral_pole_iff (m : ℕ) :
    (∃ x : SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r),
      IsIntegral (SquareConstantField p s)[X] x ∧
        squareKummerInfinityValuation p s c d r x = WithZero.exp (m : ℤ)) ↔
    ∃ i : Fin (p ^ (s + 1) + 1), ∃ k : ℕ,
      (p ^ (s + 1) + 1) * k +
        (i.val + (p ^ (d + 1) - 1) *
          (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) = m := by
  constructor
  · rintro ⟨x, hx, hv⟩
    let E := squareKummerNormalizationCoordinateEquiv p s d c (kummerExponent (p ^ (d + 1)) r)
    let a := E.symm ⟨x, hx⟩
    have ha : squareKummerPolynomialExpansion p s c d r a = x := by
      rw [← squareKummerNormalizationCoordinateEquiv_val]
      exact congrArg Subtype.val (E.apply_symm_apply ⟨x, hx⟩)
    obtain ⟨i, _, hi⟩ := squareKummerPolynomialExpansion_pole_order p s c d r a m
      (by rw [ha]; exact hv)
    exact ⟨i, (a i).natDegree, hi⟩
  · rintro ⟨i, k, rfl⟩
    exact squareKummer_exists_weighted_pole p s c d r i k

/-- Every attainable pole order has a unique reduced character and polynomial degree. -/
theorem squareKummer_exists_integral_pole_iff_unique (m : ℕ) :
    (∃ x : SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r),
      IsIntegral (SquareConstantField p s)[X] x ∧
        squareKummerInfinityValuation p s c d r x = WithZero.exp (m : ℤ)) ↔
    ∃! a : Fin (p ^ (s + 1) + 1) × ℕ,
      (p ^ (s + 1) + 1) * a.2 +
        (a.1.val + (p ^ (d + 1) - 1) *
          (a.1.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) = m := by
  rw [squareKummer_exists_integral_pole_iff]
  constructor
  · rintro ⟨i, k, h⟩
    refine ⟨(i, k), h, ?_⟩
    intro a ha
    exact (squareKummer_weightedPoleOrder_injective p s d r) (ha.trans h.symm)
  · rintro ⟨⟨i, k⟩, h, _⟩
    exact ⟨i, k, h⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
