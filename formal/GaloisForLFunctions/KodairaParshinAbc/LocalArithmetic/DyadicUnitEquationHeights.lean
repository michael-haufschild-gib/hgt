import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSpace
import Mathlib.NumberTheory.Height.NumberField

/-!
# Rank-one rational unit equations at unbounded height

The normalization in Ziegler, Theorem 1 (arXiv:2609.15487), is essential.
Two different solutions of 7x+3y=31 give two solutions at every dyadic
rescaling of 31. Even the odd targets 3·2^(n+1)+5 have solutions at
arbitrarily large height, which contradicts the bound in the abstract for
the real and dyadic places.
-/

noncomputable section
namespace GaloisForLFunctions.KodairaParshinAbc
open GaloisForLFunctions.RHTower IsDedekindDomain Height

/-- Ordered solutions in the actual rational S-unit group. -/
def RationalUnitSolutions (S : Finset (HeightOneSpectrum ℤ)) (a b c : ℚ) :=
  {z : fieldOneSUnitSubgroup S × fieldOneSUnitSubgroup S //
    a * (z.1.val : ℚ) + b * (z.2.val : ℚ) = c}

/-- Independent unit rescaling of the three coefficients preserves the entire solution fiber. -/
def rationalUnitSolutionsRescale (S : Finset (HeightOneSpectrum ℤ)) (a b c : ℚ)
    (u v w : fieldOneSUnitSubgroup S) :
    RationalUnitSolutions S a b c ≃
      RationalUnitSolutions S (a * (u.val : ℚ)) (b * (v.val : ℚ)) (c * (w.val : ℚ)) where
  toFun z := ⟨(z.val.1 * w / u, z.val.2 * w / v), by
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Units.val_div_eq_div_val, Units.val_mul]
    refine Eq.trans ?_ (congrArg (fun t : ℚ => t * (w.val : ℚ)) z.property)
    field_simp [u.val.ne_zero, v.val.ne_zero]⟩
  invFun z := ⟨(z.val.1 * u / w, z.val.2 * v / w), by
    simp only [Subgroup.coe_div, Subgroup.coe_mul, Units.val_div_eq_div_val, Units.val_mul]
    field_simp [w.val.ne_zero]
    linear_combination z.property⟩
  left_inv z := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> simp only [div_mul_cancel, mul_div_cancel_right]
  right_inv z := by apply Subtype.ext; apply Prod.ext <;> dsimp <;> simp only [div_mul_cancel, mul_div_cancel_right]

/-- The singleton finite place over 2, with the real place understood. -/
def dyadicUnitPlaces : Finset (HeightOneSpectrum ℤ) :=
  {Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩}

private def dyadicGenerator : fieldOneSUnitSubgroup dyadicUnitPlaces :=
  let v := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  ⟨fieldOneRationalPrimeUnit v, fieldOne_prime_mem_sUnitSubgroup _ ⟨v, Finset.mem_singleton_self _⟩⟩

private theorem dyadicGenerator_val : (dyadicGenerator.val : ℚ) = 2 := by
  simp [dyadicGenerator, fieldOneRationalPrimeUnit]

private theorem dyadicGenerator_pow_val (n : ℕ) : ((dyadicGenerator ^ n).val : ℚ) = 2 ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, dyadicGenerator_val]

/-- Every positive dyadic dilate of 31 admits two distinct ordered representations with coefficients 7,3. -/
theorem dyadic_two_solutions (n : ℕ) :
    ∃ x y : RationalUnitSolutions dyadicUnitPlaces 7 3 (31 * 2 ^ n), x ≠ y := by
  let t := dyadicGenerator ^ n
  have ht : (t.val : ℚ) = 2 ^ n := dyadicGenerator_pow_val n
  let x : RationalUnitSolutions dyadicUnitPlaces 7 3 (31 * 2 ^ n) :=
    ⟨(dyadicGenerator ^ 2 * t, t), by
      simp only [Subgroup.coe_mul, Units.val_mul, dyadicGenerator_pow_val, ht]
      ring⟩
  let y : RationalUnitSolutions dyadicUnitPlaces 7 3 (31 * 2 ^ n) :=
    ⟨(t, dyadicGenerator ^ 3 * t), by
      simp only [Subgroup.coe_mul, Units.val_mul, dyadicGenerator_pow_val, ht]
      ring⟩
  refine ⟨x, y, fun h => ?_⟩
  have he := congrArg (fun z : RationalUnitSolutions dyadicUnitPlaces 7 3 (31 * 2 ^ n) =>
    (z.val.1.val : ℚ)) h
  change (((dyadicGenerator ^ 2 * t).val : ℚ)) = (t.val : ℚ) at he
  rw [Subgroup.coe_mul, Units.val_mul, dyadicGenerator_pow_val] at he
  exact t.val.ne_zero (by linarith only [he])

/-- Odd targets admit positive solutions whose rational logarithmic heights tend to infinity. -/
theorem dyadic_odd_solvable_targets :
    ∀ B : ℝ, ∃ c : ℕ, Odd c ∧ B < logHeight₁ (c : ℚ) ∧
      Nonempty (RationalUnitSolutions dyadicUnitPlaces 3 5 (c : ℚ)) := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp B)
  let c := 3 * 2 ^ (n + 1) + 5
  have hc : 0 < c := by dsimp [c]; positivity
  letI : NeZero c := ⟨hc.ne'⟩
  refine ⟨c, ⟨3 * 2 ^ n + 2, by dsimp [c]; rw [pow_succ]; ring⟩, ?_, ?_⟩
  · rw [Rat.logHeight₁_natCast, ← Real.exp_lt_exp, Real.exp_log (by exact_mod_cast hc)]
    have hle : n ≤ c := by
      have hpow : n < 2 ^ n := Nat.lt_two_pow_self
      dsimp [c]
      rw [pow_succ]
      omega
    exact hn.trans_le (by exact_mod_cast hle)
  · refine ⟨⟨(dyadicGenerator ^ (n + 1), 1), ?_⟩⟩
    simp only [c, dyadicGenerator_pow_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Subgroup.coe_one, Units.val_one, mul_one]

/-- Two-solution fibers also occur at arbitrarily large raw Weil height. -/
theorem dyadic_unbounded_two_solution_height (B : ℝ) :
    ∃ c : ℕ, B < logHeight₁ (c : ℚ) ∧
      ∃ x y : RationalUnitSolutions dyadicUnitPlaces 7 3 (c : ℚ), x ≠ y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp B)
  let c : ℕ := 31 * 2 ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  letI : NeZero c := ⟨hc.ne'⟩
  refine ⟨c, ?_, ?_⟩
  · rw [Rat.logHeight₁_natCast, ← Real.exp_lt_exp, Real.exp_log (by exact_mod_cast hc)]
    have hle : n ≤ c := by have : n < 2 ^ n := Nat.lt_two_pow_self; dsimp [c]; omega
    exact hn.trans_le (by exact_mod_cast hle)
  · have he : (c : ℚ) = 31 * 2 ^ n := by simp [c]
    rw [he]
    exact dyadic_two_solutions n

#print axioms rationalUnitSolutionsRescale
#print axioms dyadic_two_solutions
#print axioms dyadic_odd_solvable_targets
#print axioms dyadic_unbounded_two_solution_height

end GaloisForLFunctions.KodairaParshinAbc
