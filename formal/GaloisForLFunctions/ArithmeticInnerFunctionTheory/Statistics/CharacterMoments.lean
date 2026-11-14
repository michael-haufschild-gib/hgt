import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheFixedBaseConeAndCriticalBernstein

/-!
# Exact fluctuations of Sato–Tate characters

Finite character expansions have diagonal covariance. The Clebsch–Gordan
product law turns fourth moments into counts of common irreducible summands.
These are the local moment identities used in the method of moments for
Frobenius, Hecke and Kloosterman statistics.
-/

open MeasureTheory Finset
open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

theorem integrable_cosSum_pow (m r : ℕ) :
    Integrable (fun θ => cosSum θ m ^ r) satoTate := by
  refine Integrable.of_bound ((continuous_cosSum m).pow r).aestronglyMeasurable
    (((m : ℝ) + 1) ^ r) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_cosSum_le θ m) r

theorem integrable_cosSum_mul (m n : ℕ) :
    Integrable (fun θ => cosSum θ m * cosSum θ n) satoTate := by
  refine Integrable.of_bound ((continuous_cosSum m).mul
    (continuous_cosSum n)).aestronglyMeasurable
    (((m : ℝ) + 1) * ((n : ℝ) + 1)) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_cosSum_le θ m) (abs_cosSum_le θ n)
    (abs_nonneg _) (by positivity)

/-- The constant character is the only character with nonzero mean. -/
theorem integral_cosSum (m : ℕ) :
    ∫ θ, cosSum θ m ∂satoTate = if m = 0 then 1 else 0 := by
  simpa only [cosSum_zero, mul_one] using integral_cosSum_mul_cosSum m 0

/-- A finite test function expanded in symmetric-power characters. -/
def characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ m ∈ s, a m * cosSum θ m

theorem integrable_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) :
    Integrable (characterPolynomial s a) satoTate := by
  exact integrable_finsetSum _ fun m _ =>
    by simpa only [pow_one] using (integrable_cosSum_pow m 1).const_mul (a m)

/-- Centering deletes exactly the coefficient of the trivial representation. -/
theorem integral_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) :
    ∫ θ, characterPolynomial s a θ ∂satoTate = if 0 ∈ s then a 0 else 0 := by
  unfold characterPolynomial
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_cosSum, mul_ite, mul_one, mul_zero]
    exact sum_ite_eq' s 0 a
  · intro m _
    simpa only [pow_one] using (integrable_cosSum_pow m 1).const_mul (a m)

/-- The covariance matrix of distinct symmetric-power characters is diagonal. -/
theorem integral_characterPolynomial_mul (s t : Finset ℕ) (a b : ℕ → ℝ) :
    ∫ θ, characterPolynomial s a θ * characterPolynomial t b θ ∂satoTate =
      ∑ m ∈ s ∩ t, a m * b m := by
  have hpoint (θ : ℝ) :
      characterPolynomial s a θ * characterPolynomial t b θ =
        ∑ m ∈ s, ∑ n ∈ t, (a m * b n) * (cosSum θ m * cosSum θ n) := by
    simp only [characterPolynomial, sum_mul_sum]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_cosSum_mul m n).const_mul (a m * b n)]
  simp_rw [integral_finsetSum _ fun n _ =>
    (integrable_cosSum_mul _ n).const_mul _, integral_const_mul,
    integral_cosSum_mul_cosSum, mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq]
  rw [← sum_filter]
  congr 1

/-- Parseval's identity for a finite Sato–Tate test function. -/
theorem integral_characterPolynomial_sq (s : Finset ℕ) (a : ℕ → ℝ) :
    ∫ θ, characterPolynomial s a θ ^ 2 ∂satoTate = ∑ m ∈ s, a m ^ 2 := by
  simpa only [sq, inter_self] using integral_characterPolynomial_mul s s a a

/-- Squaring a character produces every even character up to twice its degree. -/
theorem cosSum_sq (θ : ℝ) (m : ℕ) :
    cosSum θ m ^ 2 = ∑ r ∈ range (m + 1), cosSum θ (2 * r) := by
  rw [sq, cosSum_mul_cosSum, min_self]
  rw [← sum_range_reflect (fun r => cosSum θ (2 * r)) (m + 1)]
  apply sum_congr rfl
  intro r hr
  congr 1
  have hr' := mem_range.mp hr
  omega

/-- The fourth moment is the number of irreducible summands in the square. -/
theorem integral_cosSum_four (m : ℕ) :
    ∫ θ, cosSum θ m ^ 4 ∂satoTate = (m : ℝ) + 1 := by
  have hpoint (θ : ℝ) : cosSum θ m ^ 4 =
      ∑ r ∈ range (m + 1), ∑ k ∈ range (m + 1),
        cosSum θ (2 * r) * cosSum θ (2 * k) := by
    rw [← sum_mul_sum, ← cosSum_sq]
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun k _ =>
    integrable_cosSum_mul (2 * r) (2 * k)]
  simp_rw [integral_finsetSum _ fun k _ => integrable_cosSum_mul _ (2 * k),
    integral_cosSum_mul_cosSum, Nat.mul_left_cancel_iff (by omega : 0 < 2)]
  simp only [sum_ite_eq]
  rw [sum_congr rfl (fun r hr => if_pos hr)]
  simp

/-- Even symmetric powers have third moment one; odd symmetric powers have third moment zero. -/
theorem integral_cosSum_cube (m : ℕ) :
    ∫ θ, cosSum θ m ^ 3 ∂satoTate = if m % 2 = 0 then 1 else 0 := by
  have hpoint (θ : ℝ) : cosSum θ m ^ 3 =
      ∑ r ∈ range (m + 1), cosSum θ (2 * r) * cosSum θ m := by
    rw [← sum_mul, ← cosSum_sq]
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun r _ => integrable_cosSum_mul (2 * r) m]
  simp_rw [integral_cosSum_mul_cosSum]
  by_cases he : m % 2 = 0
  · rw [if_pos he, sum_eq_single (m / 2)]
    · rw [if_pos (by omega)]
    · intro r _ hr
      rw [if_neg (by omega)]
    · intro h
      exact False.elim (h (mem_range.mpr (by omega)))
  · rw [if_neg he]
    exact sum_eq_zero fun r _ => if_neg (by omega)

/-- Squares of characters have covariance equal to the smaller degree. -/
theorem integral_cosSum_sq_mul_sq (m n : ℕ) :
    ∫ θ, cosSum θ m ^ 2 * cosSum θ n ^ 2 ∂satoTate =
      (min m n : ℝ) + 1 := by
  simp_rw [cosSum_sq, sum_mul_sum]
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun k _ =>
    integrable_cosSum_mul (2 * r) (2 * k)]
  simp_rw [integral_finsetSum _ fun k _ => integrable_cosSum_mul _ (2 * k),
    integral_cosSum_mul_cosSum, Nat.mul_left_cancel_iff (by omega : 0 < 2)]
  simp only [sum_ite_eq, mem_range]
  rw [sum_boole]
  have hset : {r ∈ range (m + 1) | r < n + 1} = range (min m n + 1) := by
    ext r
    simp only [mem_filter, mem_range]
    omega
  rw [hset, card_range]
  push_cast
  rfl

theorem integrable_cosSum_sq_mul_sq (m n : ℕ) :
    Integrable (fun θ => cosSum θ m ^ 2 * cosSum θ n ^ 2) satoTate := by
  refine Integrable.of_bound (((continuous_cosSum m).pow 2).mul
    ((continuous_cosSum n).pow 2)).aestronglyMeasurable
    ((((m : ℝ) + 1) * ((n : ℝ) + 1)) ^ 2) (ae_of_all _ fun θ => ?_)
  rw [← mul_pow, norm_pow, Real.norm_eq_abs, abs_mul]
  exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_le_mul (abs_cosSum_le θ m) (abs_cosSum_le θ n)
      (abs_nonneg _) (by positivity)) 2

/-- The centered squared characters form the covariance kernel `min(m,n)`. -/
theorem integral_centered_cosSum_sq_mul (m n : ℕ) :
    ∫ θ, (cosSum θ m ^ 2 - 1) * (cosSum θ n ^ 2 - 1) ∂satoTate =
      (min m n : ℝ) := by
  have hprod := integrable_cosSum_sq_mul_sq m n
  have hsub : Integrable
      (fun θ => cosSum θ m ^ 2 * cosSum θ n ^ 2 - cosSum θ m ^ 2) satoTate :=
    hprod.sub (integrable_cosSum_pow m 2)
  have hsub' : Integrable
      (fun θ => cosSum θ m ^ 2 * cosSum θ n ^ 2 - cosSum θ m ^ 2 - cosSum θ n ^ 2)
      satoTate := hsub.sub (integrable_cosSum_pow n 2)
  have hpoint (θ : ℝ) : (cosSum θ m ^ 2 - 1) * (cosSum θ n ^ 2 - 1) =
      (cosSum θ m ^ 2 * cosSum θ n ^ 2 - cosSum θ m ^ 2) - cosSum θ n ^ 2 + 1 := by
    ring
  simp_rw [hpoint]
  rw [integral_add (f := fun θ =>
      (cosSum θ m ^ 2 * cosSum θ n ^ 2 - cosSum θ m ^ 2) - cosSum θ n ^ 2)
    (g := fun _ => (1 : ℝ)) hsub' (integrable_const 1),
    integral_sub (f := fun θ => cosSum θ m ^ 2 * cosSum θ n ^ 2 - cosSum θ m ^ 2)
      (g := fun θ => cosSum θ n ^ 2) hsub (integrable_cosSum_pow n 2),
    integral_sub (f := fun θ => cosSum θ m ^ 2 * cosSum θ n ^ 2)
      (g := fun θ => cosSum θ m ^ 2) hprod (integrable_cosSum_pow m 2),
    integral_cosSum_sq_mul_sq]
  have hm : (∫ θ, cosSum θ m ^ 2 ∂satoTate) = 1 := by
    simpa only [sq, if_true] using integral_cosSum_mul_cosSum m m
  have hn : (∫ θ, cosSum θ n ^ 2 ∂satoTate) = 1 := by
    simpa only [sq, if_true] using integral_cosSum_mul_cosSum n n
  rw [hm, hn]
  simp

/-- Independent torus coordinates multiply the character fourth moments. -/
theorem integral_chiProd_four {n : ℕ} (k : Fin n → ℕ) :
    ∫ θ, chiProd θ k ^ 4 ∂torusMeasure n = ∏ i, ((k i : ℝ) + 1) := by
  simp only [chiProd, ← prod_pow, torusMeasure]
  rw [integral_fintype_prod_eq_prod (f := fun i θ => cosSum θ (k i) ^ 4)]
  simp only [integral_cosSum_four]

/-- Every nontrivial character has variance one but degree-dependent kurtosis. -/
theorem cosSum_fluctuation_moments (m : ℕ) :
    (∫ θ, cosSum θ (m + 1) ∂satoTate) = 0 ∧
    (∫ θ, cosSum θ (m + 1) ^ 2 ∂satoTate) = 1 ∧
    (∫ θ, cosSum θ (m + 1) ^ 4 ∂satoTate) = (m : ℝ) + 2 := by
  refine ⟨by simp [integral_cosSum], ?_, ?_⟩
  · simpa only [sq, if_true] using integral_cosSum_mul_cosSum (m + 1) (m + 1)
  · convert integral_cosSum_four (m + 1) using 1
    push_cast
    ring

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
