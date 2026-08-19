import GaloisForLFunctions.HTGeometry.DifferenceOperatorFactorization

/-!
# Hyperexponential solutions and the Riccati equation, in every order

A solution of a scalar linear difference equation whose logarithmic difference `σ y / y` lies in the
base field forces that ratio to solve the Riccati equation of the equation, in every order and in
every difference field extension.  Conversely such a ratio produces a solution in any extension
where one exists.

So a proof that the Riccati equation has no solution in the base field is a proof that the equation
has no *hyperexponential* solution over that base — no solution at all, in any extension, whose
logarithmic difference is rational.  For the Bessel order recurrence the corpus already owns the
rational-Riccati obstruction, so this upgrades it to a statement about arbitrary extensions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The partial products of the shifts of a logarithmic difference. -/
def riccatiProduct (σ : K →+* K) (r : K) (m : ℕ) : K :=
  ∏ i ∈ Finset.range m, (⇑σ)^[i] r

@[simp] theorem riccatiProduct_zero (σ : K →+* K) (r : K) : riccatiProduct σ r 0 = 1 := by
  simp [riccatiProduct]

theorem riccatiProduct_succ (σ : K →+* K) (r : K) (m : ℕ) :
    riccatiProduct σ r (m + 1) = σ (riccatiProduct σ r m) * r := by
  unfold riccatiProduct
  rw [Finset.prod_range_succ', map_prod]
  simp only [Function.iterate_zero_apply]
  refine congrArg (fun t => t * r) ?_
  exact Finset.prod_congr rfl fun i _ => Function.iterate_succ_apply' (⇑σ) i r

/-- The iterates of a hyperexponential element are its partial Riccati products. -/
theorem iterate_of_logDifference (σK : K →+* K) (σL : L →+* L)
    (hcompat : ∀ a : K, σL (algebraMap K L a) = algebraMap K L (σK a))
    {y : L} {r : K} (hr : σL y = algebraMap K L r * y) (m : ℕ) :
    (⇑σL)^[m] y = algebraMap K L (riccatiProduct σK r m) * y := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, hcompat, hr, riccatiProduct_succ, map_mul]
      ring

/-- **A hyperexponential solution solves the Riccati equation.** -/
theorem riccatiProduct_relation_of_solution (σK : K →+* K) (σL : L →+* L)
    (hcompat : ∀ a : K, σL (algebraMap K L a) = algebraMap K L (σK a))
    {n : ℕ} (a : Fin n → K) {y : L} {r : K} (hy : y ≠ 0)
    (hr : σL y = algebraMap K L r * y)
    (hsol : (⇑σL)^[n] y = ∑ j, algebraMap K L (a j) * (⇑σL)^[(j : ℕ)] y) :
    riccatiProduct σK r n = ∑ j : Fin n, a j * riccatiProduct σK r (j : ℕ) := by
  classical
  have hleft : (⇑σL)^[n] y = algebraMap K L (riccatiProduct σK r n) * y :=
    iterate_of_logDifference σK σL hcompat hr n
  have hright : ∑ j : Fin n, algebraMap K L (a j) * (⇑σL)^[(j : ℕ)] y
      = algebraMap K L (∑ j : Fin n, a j * riccatiProduct σK r (j : ℕ)) * y := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iterate_of_logDifference σK σL hcompat hr (j : ℕ), map_mul]
    ring
  rw [hleft, hright] at hsol
  have hcancel : algebraMap K L (riccatiProduct σK r n)
      = algebraMap K L (∑ j : Fin n, a j * riccatiProduct σK r (j : ℕ)) :=
    mul_right_cancel₀ hy hsol
  exact (algebraMap K L).injective hcancel

/-- **A Riccati solution turns a hyperexponential element into a solution.** -/
theorem solution_of_riccatiProduct_relation (σK : K →+* K) (σL : L →+* L)
    (hcompat : ∀ a : K, σL (algebraMap K L a) = algebraMap K L (σK a))
    {n : ℕ} (a : Fin n → K) {y : L} {r : K}
    (hr : σL y = algebraMap K L r * y)
    (hric : riccatiProduct σK r n = ∑ j : Fin n, a j * riccatiProduct σK r (j : ℕ)) :
    (⇑σL)^[n] y = ∑ j, algebraMap K L (a j) * (⇑σL)^[(j : ℕ)] y := by
  classical
  rw [iterate_of_logDifference σK σL hcompat hr n, hric, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_of_logDifference σK σL hcompat hr (j : ℕ), map_mul]
  ring

/-- **No hyperexponential solution for the Bessel order recurrence.**  In no difference field
extension of `ℂ(X)` does the order recurrence have a nonzero solution whose logarithmic difference
is rational. -/
theorem besselOrder_no_hyperexponential_solution {c : ℂ} (hc : c ≠ 0)
    {L : Type*} [Field L] [Algebra (RatFunc ℂ) L] (σL : L →+* L)
    (hcompat : ∀ a : RatFunc ℂ,
      σL (algebraMap (RatFunc ℂ) L a) = algebraMap (RatFunc ℂ) L (ratShift a))
    {y : L} {r : RatFunc ℂ} (hy : y ≠ 0)
    (hr : σL y = algebraMap (RatFunc ℂ) L r * y)
    (hsol : (⇑σL)^[2] y = ∑ j : Fin 2,
      algebraMap (RatFunc ℂ) L
        (![1, algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C c * (Polynomial.X + Polynomial.C 1))] j)
      * (⇑σL)^[(j : ℕ)] y) : False := by
  have hric := riccatiProduct_relation_of_solution ratShift σL hcompat
    ![1, algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c * (Polynomial.X + Polynomial.C 1))] hy hr hsol
  refine orderBesselRiccati_no_ratFunc_solution hc ⟨r, ?_⟩
  simp only [riccatiProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Finset.prod_range_zero,
    Finset.prod_range_succ, Function.iterate_zero_apply, Function.iterate_one] at hric
  linear_combination hric

end

end GaloisForLFunctions.HTGeometry
