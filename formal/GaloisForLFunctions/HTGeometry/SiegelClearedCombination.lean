import GaloisForLFunctions.HTGeometry.SiegelPolynomial

/-!
# Clearing denominators from a Siegel combination

On a chart where the given meromorphic functions are quotients `A k / B k`, the combination
attached to a coefficient vector is not holomorphic, but multiplying it by `∏ B k ^ m` is: each
monomial `∏ (A k / B k) ^ β k` becomes `∏ A k ^ β k · B k ^ (m − β k)`, and the exponents stay
nonnegative because the box bounds every `β k` by `m`.

This is the object a Siegel count actually estimates chartwise.  The comparison constant between two
charts is then the `m`-th power of the ratio of their denominators, which is bounded precisely
because reduced local presentations have associated denominators.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n m : ℕ}

/-- The denominator-cleared combination on a chart. -/
noncomputable def siegelHomCombination {E : Type*} (A B : Fin (n + 1) → E → ℂ) (m : ℕ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : E → ℂ :=
  fun w => ∑ β : Fin (n + 1) → Fin (m + 1),
    a β * ∏ k, (A k w) ^ (β k : ℕ) * (B k w) ^ (m - (β k : ℕ))

/-- **Clearing denominators.**  Where the denominators do not vanish, the cleared combination is the
combination of the quotients times the product of the `m`-th powers of the denominators. -/
theorem siegelHomCombination_eq {E : Type*} (A B : Fin (n + 1) → E → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (w : E) (hB : ∀ k, B k w ≠ 0) :
    siegelHomCombination A B m a w
      = siegelCombination (fun k w => A k w / B k w) a w * ∏ k, (B k w) ^ m := by
  classical
  rw [siegelHomCombination, siegelCombination, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hle : (β k : ℕ) ≤ m := Nat.lt_succ_iff.mp (β k).isLt
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ (hB k))]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

theorem siegelHomCombination_add {E : Type*} (A B : Fin (n + 1) → E → ℂ)
    (a b : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    siegelHomCombination A B m (a + b)
      = fun w => siegelHomCombination A B m a w + siegelHomCombination A B m b w := by
  funext w
  simp only [siegelHomCombination, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem siegelHomCombination_smul {E : Type*} (A B : Fin (n + 1) → E → ℂ) (t : ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    siegelHomCombination A B m (t • a) = fun w => t * siegelHomCombination A B m a w := by
  funext w
  simp only [siegelHomCombination, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem continuous_siegelHomCombination {E : Type*} [TopologicalSpace E]
    {A B : Fin (n + 1) → E → ℂ} (hA : ∀ k, Continuous (A k)) (hB : ∀ k, Continuous (B k))
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : Continuous (siegelHomCombination A B m a) := by
  refine continuous_finsetSum _ fun β _ => ?_
  refine continuous_const.mul ?_
  exact continuous_finsetProd _ fun k _ => ((hA k).pow _).mul ((hB k).pow _)

theorem contDiff_siegelHomCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : Fin (n + 1) → E → ℂ} (hA : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (A k))
    (hB : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (B k)) (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (siegelHomCombination A B m a) := by
  refine ContDiff.sum fun β _ => ?_
  refine contDiff_const.mul ?_
  exact contDiff_prod fun k _ => ((hA k).pow _).mul ((hB k).pow _)

theorem differentiable_siegelHomCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : Fin (n + 1) → E → ℂ} (hA : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (A k))
    (hB : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (B k)) (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    Differentiable ℂ (siegelHomCombination A B m a) :=
  (contDiff_siegelHomCombination hA hB a).differentiable (by simp)

/-- **A nonvanishing cleared combination gives a nonvanishing combination.**  Where the
denominators do not vanish, the cleared combination vanishes exactly when the combination of the
quotients does. -/
theorem siegelCombination_eq_zero_of_hom_eq_zero {E : Type*} (A B : Fin (n + 1) → E → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (w : E) (hB : ∀ k, B k w ≠ 0)
    (h : siegelHomCombination A B m a w = 0) :
    siegelCombination (fun k w => A k w / B k w) a w = 0 := by
  have hprod : (∏ k, (B k w) ^ m) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hB k)
  have := siegelHomCombination_eq A B a w hB
  rw [h] at this
  exact (mul_eq_zero.mp this.symm).resolve_right hprod

end GaloisForLFunctions.HTGeometry
