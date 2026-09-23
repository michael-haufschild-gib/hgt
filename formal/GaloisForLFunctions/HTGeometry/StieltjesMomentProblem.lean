import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# The Stieltjes moment problem: shifted-Hankel positivity

The Stieltjes (one-sided) analogue of the Hamburger criteria of
`MomentFunctionalPositivity`.  When the representing measure is supported on `[0, ∞)` the moment
functional is positive not only on squares `p²` but on `x·p²`, so the **shifted Hankel matrix**
`(sᵢ₊ⱼ₊₁)` is positive semidefinite in addition to `(sᵢ₊ⱼ)`.  Positivity of both Hankel families is
exactly the Stieltjes solvability criterion (a moment sequence has a representing measure on `[0,∞)`
iff `(sᵢ₊ⱼ)` and `(sᵢ₊ⱼ₊₁)` are both positive semidefinite).  The mechanism is
`L_s(x·p²) = ∫ x·(eval x p)² dμ ≥ 0`, which holds because both factors are nonnegative `μ`-a.e.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

/-- **Stieltjes positivity of the moment functional.**  If the representing measure is supported on
`[0, ∞)` (`0 ≤ x` for `μ`-a.e. `x`), the moment functional is nonnegative on `x·p²`. -/
theorem momentFunctional_X_mul_sq_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμpos : ∀ᵐ x ∂μ, 0 ≤ x) (p : Polynomial ℝ) :
    0 ≤ momentFunctional s (X * p ^ (2 : ℕ)) := by
  rw [momentFunctional_eq_integral s hs hint]
  have hcongr : ∫ x, Polynomial.eval x (X * p ^ (2 : ℕ)) ∂μ
      = ∫ x, x * (Polynomial.eval x p) ^ (2 : ℕ) ∂μ := by
    refine integral_congr_ae (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x (X * p ^ (2 : ℕ)) = x * (Polynomial.eval x p) ^ (2 : ℕ)
    rw [eval_mul, eval_X, eval_pow]
  rw [hcongr]
  exact integral_nonneg_of_ae (hμpos.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))

/-- The moment functional of `x·(∑ᵢ vᵢ Xⁱ)²` is the shifted Hankel form `∑ᵢⱼ vᵢ vⱼ s_{i+j+1}`. -/
theorem momentFunctional_X_mul_sq_eq_shiftedHankel (s : ℕ → ℝ) {n : ℕ} (v : Fin n → ℝ) :
    momentFunctional s (X * (∑ i : Fin n, v i • X ^ (i : ℕ)) ^ (2 : ℕ))
      = ∑ i : Fin n, ∑ j : Fin n, v i * v j * s ((i : ℕ) + (j : ℕ) + 1) := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum, momentFunctional_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, momentFunctional_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show X * ((v i • X ^ (i : ℕ)) * (v j • X ^ (j : ℕ)))
      = (v i * v j) • X ^ ((i : ℕ) + (j : ℕ) + 1) from by
        rw [smul_mul_smul_comm, ← pow_add, mul_smul_comm, ← pow_succ'],
    momentFunctional_smul, momentFunctional_X_pow]

/-- **Stieltjes shifted-Hankel criterion.**  For a representing measure supported on `[0, ∞)` the
shifted Hankel matrix `(sᵢ₊ⱼ₊₁)` is positive semidefinite: `∑ᵢⱼ vᵢ vⱼ s_{i+j+1} ≥ 0` for every real
vector `v`.  Together with `hankelForm_nonneg` this is the necessary side of Stieltjes solvability. -/
theorem shiftedHankelForm_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμpos : ∀ᵐ x ∂μ, 0 ≤ x) {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j * s ((i : ℕ) + (j : ℕ) + 1) := by
  rw [← momentFunctional_X_mul_sq_eq_shiftedHankel s v]
  exact momentFunctional_X_mul_sq_nonneg s hs hint hμpos _

/-- The shifted Hankel matrix `(sᵢ₊ⱼ₊₁)` of a `[0,∞)`-supported representing measure is positive
semidefinite as an actual matrix. -/
theorem shiftedHankelMatrix_posSemidef {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμpos : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    (Matrix.of fun i j : Fin n => s ((i : ℕ) + (j : ℕ) + 1)).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    congr 1
    omega
  · have heq : (x.sum fun i xi => x.sum fun j xj =>
        star xi * (Matrix.of fun i j : Fin n => s ((i : ℕ) + (j : ℕ) + 1)) i j * xj)
        = ∑ i, ∑ j, (x i) * (x j) * s ((i : ℕ) + (j : ℕ) + 1) := by
      rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Matrix.of_apply, star_trivial]; ring
    rw [heq]; exact shiftedHankelForm_nonneg s hs hint hμpos _

/-- **Stieltjes determinant criterion.**  Every shifted Hankel determinant `det (sᵢ₊ⱼ₊₁)_{i,j<n}` of a
`[0,∞)`-supported representing measure is nonnegative. -/
theorem shiftedHankelMatrix_det_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμpos : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    0 ≤ (Matrix.of fun i j : Fin n => s ((i : ℕ) + (j : ℕ) + 1)).det :=
  (shiftedHankelMatrix_posSemidef s hs hint hμpos n).det_nonneg

/-- Subtractivity of the moment functional. -/
theorem momentFunctional_sub (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentFunctional s (p - q) = momentFunctional s p - momentFunctional s q := by
  rw [sub_eq_add_neg, momentFunctional_add, sub_eq_add_neg]
  congr 1
  rw [show -q = (-1 : ℝ) • q by rw [neg_one_smul], momentFunctional_smul]; ring

/-- **Hausdorff positivity of the moment functional.**  If the representing measure is supported on
`(-∞, 1]` (`x ≤ 1` for `μ`-a.e. `x`), the moment functional is nonnegative on `(1 - x)·p²`. -/
theorem momentFunctional_one_sub_X_mul_sq_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμle : ∀ᵐ x ∂μ, x ≤ 1) (p : Polynomial ℝ) :
    0 ≤ momentFunctional s ((1 - X) * p ^ (2 : ℕ)) := by
  rw [momentFunctional_eq_integral s hs hint]
  have hcongr : ∫ x, Polynomial.eval x ((1 - X) * p ^ (2 : ℕ)) ∂μ
      = ∫ x, (1 - x) * (Polynomial.eval x p) ^ (2 : ℕ) ∂μ := by
    refine integral_congr_ae (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x ((1 - X) * p ^ (2 : ℕ)) = (1 - x) * (Polynomial.eval x p) ^ (2 : ℕ)
    rw [eval_mul, eval_sub, eval_one, eval_X, eval_pow]
  rw [hcongr]
  exact integral_nonneg_of_ae (hμle.mono (fun x hx => mul_nonneg (by linarith) (sq_nonneg _)))

/-- **Hausdorff difference-Hankel criterion.**  For a representing measure supported on `[0, 1]` the
difference Hankel form `(sᵢ₊ⱼ − sᵢ₊ⱼ₊₁)` is positive semidefinite: `∑ᵢⱼ vᵢ vⱼ (s_{i+j} − s_{i+j+1}) ≥ 0`.
Together with `hankelForm_nonneg` and `shiftedHankelForm_nonneg` this is the necessary side of the
Hausdorff (bounded-interval) moment criterion. -/
theorem hausdorffDiffForm_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμle : ∀ᵐ x ∂μ, x ≤ 1) {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      v i * v j * (s ((i : ℕ) + (j : ℕ)) - s ((i : ℕ) + (j : ℕ) + 1)) := by
  have hid : momentFunctional s ((1 - X) * (∑ i : Fin n, v i • X ^ (i : ℕ)) ^ (2 : ℕ))
      = ∑ i : Fin n, ∑ j : Fin n,
        v i * v j * (s ((i : ℕ) + (j : ℕ)) - s ((i : ℕ) + (j : ℕ) + 1)) := by
    have hpoly : ((1 : Polynomial ℝ) - X) * (∑ i : Fin n, v i • X ^ (i : ℕ)) ^ (2 : ℕ)
        = (∑ i : Fin n, v i • X ^ (i : ℕ)) ^ (2 : ℕ)
          - X * (∑ i : Fin n, v i • X ^ (i : ℕ)) ^ (2 : ℕ) := by ring
    rw [hpoly, momentFunctional_sub, momentFunctional_sq_eq_hankelForm,
      momentFunctional_X_mul_sq_eq_shiftedHankel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [← hid]
  exact momentFunctional_one_sub_X_mul_sq_nonneg s hs hint hμle _

end HTGeometry
