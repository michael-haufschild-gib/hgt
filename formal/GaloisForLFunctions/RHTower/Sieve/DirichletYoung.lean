import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

/-!
# Finite Young inequality for multiplicative Dirichlet convolution

The product-index convolution sends an `ell^2` coefficient vector convolved with an `ell^1`
coefficient vector into `ell^2`.  Unlike a fibrewise Cauchy bound, this loses no divisor factor.
-/

namespace RHTower.Sieve

open Finset

/-- Finite complex `ell^2` Minkowski inequality. -/
theorem sqrt_sum_norm_sq_finset_sum_le {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (f : ι → κ → ℂ) :
    Real.sqrt (∑ k : κ, ‖∑ i ∈ s, f i k‖ ^ 2)
      ≤ ∑ i ∈ s, Real.sqrt (∑ k : κ, ‖f i k‖ ^ 2) := by
  classical
  have hnorm : ∀ z : κ → ℂ,
      ‖(WithLp.toLp 2 z : EuclideanSpace ℂ κ)‖ =
        Real.sqrt (∑ k : κ, ‖z k‖ ^ 2) := by
    intro z
    rw [EuclideanSpace.norm_eq]
  have hsum :
      (WithLp.toLp 2 (fun k : κ => ∑ i ∈ s, f i k) : EuclideanSpace ℂ κ) =
        ∑ i ∈ s, (WithLp.toLp 2 (f i) : EuclideanSpace ℂ κ) := by
    ext k
    simp
  rw [← hnorm, hsum]
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact hnorm (f i)

/-- Contribution to a Dirichlet convolution with its right index fixed. -/
noncomputable def dirConvRightSlice (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (k : Fin M) (r : Fin (N * M)) : ℂ :=
  ∑ j : Fin N, if prodIdx (j, k) = r then a j * b k else 0

/-- A Dirichlet convolution is the sum of its right-index slices. -/
theorem dirConv_eq_sum_rightSlice (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (r : Fin (N * M)) :
    dirConv N M a b r = ∑ k : Fin M, dirConvRightSlice N M a b k r := by
  classical
  rw [dirConv, filter_prodIdx_eq]
  simp only [dirConvRightSlice, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl fun q _ => rfl

/-- With the right index fixed, the product-index map is injective. -/
theorem prodIdx_fixed_right_injective {N M : ℕ} (k : Fin M) :
    Function.Injective (fun j : Fin N => prodIdx (j, k)) := by
  intro j₁ j₂ h
  have hval := congrArg (fun r : Fin (N * M) => (r : ℕ) + 1) h
  rw [prodIdx_val, prodIdx_val] at hval
  dsimp only at hval
  have heq : (j₁ : ℕ) + 1 = (j₂ : ℕ) + 1 :=
    Nat.mul_right_cancel (by omega) hval
  apply Fin.ext
  omega

/-- A right slice has no more `ell^2` energy than its unfurled coefficient vector. -/
theorem sum_norm_sq_dirConvRightSlice_le (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (k : Fin M) :
    ∑ r : Fin (N * M), ‖dirConvRightSlice N M a b k r‖ ^ 2
      ≤ ‖b k‖ ^ 2 * ∑ j : Fin N, ‖a j‖ ^ 2 := by
  classical
  have hcard : ∀ r : Fin (N * M),
      ((Finset.univ : Finset (Fin N)).filter (fun j => prodIdx (j, k) = r)).card ≤ 1 := by
    intro r
    rw [Finset.card_le_one]
    intro j₁ hj₁ j₂ hj₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
    exact prodIdx_fixed_right_injective k (hj₁.trans hj₂.symm)
  have hterm : ∀ r : Fin (N * M),
      ‖dirConvRightSlice N M a b k r‖ ^ 2
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => prodIdx (j, k) = r),
            ‖a j * b k‖ ^ 2 := by
    intro r
    rw [dirConvRightSlice, ← Finset.sum_filter]
    have hnorm := norm_sum_le
      ((Finset.univ : Finset (Fin N)).filter (fun j => prodIdx (j, k) = r))
      (fun j => a j * b k)
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hsq := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N)).filter (fun j => prodIdx (j, k) = r))
      (f := fun j => ‖a j * b k‖)
    have hsum0 : 0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin N)).filter
        (fun j => prodIdx (j, k) = r), ‖a j * b k‖ ^ 2 := by positivity
    have hcardR :
        ((((Finset.univ : Finset (Fin N)).filter
          (fun j => prodIdx (j, k) = r)).card : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hcard r
    nlinarith
  refine (Finset.sum_le_sum fun r _ => hterm r).trans ?_
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      prodIdx (j, k) ∈ (Finset.univ : Finset (Fin (N * M))) :=
    fun j _ => Finset.mem_univ _
  have hfibre := Finset.sum_fiberwise_of_maps_to hmaps (fun j : Fin N => ‖a j * b k‖ ^ 2)
  rw [hfibre]
  simp_rw [norm_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => le_of_eq (by ring)

/-- **Finite multiplicative Young inequality, `ell^2` convolved with `ell^1` to `ell^2`.** -/
theorem sum_norm_sq_dirConv_le_l2_l1 (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) :
    ∑ r : Fin (N * M), ‖dirConv N M a b r‖ ^ 2
      ≤ (∑ j : Fin N, ‖a j‖ ^ 2) * (∑ k : Fin M, ‖b k‖) ^ 2 := by
  classical
  let A : ℝ := ∑ j : Fin N, ‖a j‖ ^ 2
  let B : ℝ := ∑ k : Fin M, ‖b k‖
  let E : ℝ := ∑ r : Fin (N * M), ‖dirConv N M a b r‖ ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hE : 0 ≤ E := by positivity
  have hmink :
      Real.sqrt E ≤
        ∑ k : Fin M,
          Real.sqrt (∑ r : Fin (N * M), ‖dirConvRightSlice N M a b k r‖ ^ 2) := by
    have h := sqrt_sum_norm_sq_finset_sum_le
      (s := (Finset.univ : Finset (Fin M)))
      (f := fun k r => dirConvRightSlice N M a b k r)
    simpa only [E, dirConv_eq_sum_rightSlice] using h
  have hslice : ∀ k : Fin M,
      Real.sqrt (∑ r : Fin (N * M), ‖dirConvRightSlice N M a b k r‖ ^ 2)
        ≤ ‖b k‖ * Real.sqrt A := by
    intro k
    calc
      Real.sqrt (∑ r : Fin (N * M), ‖dirConvRightSlice N M a b k r‖ ^ 2)
          ≤ Real.sqrt (‖b k‖ ^ 2 * A) :=
        Real.sqrt_le_sqrt (sum_norm_sq_dirConvRightSlice_le N M a b k)
      _ = ‖b k‖ * Real.sqrt A := by
        rw [Real.sqrt_mul (sq_nonneg ‖b k‖), Real.sqrt_sq (norm_nonneg _)]
  have hsqrt : Real.sqrt E ≤ Real.sqrt A * B := by
    refine hmink.trans ?_
    calc
      (∑ k : Fin M,
          Real.sqrt (∑ r : Fin (N * M), ‖dirConvRightSlice N M a b k r‖ ^ 2))
          ≤ ∑ k : Fin M, ‖b k‖ * Real.sqrt A :=
        Finset.sum_le_sum fun k _ => hslice k
      _ = Real.sqrt A * B := by
        simp only [A, B]
        rw [← Finset.sum_mul]
        ring
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg E) hsqrt 2
  have hsqrtE : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have hsqrtA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  dsimp only [E, A, B] at *
  nlinarith

end RHTower.Sieve
