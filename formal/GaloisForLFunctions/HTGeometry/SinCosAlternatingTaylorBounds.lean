import Mathlib

/-!
# Alternating Taylor bounds for sine and cosine at every order

For `x ≥ 0` and `n ≥ 1` the Taylor partial sums

`C_n(x) = Σ_{k<n} (−1)^k x^{2k}/(2k)!`,   `S_n(x) = Σ_{k<n} (−1)^k x^{2k+1}/(2k+1)!`

satisfy `(−1)^n (cos x − C_n(x)) ≥ 0` and `(−1)^n (sin x − S_n(x)) ≥ 0`: the partial sums
alternate around `cos` and `sin`.  The proof is one induction: `S_n' = C_n`, `C_{n+1}' = −S_n`, both
remainders vanish at `0`, and a function with nonnegative derivative on `[0, ∞)` vanishing at `0` is
nonnegative there.  For the cosine the bounds hold on all of `ℝ` by evenness.
-/

namespace GaloisForLFunctions.HTGeometry

open Real Finset Set

/-- The cosine Taylor partial sum `Σ_{k<n} (−1)^k x^{2k}/(2k)!`. -/
noncomputable def cosTaylorSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- The sine Taylor partial sum `Σ_{k<n} (−1)^k x^{2k+1}/(2k+1)!`. -/
noncomputable def sinTaylorSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

theorem sinTaylorSum_zero_arg (n : ℕ) : sinTaylorSum n 0 = 0 := by
  unfold sinTaylorSum
  refine Finset.sum_eq_zero (fun k _ => ?_)
  simp

theorem cosTaylorSum_succ_zero_arg (n : ℕ) : cosTaylorSum (n + 1) 0 = 1 := by
  unfold cosTaylorSum
  rw [Finset.sum_range_succ']
  have h : ∑ k ∈ range n, (-1 : ℝ) ^ (k + 1) * (0 : ℝ) ^ (2 * (k + 1)) /
      ((2 * (k + 1)).factorial : ℝ) = 0 :=
    Finset.sum_eq_zero (fun k _ => by simp)
  rw [h]
  simp

theorem cosTaylorSum_neg (n : ℕ) (x : ℝ) : cosTaylorSum n (-x) = cosTaylorSum n x := by
  unfold cosTaylorSum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_mul, pow_mul, neg_sq]

theorem hasDerivAt_sinTaylorSum (n : ℕ) (x : ℝ) :
    HasDerivAt (sinTaylorSum n) (cosTaylorSum n x) x := by
  unfold sinTaylorSum cosTaylorSum
  have : ∀ k ∈ range n, HasDerivAt
      (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      ((-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)) x := by
    intro k _
    have h := ((hasDerivAt_pow (2 * k + 1) x).const_mul ((-1 : ℝ) ^ k)).div_const
      ((2 * k + 1).factorial : ℝ)
    refine h.congr_deriv ?_
    rw [Nat.factorial_succ, show 2 * k + 1 - 1 = 2 * k by omega]
    push_cast
    have hf : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  exact HasDerivAt.fun_sum this

theorem hasDerivAt_cosTaylorSum_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (cosTaylorSum (n + 1)) (-sinTaylorSum n x) x := by
  have hfun : cosTaylorSum (n + 1) = fun y => 1 + ∑ k ∈ range n,
      (-1 : ℝ) ^ (k + 1) * y ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) := by
    funext y
    unfold cosTaylorSum
    rw [Finset.sum_range_succ']
    simp [add_comm]
  rw [hfun]
  have : ∀ k ∈ range n, HasDerivAt
      (fun y : ℝ => (-1 : ℝ) ^ (k + 1) * y ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ))
      (-((-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))) x := by
    intro k _
    have h := ((hasDerivAt_pow (2 * (k + 1)) x).const_mul ((-1 : ℝ) ^ (k + 1))).div_const
      ((2 * (k + 1)).factorial : ℝ)
    refine h.congr_deriv ?_
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ,
      show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
    push_cast
    have hf : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hs := (hasDerivAt_const x (1 : ℝ)).add (HasDerivAt.fun_sum this)
  refine hs.congr_deriv ?_
  unfold sinTaylorSum
  rw [Finset.sum_neg_distrib]
  ring

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y).deriv]
      exact hd y (le_of_lt hy)
  have := hmono self_mem_Ici hx hx
  rwa [h0] at this

theorem sin_remainder_nonneg_of_cos {n : ℕ}
    (hc : ∀ y, 0 ≤ y → 0 ≤ (-1 : ℝ) ^ n * (Real.cos y - cosTaylorSum n y)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ n * (Real.sin x - sinTaylorSum n x) := by
  refine nonneg_of_hasDerivAt_nonneg (f' := fun y => (-1 : ℝ) ^ n * (Real.cos y - cosTaylorSum n y))
    (fun y => ((Real.hasDerivAt_sin y).sub (hasDerivAt_sinTaylorSum n y)).const_mul _) ?_ hc hx
  simp [sinTaylorSum_zero_arg]

theorem cos_remainder_succ_nonneg_of_sin {n : ℕ}
    (hs : ∀ y, 0 ≤ y → 0 ≤ (-1 : ℝ) ^ n * (Real.sin y - sinTaylorSum n y)) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ (n + 1) * (Real.cos x - cosTaylorSum (n + 1) x) := by
  refine nonneg_of_hasDerivAt_nonneg
    (f' := fun y => (-1 : ℝ) ^ (n + 1) * (-Real.sin y - -sinTaylorSum n y))
    (fun y => ((Real.hasDerivAt_cos y).sub (hasDerivAt_cosTaylorSum_succ n y)).const_mul _) ?_ ?_ hx
  · simp [cosTaylorSum_succ_zero_arg]
  · intro y hy
    have := hs y hy
    have heq : (-1 : ℝ) ^ (n + 1) * (-Real.sin y - -sinTaylorSum n y) =
        (-1 : ℝ) ^ n * (Real.sin y - sinTaylorSum n y) := by ring
    rw [heq]
    exact this

/-- **Alternating Taylor bounds.**  For `n ≥ 1` and `x ≥ 0` both remainders have sign `(−1)^n`. -/
theorem sinCos_alternating_remainder_nonneg (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1 : ℝ) ^ n * (Real.cos x - cosTaylorSum n x) ∧
      0 ≤ (-1 : ℝ) ^ n * (Real.sin x - sinTaylorSum n x) := by
  induction n, hn using Nat.le_induction generalizing x with
  | base =>
    have hc : ∀ y, 0 ≤ y → 0 ≤ (-1 : ℝ) ^ 1 * (Real.cos y - cosTaylorSum 1 y) := by
      intro y _
      simp [cosTaylorSum, Real.cos_le_one]
    exact ⟨hc x hx, sin_remainder_nonneg_of_cos hc hx⟩
  | succ n hn ih =>
    have hc : ∀ y, 0 ≤ y → 0 ≤ (-1 : ℝ) ^ (n + 1) * (Real.cos y - cosTaylorSum (n + 1) y) :=
      fun y hy => cos_remainder_succ_nonneg_of_sin (fun z hz => (ih hz).2) hy
    exact ⟨hc x hx, sin_remainder_nonneg_of_cos hc hx⟩

/-- `cos x ≤ C_{2k+1}(x)` for every real `x`. -/
theorem cos_le_cosTaylorSum_odd (k : ℕ) (x : ℝ) : Real.cos x ≤ cosTaylorSum (2 * k + 1) x := by
  have key : ∀ y, 0 ≤ y → Real.cos y ≤ cosTaylorSum (2 * k + 1) y := by
    intro y hy
    have h := (sinCos_alternating_remainder_nonneg (2 * k + 1) (by omega) hy).1
    rw [Odd.neg_one_pow ⟨k, rfl⟩] at h
    linarith
  rcases le_total 0 x with hx | hx
  · exact key x hx
  · have := key (-x) (by linarith)
    rwa [Real.cos_neg, cosTaylorSum_neg] at this

/-- `C_{2k+2}(x) ≤ cos x` for every real `x`. -/
theorem cosTaylorSum_even_le_cos (k : ℕ) (x : ℝ) : cosTaylorSum (2 * k + 2) x ≤ Real.cos x := by
  have key : ∀ y, 0 ≤ y → cosTaylorSum (2 * k + 2) y ≤ Real.cos y := by
    intro y hy
    have h := (sinCos_alternating_remainder_nonneg (2 * k + 2) (by omega) hy).1
    rw [Even.neg_one_pow ⟨k + 1, by ring⟩] at h
    linarith
  rcases le_total 0 x with hx | hx
  · exact key x hx
  · have := key (-x) (by linarith)
    rwa [Real.cos_neg, cosTaylorSum_neg] at this

/-- `sin x ≤ S_{2k+1}(x)` for `x ≥ 0`. -/
theorem sin_le_sinTaylorSum_odd (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ sinTaylorSum (2 * k + 1) x := by
  have h := (sinCos_alternating_remainder_nonneg (2 * k + 1) (by omega) hx).2
  rw [Odd.neg_one_pow ⟨k, rfl⟩] at h
  linarith

/-- `S_{2k+2}(x) ≤ sin x` for `x ≥ 0`. -/
theorem sinTaylorSum_even_le_sin (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    sinTaylorSum (2 * k + 2) x ≤ Real.sin x := by
  have h := (sinCos_alternating_remainder_nonneg (2 * k + 2) (by omega) hx).2
  rw [Even.neg_one_pow ⟨k + 1, by ring⟩] at h
  linarith

end GaloisForLFunctions.HTGeometry
