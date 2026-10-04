import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivatives of `L(1/p)` and the Lah numbers

For a function `L` all of whose iterated derivatives are differentiable and `z = 1/p`, `p > 0`,

`(-1)^n (d/dp)^n L(1/p) = Σ_{k=0}^{n} L(n,k) z^{n+k} L^{(k)}(z)`,

where the unsigned Lah numbers satisfy `L(n+1,k+1) = (n+k+1) L(n,k+1) + L(n,k)` and, for
`n, k ≥ 0`, `L(n+1,k+1) (k+1)! = C(n,k) (n+1)!`.  The recurrence is the effect of `-d/dp = z² d/dz`
on `z^{n+k} L^{(k)}(z)`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Unsigned Lah numbers. -/
def lahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (n + k + 1) * lahNumber n (k + 1) + lahNumber n k

@[simp] theorem lahNumber_zero_zero : lahNumber 0 0 = 1 := rfl

@[simp] theorem lahNumber_zero_succ (k : ℕ) : lahNumber 0 (k + 1) = 0 := rfl

@[simp] theorem lahNumber_succ_zero (n : ℕ) : lahNumber (n + 1) 0 = 0 := rfl

theorem lahNumber_succ_succ (n k : ℕ) :
    lahNumber (n + 1) (k + 1) = (n + k + 1) * lahNumber n (k + 1) + lahNumber n k := rfl

theorem lahNumber_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → lahNumber n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [lahNumber_succ_succ, lahNumber_eq_zero_of_lt (by omega : n < k + 1),
      lahNumber_eq_zero_of_lt (by omega : n < k), mul_zero]

theorem lahNumber_zero_right_mul (n : ℕ) : lahNumber n 0 * n = 0 := by
  cases n <;> simp

/-- **Closed form.**  `L(n+1,k+1) (k+1)! = C(n,k) (n+1)!`. -/
theorem lahNumber_succ_succ_mul_factorial : ∀ n k : ℕ,
    lahNumber (n + 1) (k + 1) * (k + 1).factorial = n.choose k * (n + 1).factorial
  | 0, 0 => rfl
  | 0, k + 1 => by simp [lahNumber_succ_succ]
  | n + 1, 0 => by
    have ih := lahNumber_succ_succ_mul_factorial n 0
    simp only [Nat.factorial_one, mul_one, Nat.choose_zero_right, one_mul, zero_add] at ih ⊢
    rw [lahNumber_succ_succ, lahNumber_succ_zero, add_zero, ih, Nat.factorial_succ (n + 1)]
  | n + 1, k + 1 => by
    have ih1 := lahNumber_succ_succ_mul_factorial n (k + 1)
    have ih0 := lahNumber_succ_succ_mul_factorial n k
    have hc := Nat.choose_succ_right_eq n k
    rw [lahNumber_succ_succ, Nat.choose_succ_succ', Nat.factorial_succ (n + 1)]
    rw [Nat.factorial_succ (k + 1)] at ih1 ⊢
    have e1 : ((n + 1 + (k + 1) + 1) * lahNumber (n + 1) (k + 1 + 1) + lahNumber (n + 1) (k + 1)) *
        ((k + 1 + 1) * (k + 1).factorial) =
          (n + k + 3) * (lahNumber (n + 1) (k + 1 + 1) * ((k + 1 + 1) * (k + 1).factorial)) +
            (k + 2) * (lahNumber (n + 1) (k + 1) * (k + 1).factorial) := by ring
    rw [e1, ih1, ih0]
    rcases le_or_gt k n with hkn | hkn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rw [Nat.add_sub_cancel_left] at hc
      nlinarith [hc]
    · rw [Nat.choose_eq_zero_of_lt hkn, Nat.choose_eq_zero_of_lt (by omega : k + 1 > n)]
      ring

/-- `d/dp (1/p)^j = -j (1/p)^{j+1}`. -/
theorem hasDerivAt_inv_pow (j : ℕ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun q : ℝ => q⁻¹ ^ j) (-((j : ℝ) * p⁻¹ ^ (j + 1))) p := by
  refine ((hasDerivAt_inv hp).fun_pow j).congr_deriv ?_
  rcases j with _ | j
  · simp
  · rw [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, ← inv_pow p 2]
    ring

/-- The Lah sum `S_n(p) = Σ_{k ≤ n} L(n,k) z^{n+k} L^{(k)}(z)`, `z = 1/p`. -/
def lahInverseSum (L : ℝ → ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) * p⁻¹ ^ (n + k) * iteratedDeriv k L p⁻¹

theorem lahInverseSum_succ_eq (L : ℝ → ℝ) (n : ℕ) (p : ℝ) :
    lahInverseSum L (n + 1) p = ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) *
      (((n : ℝ) + k) * p⁻¹ ^ (n + k + 1) * iteratedDeriv k L p⁻¹ +
        p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹) := by
  have hA : ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) * ((n : ℝ) + k) * p⁻¹ ^ (n + k + 1) *
      iteratedDeriv k L p⁻¹ = ∑ k ∈ range (n + 1), (lahNumber n (k + 1) : ℝ) * ((n : ℝ) + k + 1) *
        p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹ := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ _ n,
      lahNumber_eq_zero_of_lt (Nat.lt_succ_self n)]
    have h0 : (lahNumber n 0 : ℝ) * ((n : ℝ) + ((0 : ℕ) : ℝ)) = 0 := by
      rw [Nat.cast_zero, add_zero]; exact_mod_cast lahNumber_zero_right_mul n
    rw [h0]
    simp only [zero_mul, add_zero, Nat.cast_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  calc lahInverseSum L (n + 1) p = ∑ k ∈ range (n + 1), ((lahNumber n (k + 1) : ℝ) *
        ((n : ℝ) + k + 1) * p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹ +
          (lahNumber n k : ℝ) * p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹) := by
        unfold lahInverseSum
        rw [Finset.sum_range_succ']
        simp only [lahNumber_succ_zero, Nat.cast_zero, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lahNumber_succ_succ]; push_cast; ring
    _ = ∑ k ∈ range (n + 1), (lahNumber n (k + 1) : ℝ) * ((n : ℝ) + k + 1) * p⁻¹ ^ (n + k + 2) *
          iteratedDeriv (k + 1) L p⁻¹ + ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) *
            p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹ := Finset.sum_add_distrib
    _ = _ := by
        rw [← hA, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem hasDerivAt_lahInverseSum {L : ℝ → ℝ} (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L))
    (n : ℕ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (lahInverseSum L n) (-lahInverseSum L (n + 1) p) p := by
  have hterm : ∀ k ∈ range (n + 1), HasDerivAt
      (fun q => (lahNumber n k : ℝ) * q⁻¹ ^ (n + k) * iteratedDeriv k L q⁻¹)
      (-((lahNumber n k : ℝ) * (((n : ℝ) + k) * p⁻¹ ^ (n + k + 1) * iteratedDeriv k L p⁻¹ +
        p⁻¹ ^ (n + k + 2) * iteratedDeriv (k + 1) L p⁻¹))) p := by
    intro k _
    have h1 := hasDerivAt_inv_pow (n + k) hp
    have h2 : HasDerivAt (fun q : ℝ => iteratedDeriv k L q⁻¹)
        (iteratedDeriv (k + 1) L p⁻¹ * (-(p ^ 2)⁻¹)) p := by
      have hd := ((hL k) p⁻¹).hasDerivAt
      rw [← iteratedDeriv_succ] at hd
      exact hd.comp p (hasDerivAt_inv hp)
    have h := (h1.fun_mul h2).const_mul (lahNumber n k : ℝ)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by ring)).congr_deriv ?_
    rw [← inv_pow p 2]
    push_cast
    ring
  have hsum := HasDerivAt.fun_sum hterm
  rw [lahInverseSum_succ_eq, ← Finset.sum_neg_distrib]
  exact hsum

/-- **Lah formula.**  For `p > 0`,
`(-1)^n (d/dp)^n L(1/p) = Σ_{k ≤ n} L(n,k) p^{-(n+k)} L^{(k)}(1/p)`. -/
theorem neg_one_pow_mul_iteratedDeriv_comp_inv {L : ℝ → ℝ}
    (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L)) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    (-1) ^ n * iteratedDeriv n (fun q => L q⁻¹) p = lahInverseSum L n p := by
  induction n generalizing p with
  | zero => simp [lahInverseSum]
  | succ n ih =>
    have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    have hev : iteratedDeriv n (fun q => L q⁻¹) =ᶠ[nhds p]
        fun q => (-1) ^ n * lahInverseSum L n q := by
      filter_upwards [Ioi_mem_nhds hp] with q hq
      rw [← ih hq, ← mul_assoc, hsq, one_mul]
    rw [iteratedDeriv_succ, hev.deriv_eq,
      ((hasDerivAt_lahInverseSum hL n hp.ne').const_mul ((-1) ^ n)).deriv, pow_succ]
    linear_combination (lahInverseSum L (n + 1) p) * hsq

/-- The Lah formula with the closed-form coefficients
`L(n+1,k+1) = C(n,k) (n+1)!/(k+1)!`. -/
theorem neg_one_pow_mul_iteratedDeriv_comp_inv_eq_choose {L : ℝ → ℝ}
    (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L)) (n : ℕ) {p : ℝ} (hp : 0 < p) :
    (-1) ^ (n + 1) * iteratedDeriv (n + 1) (fun q => L q⁻¹) p =
      ∑ k ∈ range (n + 1), ((n + 1).factorial : ℝ) / ((k + 1).factorial : ℝ) * (n.choose k : ℝ) *
        p⁻¹ ^ (n + 1 + (k + 1)) * iteratedDeriv (k + 1) L p⁻¹ := by
  rw [neg_one_pow_mul_iteratedDeriv_comp_inv hL (n + 1) hp, lahInverseSum, Finset.sum_range_succ',
    lahNumber_succ_zero, Nat.cast_zero, zero_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := lahNumber_succ_succ_mul_factorial n k
  have hf : ((k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hl : (lahNumber (n + 1) (k + 1) : ℝ) = ((n + 1).factorial : ℝ) / ((k + 1).factorial : ℝ) *
      (n.choose k : ℝ) := by
    rw [div_mul_eq_mul_div, eq_div_iff hf]
    exact_mod_cast h.trans (mul_comm _ _)
  rw [hl]

/-- **Third order.**  `-(d/dp)^3 L(1/p) = z^4 (6 L⁽¹⁾(z) + 6 z L⁽²⁾(z) + z² L⁽³⁾(z))`,
`z = 1/p`. -/
theorem neg_iteratedDeriv_three_comp_inv {L : ℝ → ℝ}
    (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L)) {p : ℝ} (hp : 0 < p) :
    -iteratedDeriv 3 (fun q => L q⁻¹) p = p⁻¹ ^ 4 * (6 * iteratedDeriv 1 L p⁻¹ +
      6 * p⁻¹ * iteratedDeriv 2 L p⁻¹ + p⁻¹ ^ 2 * iteratedDeriv 3 L p⁻¹) := by
  have h := neg_one_pow_mul_iteratedDeriv_comp_inv hL 3 hp
  simp only [lahInverseSum, Finset.sum_range_succ, Finset.sum_range_zero] at h
  have l30 : lahNumber 3 0 = 0 := rfl
  have l31 : lahNumber 3 1 = 6 := rfl
  have l32 : lahNumber 3 2 = 6 := rfl
  have l33 : lahNumber 3 3 = 1 := rfl
  rw [l30, l31, l32, l33] at h
  push_cast at h
  linear_combination h

/-- **Lah recurrence on sums.**  For every sequence `T`,
`Σ_{k ≤ n+1} L(n+1,k) T_k = Σ_{k ≤ n} L(n,k) ((n+k) T_k + T_{k+1})`. -/
theorem sum_lahNumber_succ (n : ℕ) (T : ℕ → ℝ) :
    ∑ k ∈ range (n + 2), (lahNumber (n + 1) k : ℝ) * T k =
      ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) * (((n : ℝ) + k) * T k + T (k + 1)) := by
  have hA : ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) * ((n : ℝ) + k) * T k =
      ∑ k ∈ range (n + 1), (lahNumber n (k + 1) : ℝ) * ((n : ℝ) + k + 1) * T (k + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ _ n,
      lahNumber_eq_zero_of_lt (Nat.lt_succ_self n)]
    have h0 : (lahNumber n 0 : ℝ) * ((n : ℝ) + ((0 : ℕ) : ℝ)) = 0 := by
      rw [Nat.cast_zero, add_zero]; exact_mod_cast lahNumber_zero_right_mul n
    rw [h0]
    simp only [zero_mul, add_zero, Nat.cast_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [Finset.sum_range_succ', lahNumber_succ_zero, Nat.cast_zero, zero_mul, add_zero]
  calc ∑ k ∈ range (n + 1), (lahNumber (n + 1) (k + 1) : ℝ) * T (k + 1) =
      ∑ k ∈ range (n + 1), ((lahNumber n (k + 1) : ℝ) * ((n : ℝ) + k + 1) * T (k + 1) +
        (lahNumber n k : ℝ) * T (k + 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lahNumber_succ_succ]; push_cast; ring
    _ = _ := by
        rw [Finset.sum_add_distrib, ← hA, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- The cumulant Lah sum `L_n(z) = Σ_{k ≤ n} L(n,k) z^k L^{(k)}(z)`. -/
def lahCumulantSum (L : ℝ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (lahNumber n k : ℝ) * z ^ k * iteratedDeriv k L z

theorem hasDerivAt_lahCumulantSum {L : ℝ → ℝ} (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L))
    (n : ℕ) (z : ℝ) :
    HasDerivAt (lahCumulantSum L n) (∑ k ∈ range (n + 1), (lahNumber n k : ℝ) *
      ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k L z + z ^ k * iteratedDeriv (k + 1) L z)) z := by
  have hterm : ∀ k ∈ range (n + 1), HasDerivAt
      (fun y => (lahNumber n k : ℝ) * y ^ k * iteratedDeriv k L y)
      ((lahNumber n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * iteratedDeriv k L z +
        z ^ k * iteratedDeriv (k + 1) L z)) z := by
    intro k _
    have hd := ((hL k) z).hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    have h := ((hasDerivAt_pow k z).fun_mul hd).const_mul (lahNumber n k : ℝ)
    exact (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)).congr_deriv
      (by ring)
  exact HasDerivAt.fun_sum hterm

/-- **Cumulant Lah recurrence.**  `L_{n+1} = n L_n + z L_n'`. -/
theorem lahCumulantSum_succ {L : ℝ → ℝ} (hL : ∀ k, Differentiable ℝ (iteratedDeriv k L))
    (n : ℕ) (z : ℝ) :
    lahCumulantSum L (n + 1) z = n * lahCumulantSum L n z + z * deriv (lahCumulantSum L n) z := by
  rw [(hasDerivAt_lahCumulantSum hL n z).deriv]
  unfold lahCumulantSum
  have hl : ∑ k ∈ range (n + 1 + 1), (lahNumber (n + 1) k : ℝ) * z ^ k * iteratedDeriv k L z =
      ∑ k ∈ range (n + 2), (lahNumber (n + 1) k : ℝ) * (z ^ k * iteratedDeriv k L z) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hl, sum_lahNumber_succ n (fun k => z ^ k * iteratedDeriv k L z)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases k with _ | k
  · simp; ring
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    ring

/-- `(-1)^n (d/dp)^n L(1/p) = z^n L_n(z)` at `z = 1/p`. -/
theorem lahInverseSum_inv_eq (L : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    lahInverseSum L n z⁻¹ = z ^ n * lahCumulantSum L n z := by
  unfold lahInverseSum lahCumulantSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_inv, pow_add]
  ring

end GaloisForLFunctions.HTGeometry
