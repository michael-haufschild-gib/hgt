import GaloisForLFunctions.RHTower.Sieve.DirichletBlockStandardOrder

/-!
# The window always contains an integer order

Read as a condition on `k` at a fixed height, the halved window of
`dirichlet_block_saves_half` is

```text
u + 1/2 + e  ≤  k  ≤  u + 7/4,        u = log T / log M,
```

where `e = k·log(4k)/log M` is the order's own weight.  Its length is `5/4 − e`, so as soon as the
weight costs at most a quarter the interval is longer than one and contains an integer.  This is
exactly what fails at the unhalved saving `ρ = 2^{-k}`, where the length is only about `1/2`.
-/

namespace RHTower.Sieve

/-- **An integer order exists in the window.**  The ceiling of the left end works, and it is at
least two once `u ≥ 1`. -/
theorem exists_order_in_window {u e : ℝ} (hu : 1 ≤ u) (he0 : 0 ≤ e) (he : e ≤ 1 / 4) :
    ∃ k : ℕ, 2 ≤ k ∧ u + 1 / 2 + e ≤ (k : ℝ) ∧ (k : ℝ) ≤ u + 7 / 4 := by
  have harg : (0 : ℝ) ≤ u + 1 / 2 + e := by linarith
  refine ⟨⌈u + 1 / 2 + e⌉₊, ?_, Nat.le_ceil _, ?_⟩
  · -- the ceiling is at least `⌈3/2⌉ = 2`
    have hge : (2 : ℝ) ≤ u + 1 / 2 + e + 1 / 2 := by linarith
    have hceil : u + 1 / 2 + e ≤ (⌈u + 1 / 2 + e⌉₊ : ℝ) := Nat.le_ceil _
    by_contra hlt
    push_neg at hlt
    have : (⌈u + 1 / 2 + e⌉₊ : ℝ) ≤ 1 := by
      have : ⌈u + 1 / 2 + e⌉₊ ≤ 1 := by omega
      exact_mod_cast this
    linarith
  · have h := Nat.ceil_lt_add_one harg
    linarith

/-! ## Transferring between powers of `M` and the ratio `log T / log M`

The window is stated as powers of the block's scale, the order choice as an inequality between
real numbers.  These three lemmas move between the two. -/

/-- A power of `M` is below `T` once its exponent is below `log T / log M`. -/
theorem rpow_le_of_le_log_div {M T a : ℝ} (hM : 1 < M) (hT : 0 < T)
    (h : a ≤ Real.log T / Real.log M) : M ^ a ≤ T := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog : (0 : ℝ) < Real.log M := Real.log_pos hM
  rw [Real.rpow_def_of_pos hM0]
  have hmul : Real.log M * a ≤ Real.log T := by
    rw [le_div_iff₀ hlog] at h
    linarith [h]
  calc Real.exp (Real.log M * a) ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr hmul
    _ = T := Real.exp_log hT

/-- `T` is below a power of `M` once `log T / log M` is below its exponent. -/
theorem le_rpow_of_log_div_le {M T a : ℝ} (hM : 1 < M) (hT : 0 < T)
    (h : Real.log T / Real.log M ≤ a) : T ≤ M ^ a := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog : (0 : ℝ) < Real.log M := Real.log_pos hM
  rw [Real.rpow_def_of_pos hM0]
  have hmul : Real.log T ≤ Real.log M * a := by
    rw [div_le_iff₀ hlog] at h
    linarith [h]
  calc T = Real.exp (Real.log T) := (Real.exp_log hT).symm
    _ ≤ Real.exp (Real.log M * a) := Real.exp_le_exp.mpr hmul

/-- The weighted form: the order's own weight `A` enters as `log A / log M`. -/
theorem mul_le_rpow_of_log_div_le {M T A a : ℝ} (hM : 1 < M) (hT : 0 < T) (hA : 0 < A)
    (h : Real.log T / Real.log M + Real.log A / Real.log M ≤ a) : T * A ≤ M ^ a := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog : (0 : ℝ) < Real.log M := Real.log_pos hM
  have hsum : Real.log T + Real.log A ≤ Real.log M * a := by
    have h1 : (Real.log T + Real.log A) / Real.log M ≤ a := by
      rw [add_div]
      exact h
    rw [div_le_iff₀ hlog] at h1
    linarith [h1]
  rw [Real.rpow_def_of_pos hM0]
  calc T * A = Real.exp (Real.log T + Real.log A) := by
        rw [Real.exp_add, Real.exp_log hT, Real.exp_log hA]
    _ ≤ Real.exp (Real.log M * a) := Real.exp_le_exp.mpr hsum

end RHTower.Sieve
