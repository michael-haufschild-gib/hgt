import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Character partial sums are bounded by the modulus; the Abel bound `‖L(σ,χ)‖ ≤ 3N`

For a nontrivial Dirichlet character `χ` modulo `N`, every complete period sums to zero, so every
partial sum `Σ_{m<n} χ(m)` is a partial period and has norm at most `N`.  Summation by parts then
bounds the absolutely convergent series `Σ χ(n) n^{-σ}` on the real axis `σ > 1` by `3N`, uniformly
in `σ`: the kernel `n ↦ n^{-σ}` is at most `1`, is decreasing with total variation at most `1` after
the first step, and the first step itself contributes `1`.

This is the conductor-uniform bound on the real axis that a values-based exceptional-zero argument
needs for the product character, where no pole and no strip estimate is available.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A complete period of a nontrivial character sums to zero. -/
theorem dirichletCharacter_sum_range_modulus (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∑ m ∈ Finset.range N, χ (m : ZMod N) = 0 := by
  have hbij : ∑ m ∈ Finset.range N, χ (m : ZMod N) = ∑ a : ZMod N, χ a := by
    refine Finset.sum_nbij' (fun m => (m : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro m _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro m hm; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro m _; rfl
  rw [hbij]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- A shifted complete period also sums to zero. -/
theorem dirichletCharacter_sum_range_shift (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (r : ℕ) :
    ∑ m ∈ Finset.range N, χ ((r + m : ℕ) : ZMod N) = 0 := by
  have hbij : ∑ m ∈ Finset.range N, χ ((r + m : ℕ) : ZMod N)
      = ∑ a : ZMod N, χ ((r : ZMod N) + a) := by
    refine Finset.sum_nbij' (fun m => (m : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro m _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro m hm; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro m _; push_cast; rfl
  rw [hbij, Fintype.sum_equiv (Equiv.addLeft (r : ZMod N)) (fun a => χ ((r : ZMod N) + a))
    (fun a => χ a) (fun a => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- Partial sums over `[0, N·q + r)` reduce to the partial period `[0, r)`. -/
theorem dirichletCharacter_sum_range_mul_add (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (q r : ℕ) :
    ∑ m ∈ Finset.range (N * q + r), χ (m : ZMod N) = ∑ m ∈ Finset.range r, χ (m : ZMod N) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : N * (q + 1) + r = (N * q + r) + N := by ring
    rw [hsplit, Finset.sum_range_add, ih]
    have hzero : ∑ x ∈ Finset.range N, χ (((N * q + r + x : ℕ)) : ZMod N) = 0 :=
      dirichletCharacter_sum_range_shift χ hχ (N * q + r)
    rw [hzero, add_zero]

/-- **Every character partial sum is bounded by the modulus.** -/
theorem norm_dirichletCharacter_sum_range_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ m ∈ Finset.range n, χ (m : ZMod N)‖ ≤ N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdecomp : n = N * (n / N) + n % N := (Nat.div_add_mod n N).symm
  rw [hdecomp, dirichletCharacter_sum_range_mul_add χ hχ]
  calc ‖∑ m ∈ Finset.range (n % N), χ (m : ZMod N)‖
      ≤ ∑ m ∈ Finset.range (n % N), ‖χ (m : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n % N), (1 : ℝ) :=
        Finset.sum_le_sum (fun m _ => DirichletCharacter.norm_le_one χ _)
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt n hN).le

/-- The real kernel `n ↦ n^{-σ}`, with the value `0` at `n = 0`. -/
def realPowerKernel (σ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-σ)

theorem realPowerKernel_zero {σ : ℝ} (hσ : σ ≠ 0) : realPowerKernel σ 0 = 0 := by
  simp [realPowerKernel, Real.zero_rpow (neg_ne_zero.mpr hσ)]

theorem realPowerKernel_one (σ : ℝ) : realPowerKernel σ 1 = 1 := by
  simp [realPowerKernel]

theorem realPowerKernel_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ realPowerKernel σ n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem realPowerKernel_le_one (σ : ℝ) (hσ : 0 ≤ σ) (n : ℕ) : realPowerKernel σ n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [realPowerKernel]
    rcases eq_or_ne σ 0 with rfl | h
    · simp
    · simp [Real.zero_rpow (neg_ne_zero.mpr h)]
  · unfold realPowerKernel
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = 1 := Real.rpow_zero _

/-- The kernel is nonincreasing from `n = 1` on. -/
theorem realPowerKernel_succ_le {σ : ℝ} (hσ : 0 ≤ σ) {n : ℕ} (hn : 1 ≤ n) :
    realPowerKernel σ (n + 1) ≤ realPowerKernel σ n := by
  unfold realPowerKernel
  have h0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  rw [Real.rpow_neg h0.le, Real.rpow_neg (by positivity)]
  have hpow : (n : ℝ) ^ σ ≤ ((n + 1 : ℕ) : ℝ) ^ σ := Real.rpow_le_rpow h0.le hle hσ
  have hposn : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos h0 σ
  exact inv_anti₀ hposn hpow

omit [NeZero N] in
/-- The complex Dirichlet term is the character value times the real kernel. -/
theorem LSeries_term_dirichletCharacter_eq (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : σ ≠ 0)
    (n : ℕ) :
    LSeries.term (fun m : ℕ => χ (m : ZMod N)) (σ : ℂ) n
      = ((realPowerKernel σ n : ℝ) : ℂ) * χ (n : ZMod N) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, realPowerKernel_zero hσ]
    simp
  · rw [LSeries.term_of_ne_zero hn, realPowerKernel]
    have hcast : (((n : ℝ) ^ (-σ) : ℝ) : ℂ) = ((n : ℝ) : ℂ) ^ ((-σ : ℝ) : ℂ) :=
      Complex.ofReal_cpow (Nat.cast_nonneg n) _
    rw [hcast]
    push_cast
    rw [Complex.cpow_neg, div_eq_mul_inv, mul_comm]

/-- Total variation of the kernel on `[0, M)`: the first step contributes `1`, the rest telescope. -/
theorem sum_abs_realPowerKernel_diff_le {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    ∑ i ∈ Finset.range M, |realPowerKernel σ (i + 1) - realPowerKernel σ i| ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 : |realPowerKernel σ (0 + 1) - realPowerKernel σ 0| = 1 := by
      rw [zero_add, realPowerKernel_one, realPowerKernel_zero hσ.ne']
      norm_num
    rw [h0]
    have htail : ∑ i ∈ Finset.range K, |realPowerKernel σ (i + 1 + 1) - realPowerKernel σ (i + 1)|
        = ∑ i ∈ Finset.range K, (realPowerKernel σ (i + 1) - realPowerKernel σ (i + 1 + 1)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (realPowerKernel_succ_le hσ.le (by omega)))]
    rw [htail, Finset.sum_range_sub' (fun i => realPowerKernel σ (i + 1)) K]
    have h1' : realPowerKernel σ (0 + 1) = 1 := realPowerKernel_one σ
    have h2 := realPowerKernel_nonneg σ (K + 1)
    linarith [h1', h2]

/-- Summation by parts against bounded partial sums: the weighted sum is controlled by the last
weight plus the total variation of the weights. -/
theorem norm_sum_ofReal_mul_le_of_bounded_partial {f : ℕ → ℝ} {g : ℕ → ℂ} {C : ℝ}
    (hG : ∀ k, ‖∑ j ∈ Finset.range k, g j‖ ≤ C) (hf : ∀ n, 0 ≤ f n) (M : ℕ) :
    ‖∑ i ∈ Finset.range M, ((f i : ℝ) : ℂ) * g i‖
      ≤ (f (M - 1) + ∑ i ∈ Finset.range (M - 1), |f (i + 1) - f i|) * C := by
  have h := Finset.sum_range_by_parts (fun n => ((f n : ℝ) : ℂ)) g M
  simp only [smul_eq_mul] at h
  rw [h]
  have hfnorm : ∀ n, ‖((f n : ℝ) : ℂ)‖ = f n := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (hf n)]
  have hfdiff : ∀ i, ‖((f (i + 1) : ℝ) : ℂ) - ((f i : ℝ) : ℂ)‖ = |f (i + 1) - f i| := by
    intro i
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hA : ‖((f (M - 1) : ℝ) : ℂ) * ∑ j ∈ Finset.range M, g j‖ ≤ f (M - 1) * C := by
    rw [norm_mul, hfnorm]
    exact mul_le_mul_of_nonneg_left (hG M) (hf _)
  have hB : ‖∑ i ∈ Finset.range (M - 1),
      (((f (i + 1) : ℝ) : ℂ) - ((f i : ℝ) : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖
        ≤ (∑ i ∈ Finset.range (M - 1), |f (i + 1) - f i|) * C := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul, hfdiff]
    exact mul_le_mul_of_nonneg_left (hG _) (abs_nonneg _)
  calc ‖((f (M - 1) : ℝ) : ℂ) * ∑ j ∈ Finset.range M, g j
        - ∑ i ∈ Finset.range (M - 1),
            (((f (i + 1) : ℝ) : ℂ) - ((f i : ℝ) : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖
      ≤ ‖((f (M - 1) : ℝ) : ℂ) * ∑ j ∈ Finset.range M, g j‖
        + ‖∑ i ∈ Finset.range (M - 1),
            (((f (i + 1) : ℝ) : ℂ) - ((f i : ℝ) : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖ :=
        norm_sub_le _ _
    _ ≤ f (M - 1) * C + (∑ i ∈ Finset.range (M - 1), |f (i + 1) - f i|) * C := add_le_add hA hB
    _ = (f (M - 1) + ∑ i ∈ Finset.range (M - 1), |f (i + 1) - f i|) * C := by ring

/-- Summation by parts: every partial sum of `Σ χ(n) n^{-σ}` is bounded by `3N`. -/
theorem norm_sum_range_LSeries_term_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, LSeries.term (fun m : ℕ => χ (m : ZMod N)) (σ : ℂ) n‖ ≤ 3 * N := by
  have hterm : ∀ n ∈ Finset.range M, LSeries.term (fun m : ℕ => χ (m : ZMod N)) (σ : ℂ) n
      = ((realPowerKernel σ n : ℝ) : ℂ) * χ (n : ZMod N) := by
    intro n _
    exact LSeries_term_dirichletCharacter_eq χ hσ.ne' n
  rw [Finset.sum_congr rfl hterm]
  have hmain := norm_sum_ofReal_mul_le_of_bounded_partial
    (fun k => norm_dirichletCharacter_sum_range_le χ hχ k) (realPowerKernel_nonneg σ) M
  have hker := realPowerKernel_le_one σ hσ.le (M - 1)
  have hvar := sum_abs_realPowerKernel_diff_le hσ (M - 1)
  calc ‖∑ i ∈ Finset.range M, ((realPowerKernel σ i : ℝ) : ℂ) * χ (i : ZMod N)‖
      ≤ (realPowerKernel σ (M - 1)
          + ∑ i ∈ Finset.range (M - 1), |realPowerKernel σ (i + 1) - realPowerKernel σ i|) * N :=
        hmain
    _ ≤ (1 + 2) * N := by gcongr
    _ = 3 * N := by ring

/-- **Abel bound on the real axis.**  For a nontrivial character modulo `N` and real `σ > 1`,
`‖L(σ,χ)‖ ≤ 3N`, uniformly in `σ`. -/
theorem norm_LFunction_le_three_mul_modulus (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ 3 * N := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ']
  have hsum : LSeriesSummable (fun m : ℕ => χ (m : ZMod N)) (σ : ℂ) :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr hσ'
  have htend := hsum.hasSum.tendsto_sum_nat
  refine le_of_tendsto' (htend.norm) (fun M => ?_)
  exact norm_sum_range_LSeries_term_le χ hχ (by linarith) M

end

end RHTower
