import GaloisForLFunctions.RigidArithmeticOfCuts.TheCutIdentity
import GaloisForLFunctions.RigidArithmeticOfCuts.NoUniformMeasureOnTheIntegers

/-!
# A cut vector with a monotone tail vanishes

The **cut defect** of a function `W` on the positive integers at level `k` is
`Σ_{r ≤ kJ} W(r) − k Σ_{j ≤ J} W(kj)`, and `W` is a **kernel vector** when it tends to `0` for all `k`.

Let `W = 1/r − T(r)` with `T` nonincreasing. Then `W − 1/r` is nondecreasing, so a value at a multiple
`kj` is at most the average of `W` on the next block, up to `1/(k j²)`. Summing over `j`, the cut defect
controls the partial sums: `Σ_{r < k} W(r) ≤ 2` for every `k`. So a nonnegative `W` of this form is
summable, and it vanishes because there is no uniform measure on the integers.

This is a Tauberian step with no analytic input: monotonicity of the tail replaces every estimate.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The cut defect of `W` at level `k`, truncated at `kJ`. -/
def cutDefect (W : ℕ → ℝ) (k J : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 (k * J), W r - (k : ℝ) * ∑ j ∈ Icc 1 J, W (k * j)

/-- `W` is a kernel vector of the cut system. -/
def IsCutKernel (W : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Tendsto (cutDefect W k) atTop (𝓝 0)

private lemma sum_inv_sq_le (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Icc 1 J, 1 / ((j : ℝ) ^ 2) ≤ 2 - 1 / (J : ℝ) := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ J hJ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
    have hkey : 1 / (((J + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (J : ℝ) - 1 / ((J + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hJR.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

variable {W : ℕ → ℝ}

/-- Monotonicity of `W − 1/r` across a gap. -/
private lemma le_add_inv_sub_inv (hmono : ∀ r, 1 ≤ r → W r - 1 / (r : ℝ) ≤ W (r + 1) - 1 / ((r + 1 : ℕ) : ℝ))
    {a r : ℕ} (ha : 1 ≤ a) (har : a ≤ r) : W a ≤ W r + 1 / (a : ℝ) - 1 / (r : ℝ) := by
  induction r, har using Nat.le_induction with
  | base => linarith
  | succ r har ih =>
    have := hmono r (by omega)
    linarith

/-- A value at a multiple is at most the block average. -/
private lemma mul_le_block (hmono : ∀ r, 1 ≤ r → W r - 1 / (r : ℝ) ≤ W (r + 1) - 1 / ((r + 1 : ℕ) : ℝ))
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (k : ℝ) * W (k * j) ≤ ∑ r ∈ Ico (k * j) (k * (j + 1)), W r + 1 / ((j : ℝ) ^ 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hcard : (Ico (k * j) (k * (j + 1))).card = k := by
    rw [Nat.card_Ico, Nat.mul_succ]; omega
  have hterm : ∀ r ∈ Ico (k * j) (k * (j + 1)),
      W (k * j) ≤ W r + 1 / ((k : ℝ) * (j : ℝ) ^ 2) := by
    intro r hr
    obtain ⟨h1, h2⟩ := mem_Ico.mp hr
    have ha : 1 ≤ k * j := Nat.mul_pos hk hj
    have hstep := le_add_inv_sub_inv hmono ha h1
    have hrR : (k : ℝ) * j ≤ r := by exact_mod_cast h1
    have hrR2 : (r : ℝ) ≤ (k : ℝ) * j + k := by
      have : r ≤ k * j + k := by rw [Nat.mul_succ] at h2; omega
      exact_mod_cast this
    have hapos : (0 : ℝ) < (k : ℝ) * j := by positivity
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le hapos hrR
    have hdiff : 1 / (((k * j : ℕ) : ℝ)) - 1 / (r : ℝ) ≤ 1 / ((k : ℝ) * (j : ℝ) ^ 2) := by
      push_cast
      rw [div_sub_div _ _ hapos.ne' hrpos.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hk2 : (r : ℝ) - (k : ℝ) * j ≤ k := by linarith
      have h3 : ((r : ℝ) - (k : ℝ) * j) * ((k : ℝ) * j) ≤ (k : ℝ) * r := by
        have h4 : (0 : ℝ) ≤ (k : ℝ) * j := hapos.le
        calc ((r : ℝ) - (k : ℝ) * j) * ((k : ℝ) * j) ≤ (k : ℝ) * ((k : ℝ) * j) :=
              mul_le_mul_of_nonneg_right hk2 h4
          _ ≤ (k : ℝ) * r := mul_le_mul_of_nonneg_left hrR hkR.le
      nlinarith [mul_nonneg hkR.le hjR.le, mul_pos hkR hjR]
    linarith
  have hsum : ∑ _r ∈ Ico (k * j) (k * (j + 1)), W (k * j) ≤
      ∑ r ∈ Ico (k * j) (k * (j + 1)), (W r + 1 / ((k : ℝ) * (j : ℝ) ^ 2)) :=
    sum_le_sum hterm
  rw [sum_const, hcard, nsmul_eq_mul, sum_add_distrib, sum_const, hcard, nsmul_eq_mul] at hsum
  have hval : (k : ℝ) * (1 / ((k : ℝ) * (j : ℝ) ^ 2)) = 1 / ((j : ℝ) ^ 2) := by field_simp
  rwa [hval] at hsum

private lemma sum_blocks (W : ℕ → ℝ) (k J : ℕ) :
    ∑ j ∈ Icc 1 J, ∑ r ∈ Ico (k * j) (k * (j + 1)), W r = ∑ r ∈ Ico k (k * (J + 1)), W r := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Icc_succ_top (by omega), ih,
      sum_Ico_consecutive _ (by nlinarith) (Nat.mul_le_mul_left k (by omega))]

private lemma Icc_one_eq_Ico (N : ℕ) : Icc 1 N = Ico 1 (N + 1) := by
  ext x
  simp only [mem_Icc, mem_Ico]
  omega

/-- **The partial sums of a kernel vector with a monotone tail are bounded above.** -/
theorem sum_Ico_one_le_two (hW1 : ∀ r, 1 ≤ r → W r ≤ 1 / (r : ℝ))
    (hmono : ∀ r, 1 ≤ r → W r - 1 / (r : ℝ) ≤ W (r + 1) - 1 / ((r + 1 : ℕ) : ℝ))
    (hcut : IsCutKernel W) {k : ℕ} (hk : 1 ≤ k) : ∑ r ∈ Ico 1 k, W r ≤ 2 := by
  have hbound : ∀ J : ℕ, 1 ≤ J →
      ∑ r ∈ Ico 1 k, W r - 2 - 1 / (J : ℝ) ≤ cutDefect W k J := by
    intro J hJ
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hblock : (k : ℝ) * ∑ j ∈ Icc 1 J, W (k * j) ≤
        ∑ r ∈ Ico k (k * (J + 1)), W r + 2 := by
      rw [mul_sum]
      have h1 : ∑ j ∈ Icc 1 J, (k : ℝ) * W (k * j) ≤
          ∑ j ∈ Icc 1 J, (∑ r ∈ Ico (k * j) (k * (j + 1)), W r + 1 / ((j : ℝ) ^ 2)) :=
        sum_le_sum fun j hj => mul_le_block hmono hk (mem_Icc.mp hj).1
      rw [sum_add_distrib, sum_blocks W] at h1
      have h2 := sum_inv_sq_le J hJ
      have h3 : (0 : ℝ) ≤ 1 / (J : ℝ) := by positivity
      linarith
    have hsplit1 : ∑ r ∈ Ico 1 (k * (J + 1)), W r =
        ∑ r ∈ Ico 1 k, W r + ∑ r ∈ Ico k (k * (J + 1)), W r :=
      (sum_Ico_consecutive _ hk (by nlinarith)).symm
    have hlt : k * J + 1 ≤ k * (J + 1) := by rw [Nat.mul_succ]; omega
    have hsplit2 : ∑ r ∈ Ico 1 (k * (J + 1)), W r =
        ∑ r ∈ Ico 1 (k * J + 1), W r + ∑ r ∈ Ico (k * J + 1) (k * (J + 1)), W r :=
      (sum_Ico_consecutive _ (by omega) hlt).symm
    have htail : ∑ r ∈ Ico (k * J + 1) (k * (J + 1)), W r ≤ 1 / (J : ℝ) := by
      have hc : (Ico (k * J + 1) (k * (J + 1))).card = k - 1 := by
        rw [Nat.card_Ico, Nat.mul_succ]; omega
      have hterm : ∀ r ∈ Ico (k * J + 1) (k * (J + 1)), W r ≤ 1 / ((k : ℝ) * J) := by
        intro r hr
        obtain ⟨h1, _⟩ := mem_Ico.mp hr
        have hr1 : 1 ≤ r := by omega
        refine (hW1 r hr1).trans ?_
        have hr2 : (k : ℝ) * J ≤ r := by
          have : k * J ≤ r := by omega
          exact_mod_cast this
        exact one_div_le_one_div_of_le (by positivity) hr2
      have hs := sum_le_sum hterm
      rw [sum_const, hc, nsmul_eq_mul] at hs
      refine hs.trans ?_
      have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by
        have : k - 1 ≤ k := Nat.sub_le k 1
        exact_mod_cast this
      calc ((k - 1 : ℕ) : ℝ) * (1 / ((k : ℝ) * J)) ≤ (k : ℝ) * (1 / ((k : ℝ) * J)) :=
            mul_le_mul_of_nonneg_right hk1 (by positivity)
        _ = 1 / (J : ℝ) := by field_simp
    rw [cutDefect, Icc_one_eq_Ico]
    linarith
  have hlim := hcut k hk
  have hlim' : Tendsto (fun J : ℕ => ∑ r ∈ Ico 1 k, W r - 2 - 1 / (J : ℝ)) atTop
      (𝓝 (∑ r ∈ Ico 1 k, W r - 2 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  have hle := le_of_tendsto_of_tendsto hlim' hlim
    (eventually_atTop.mpr ⟨1, fun J hJ => hbound J hJ⟩)
  linarith

/-- **Summability.** A nonnegative kernel vector with a monotone tail is summable. -/
theorem summable_of_cut_kernel (hW0 : W 0 = 0) (hnn : ∀ r, 1 ≤ r → 0 ≤ W r)
    (hW1 : ∀ r, 1 ≤ r → W r ≤ 1 / (r : ℝ))
    (hmono : ∀ r, 1 ≤ r → W r - 1 / (r : ℝ) ≤ W (r + 1) - 1 / ((r + 1 : ℕ) : ℝ))
    (hcut : IsCutKernel W) : Summable W := by
  refine summable_of_sum_range_le (c := 2) (fun r => ?_) (fun n => ?_)
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact hW0.ge
    · exact hnn r hr
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn, hW0, zero_add]
      exact sum_Ico_one_le_two hW1 hmono hcut hn

/-- One vanishing cut defect gives one uniform multiple. -/
theorem uniform_multiple_of_tendsto (hW : Summable W) (hW0 : W 0 = 0) {k : ℕ} (hk : 1 ≤ k)
    (hcut : Tendsto (cutDefect W k) atTop (𝓝 0)) : (k : ℝ) * ∑' t, W (k * t) = ∑' t, W t := by
  have hk0 : 0 < k := hk
  have hsk : Summable fun t => W (k * t) :=
    hW.comp_injective fun _ _ h => Nat.eq_of_mul_eq_mul_left hk0 h
  have h1 : Tendsto (fun J : ℕ => ∑ r ∈ Icc 1 (k * J), W r) atTop (𝓝 (∑' t, W t)) := by
    have hN : Tendsto (fun J : ℕ => k * J + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp (tendsto_id.const_mul_atTop' hk0)
    refine (hW.hasSum.tendsto_sum_nat.comp hN).congr fun J => ?_
    simp only [Function.comp]
    rw [sum_range_succ', sum_Icc_one_eq_sum_range, hW0, add_zero]
  have h2 : Tendsto (fun J : ℕ => ∑ j ∈ Icc 1 J, W (k * j)) atTop (𝓝 (∑' t, W (k * t))) := by
    refine ((hsk.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).congr fun J => ?_
    simp only [Function.comp]
    rw [sum_range_succ', sum_Icc_one_eq_sum_range, Nat.mul_zero, hW0, add_zero]
  have h3 := h1.sub (h2.const_mul (k : ℝ))
  have h4 := tendsto_nhds_unique h3 hcut
  linarith

/-- A summable kernel vector has uniform multiples. -/
theorem uniform_multiples_of_cut_kernel (hW : Summable W) (hW0 : W 0 = 0) (hcut : IsCutKernel W)
    {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) * ∑' t, W (k * t) = ∑' t, W t :=
  uniform_multiple_of_tendsto hW hW0 hk (hcut k hk)

/-- **A nonnegative kernel vector with a monotone tail is zero.** -/
theorem eq_zero_of_cut_kernel (hW0 : W 0 = 0) (hnn : ∀ r, 1 ≤ r → 0 ≤ W r)
    (hW1 : ∀ r, 1 ≤ r → W r ≤ 1 / (r : ℝ))
    (hmono : ∀ r, 1 ≤ r → W r - 1 / (r : ℝ) ≤ W (r + 1) - 1 / ((r + 1 : ℕ) : ℝ))
    (hcut : IsCutKernel W) {n : ℕ} (hn : 1 ≤ n) : W n = 0 :=
  have hW := summable_of_cut_kernel hW0 hnn hW1 hmono hcut
  eq_zero_of_uniform_multiples hW hW0
    (fun _ hk => uniform_multiples_of_cut_kernel hW hW0 hcut hk) hn

/-- **The summable kernel is trivial.** A summable kernel vector vanishes, with no sign on it. -/
theorem eq_zero_of_summable_cut_kernel (hW : Summable W) (hW0 : W 0 = 0) (hcut : IsCutKernel W)
    {n : ℕ} (hn : 1 ≤ n) : W n = 0 :=
  eq_zero_of_uniform_multiples hW hW0
    (fun _ hk => uniform_multiples_of_cut_kernel hW hW0 hcut hk) hn

end GaloisForLFunctions.RigidArithmeticOfCuts
