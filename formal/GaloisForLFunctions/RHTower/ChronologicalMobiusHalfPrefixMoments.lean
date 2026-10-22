import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO
import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicPartial
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# Möbius moments of the half-length prefix

With `M = ⌊N/2⌋` and the unconditional prime number theorem in the forms
`Σ_{k ≤ X} μ(k) = o(X)` and `Σ_{k ≤ X} μ(k)/k → 0`:

* `Σ_{k ≤ M} μ(k)/k → 0`;
* `N⁻¹ Σ_{k ≤ M} μ(k) (k/N)^p → 0` for every `p ≥ 0`.

The second follows from Abel's monotone-weight inequality
`|Σ_{k ≤ M} u_k w_k| ≤ 2 S W` for nondecreasing weights `0 ≤ w_k ≤ W` and partial sums
`|Σ_{k ≤ n} u_k| ≤ S` (`n ≤ M`), together with `max_{n ≤ M} |Σ_{k ≤ n} μ(k)| = o(M)`.
-/

open Filter Topology ArithmeticFunction
open scoped Moebius

noncomputable section

namespace RHTower

/-- **Summation by parts.** `Σ_{k ≤ M} u_k w_k = U_M w_M - Σ_{k ≤ M} U_{k-1} (w_k - w_{k-1})`. -/
theorem sum_Ioc_mul_eq_by_parts (u w : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Ioc 0 M, u k * w k =
      (∑ k ∈ Finset.Ioc 0 M, u k) * w M -
        ∑ k ∈ Finset.Ioc 0 M, (∑ j ∈ Finset.Ioc 0 (k - 1), u j) * (w k - w (k - 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le M), ih, Finset.sum_Ioc_succ_top (Nat.zero_le M),
      Finset.sum_Ioc_succ_top (Nat.zero_le M), Nat.add_sub_cancel]
    ring

theorem sum_Ioc_sub_pred (w : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Ioc 0 M, (w k - w (k - 1)) = w M - w 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le M), ih, Nat.add_sub_cancel]; ring

/-- **Abel's monotone-weight inequality.** -/
theorem abs_sum_Ioc_mul_le_of_monotone {u w : ℕ → ℝ} {M : ℕ} {S W : ℝ}
    (hmono : ∀ k, 1 ≤ k → k ≤ M → w (k - 1) ≤ w k) (hw0 : 0 ≤ w 0) (hwM : w M ≤ W)
    (hU : ∀ n ≤ M, |∑ k ∈ Finset.Ioc 0 n, u k| ≤ S) :
    |∑ k ∈ Finset.Ioc 0 M, u k * w k| ≤ 2 * S * W := by
  have hS : 0 ≤ S := (abs_nonneg _).trans (hU 0 (Nat.zero_le M))
  have hwM0 : 0 ≤ w M := by
    have hmon : ∀ n ≤ M, w 0 ≤ w n := by
      intro n hn
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact (ih (by omega)).trans (by simpa using hmono (n + 1) (by omega) hn)
    exact hw0.trans (hmon M le_rfl)
  rw [sum_Ioc_mul_eq_by_parts]
  have hterm : ∀ k ∈ Finset.Ioc 0 M,
      |(∑ j ∈ Finset.Ioc 0 (k - 1), u j) * (w k - w (k - 1))| ≤ S * (w k - w (k - 1)) := by
    intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Ioc.mp hk
    have hd : 0 ≤ w k - w (k - 1) := sub_nonneg.mpr (hmono k hk1 hkM)
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right (hU (k - 1) (by omega)) hd
  calc |(∑ k ∈ Finset.Ioc 0 M, u k) * w M -
        ∑ k ∈ Finset.Ioc 0 M, (∑ j ∈ Finset.Ioc 0 (k - 1), u j) * (w k - w (k - 1))|
      ≤ |(∑ k ∈ Finset.Ioc 0 M, u k) * w M| +
          ∑ k ∈ Finset.Ioc 0 M, |(∑ j ∈ Finset.Ioc 0 (k - 1), u j) * (w k - w (k - 1))| :=
        (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ S * W + S * (w M - w 0) := by
        refine add_le_add ?_ ((Finset.sum_le_sum hterm).trans_eq ?_)
        · rw [abs_mul, abs_of_nonneg hwM0]
          exact mul_le_mul (hU M le_rfl) hwM hwM0 hS
        · rw [← Finset.mul_sum, sum_Ioc_sub_pred]
    _ ≤ 2 * S * W := by nlinarith

/-- The Mertens function over `Ioc`. -/
theorem sum_Ioc_moebius_eq_range (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 n, ((μ k : ℤ) : ℝ) = ∑ k ∈ Finset.range (n + 1), ((μ k : ℤ) : ℝ) := by
  refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Finset.mem_Ioc.mp hk).2)) fun k hk hk' => ?_
  have : k = 0 := by
    by_contra h0
    exact hk' (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩)
  subst this; simp

/-- **Mertens is `o(n)` along the integers.** -/
theorem tendsto_abs_sum_moebius_div :
    Tendsto (fun n : ℕ => |∑ k ∈ Finset.Ioc 0 n, ((μ k : ℤ) : ℝ)| / n) atTop (𝓝 0) := by
  have h := Sieve.tendsto_norm_sum_moebius_div.comp tendsto_natCast_atTop_atTop
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.floor_natCast]
  rw [sum_Ioc_moebius_eq_range]
  congr 1
  rw [show (∑ k ∈ Finset.range (n + 1), (μ k : ℂ)) =
      ((∑ k ∈ Finset.range (n + 1), ((μ k : ℤ) : ℝ) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The running maximum of the Mertens function is `o(M)`.** -/
theorem exists_abs_sum_moebius_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M n : ℕ, n ≤ M → |∑ k ∈ Finset.Ioc 0 n, ((μ k : ℤ) : ℝ)| ≤ C + ε * M := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((tendsto_abs_sum_moebius_div.eventually (gt_mem_nhds hε)))
  refine ⟨n₀, Nat.cast_nonneg _, fun M n hnM => ?_⟩
  have hsmall : |∑ k ∈ Finset.Ioc 0 n, ((μ k : ℤ) : ℝ)| ≤ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ioc 0 n, |((μ k : ℤ) : ℝ)| ≤ ∑ _k ∈ Finset.Ioc 0 n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by exact_mod_cast abs_moebius_le_one
      _ = n := by simp
  have hM : (n : ℝ) ≤ M := by exact_mod_cast hnM
  rcases lt_or_ge n n₀ with hlt | hge
  · have : (n : ℝ) ≤ n₀ := by exact_mod_cast hlt.le
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg M)]
  · have h := hn₀ n hge
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp; positivity
    have hnr : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [div_lt_iff₀ hnr] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) n₀]

/-- **Half-prefix Möbius moments.** `N⁻¹ Σ_{k ≤ ⌊N/2⌋} μ(k) (k/N)^p → 0` for every `p ≥ 0`. -/
theorem tendsto_halfPrefix_moebius_pow (p : ℕ) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) *
      ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * ((k : ℝ) / N) ^ p) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := exists_abs_sum_moebius_le (ε / 8) (by positivity)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 * C / ε)
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound := abs_sum_Ioc_mul_le_of_monotone (u := fun k => ((μ k : ℤ) : ℝ))
    (w := fun k => ((k : ℝ) / N) ^ p) (M := N / 2) (S := C + ε / 8 * (N / 2 : ℕ)) (W := 1)
    (fun k hk _ => by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1) hNpos.le)
    (by positivity)
    (by
      apply pow_le_one₀ (by positivity)
      rw [div_le_one hNpos]; exact_mod_cast Nat.div_le_self N 2)
    (fun n hn => hC (N / 2) n hn)
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  have hhalf : ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N 2
  have hNbig : 8 * C / ε < N := hN₁.trans (by exact_mod_cast (by omega : N₁ < N))
  have hC' : C < ε / 8 * N := by
    rw [div_lt_iff₀ hε] at hNbig; linarith
  calc 1 / (N : ℝ) * |∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * ((k : ℝ) / N) ^ p|
      ≤ 1 / N * (2 * (C + ε / 8 * (N / 2 : ℕ)) * 1) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 1 / N * (2 * (ε / 8 * N + ε / 8 * N)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hhalf (by positivity : (0 : ℝ) ≤ ε / 8)]
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

/-- **The harmonic Möbius sum of the half prefix tends to zero.** -/
theorem tendsto_halfPrefix_moebius_harmonic :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k) atTop (𝓝 0) := by
  have h := deningerHarmonicPartial_tendsto
  rw [deningerHarmonicLimit_eq_zero] at h
  have hdiv : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  refine (h.comp hdiv).congr fun N => ?_
  simp only [Function.comp_apply, deningerHarmonicPartial]
  refine (Finset.sum_subset (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Finset.mem_Ioc.mp hk).2)) fun k hk hk' => ?_).symm
  have : k = 0 := by
    by_contra h0
    exact hk' (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩)
  subst this; simp

end RHTower
