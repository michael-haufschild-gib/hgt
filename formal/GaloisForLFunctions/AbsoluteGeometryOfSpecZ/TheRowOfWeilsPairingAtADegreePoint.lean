import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsOffDiagonalIsContactsPlusJets
import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# The row of Weil's pairing at a degree point

Weil's pairing of two degree points is `Γ_m · Γ_n = contacts + jets`. Normalized by `mn`, the jets
are the kernel

  `Γ_m ·_∞ Γ_n / (mn) = ½ (1/|m − n| + 1/(m + n))`   (`jets_div_eq_jetKernel`),

a difference kernel plus Hilbert's matrix. The diagonal entry is missing. This file computes the
rows without it and their finite parts.

* **The jets row** (`sum_jetKernel_row`): for `1 ≤ n ≤ M`,
  `Σ_{m ≤ M, m ≠ n} ½(1/|m − n| + 1/(m + n)) = ½(H_{M−n} + H_{M+n}) − 3/(4n)`, with `H` the harmonic
  numbers.
* **Its finite part is Euler's constant** (`tendsto_sum_jetKernel_row_sub_log`): the row minus
  `log M` tends to `γ − 3/(4n)`. The `γ` of Weil's archimedean diagonal is the Euler constant of
  the harmonic row of the jets on the integer degree points.
* **The row of the diagonal graph** (`sum_pointCount_div`): for `M ≥ 1`,
  `Σ_{2 ≤ m ≤ M} N(m)/m = Σ_{m ≤ M} Λ(m)/m + H_M − 3/4 − 1/(2M(M+1))`.
* **Its finite part has no Euler constant** (`tendsto_sum_pointCount_div_sub`):
  `Σ_{2 ≤ m ≤ M} N(m)/m − 2 log M → −3/4`. The constant `+γ` of the cusp and the constant `−γ` of
  the primes (Mertens) cancel on the row of `Γ_1`.

So on the degree points the glued object of contacts and jets has an explicit finite part row by
row. It is a Robin mass of the degree point in the glued object; whether it is Weil's diagonal on
packets is the open question of the programme.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.SurfaceOfSpecZ

/-! ### Harmonic numbers -/

/-- The harmonic number `H_N = Σ_{k < N} 1/(k + 1)`. -/
def harm (N : ℕ) : ℝ := ∑ k ∈ range N, 1 / ((k : ℝ) + 1)

theorem harm_succ (N : ℕ) : harm (N + 1) = harm N + 1 / ((N : ℝ) + 1) :=
  Finset.sum_range_succ _ _

theorem harm_eq_harmonic (N : ℕ) : harm N = (harmonic N : ℝ) := by
  induction N with
  | zero => simp [harm]
  | succ n ih =>
    rw [harm_succ, ih, harmonic_succ]
    push_cast
    rw [one_div]

/-- `H_N − log N → γ`. -/
theorem tendsto_harm_sub_log :
    Tendsto (fun N : ℕ => harm N - Real.log N) atTop (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log.congr fun N => by rw [harm_eq_harmonic]

theorem Ico_succ_succ_eq_Ioc' (N M : ℕ) : Ico (N + 1) (M + 1) = Ioc N M := by
  ext k; simp only [mem_Ico, mem_Ioc]; omega

/-- `Σ_{k < M} 1/(n + k + 1) = H_{n+M} − H_n`. -/
theorem sum_range_inv_add (n M : ℕ) :
    ∑ k ∈ range M, 1 / ((n : ℝ) + k + 1) = harm (n + M) - harm n := by
  unfold harm
  rw [Finset.sum_range_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  rfl

/-- `Σ_{n < m ≤ M} 1/(m − n) = H_{M−n}`. -/
theorem sum_Ioc_inv_sub (n M : ℕ) : ∑ m ∈ Ioc n M, 1 / ((m : ℝ) - n) = harm (M - n) := by
  rw [← Ico_succ_succ_eq_Ioc', Finset.sum_Ico_eq_sum_range, Nat.add_sub_add_right, harm]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  congr 1
  ring

/-- `Σ_{1 ≤ m < n} 1/(n − m) = H_{n−1}`. -/
theorem sum_Ico_inv_sub (n : ℕ) : ∑ m ∈ Ico 1 n, 1 / ((n : ℝ) - m) = harm (n - 1) := by
  rw [Finset.sum_Ico_eq_sum_range, harm, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have h2 : (n - 1 - 1 - k) + k + 2 = n := by omega
  have h3 : (((n - 1 - 1 - k : ℕ)) : ℝ) + k + 2 = n := by exact_mod_cast h2
  push_cast
  congr 1
  linarith

/-! ### The jets kernel -/

/-- The normalized jets kernel `½(1/|m − n| + 1/(m + n))`. -/
def jetKernel (m n : ℕ) : ℝ := (1 / |(m : ℝ) - n| + 1 / ((m : ℝ) + n)) / 2

/-- **The jets, normalized by `mn`, are a difference kernel plus Hilbert's matrix.** -/
theorem jets_div_eq_jetKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    min (m : ℝ) n / (1 - (min (m : ℝ) n / max (m : ℝ) n) ^ 2) / ((m : ℝ) * n) = jetKernel m n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have h' : (m : ℝ) < n := by exact_mod_cast h
    have hd : (n : ℝ) - m ≠ 0 := by linarith
    have hd2 : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := by nlinarith
    rw [min_eq_left h'.le, max_eq_right h'.le, jetKernel, abs_of_neg (by linarith), neg_sub]
    field_simp
    ring
  · have h' : (n : ℝ) < m := by exact_mod_cast h
    have hd : (m : ℝ) - n ≠ 0 := by linarith
    have hd2 : (m : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by nlinarith
    rw [min_eq_right h'.le, max_eq_left h'.le, jetKernel, abs_of_pos (by linarith)]
    field_simp
    ring

/-- **The jets row without its diagonal entry.** -/
theorem sum_jetKernel_row {n M : ℕ} (hn : 1 ≤ n) (hM : n ≤ M) :
    ∑ m ∈ Ico 1 n, jetKernel m n + ∑ m ∈ Ioc n M, jetKernel m n =
      (harm (M - n) + harm (M + n)) / 2 - 3 / (4 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the two halves of the row
  have hlow : ∑ m ∈ Ico 1 n, jetKernel m n =
      (harm (n - 1) + ∑ m ∈ Ico 1 n, 1 / ((m : ℝ) + n)) / 2 := by
    rw [← sum_Ico_inv_sub, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt : (m : ℝ) < n := by exact_mod_cast (mem_Ico.mp hm).2
    rw [jetKernel, abs_of_neg (by linarith), neg_sub]
  have hupp : ∑ m ∈ Ioc n M, jetKernel m n =
      (harm (M - n) + ∑ m ∈ Ioc n M, 1 / ((m : ℝ) + n)) / 2 := by
    rw [← sum_Ioc_inv_sub, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt : (n : ℝ) < m := by exact_mod_cast (mem_Ioc.mp hm).1
    rw [jetKernel, abs_of_pos (by linarith)]
  -- the Hilbert part over the whole row
  have hall : ∑ m ∈ Ico 1 (M + 1), 1 / ((m : ℝ) + n) = harm (n + M) - harm n := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, ← sum_range_inv_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    congr 1
    ring
  have hsplit : ∑ m ∈ Ico 1 (M + 1), 1 / ((m : ℝ) + n) =
      ∑ m ∈ Ico 1 n, 1 / ((m : ℝ) + n) + (1 / ((n : ℝ) + n) + ∑ m ∈ Ioc n M, 1 / ((m : ℝ) + n)) := by
    rw [← Finset.sum_Ico_consecutive _ hn (by omega : n ≤ M + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : n < M + 1), Ico_succ_succ_eq_Ioc']
  have hstep : harm n = harm (n - 1) + 1 / (n : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [harm_succ, Nat.add_sub_cancel]
    push_cast
    rfl
  have hMn : harm (n + M) = harm (M + n) := by rw [add_comm]
  have h2n : 1 / ((n : ℝ) + n) = 1 / (2 * (n : ℝ)) := by rw [two_mul]
  have e1 : 1 / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by field_simp
  have e2 : 3 / (4 * (n : ℝ)) = 3 * (1 / (n : ℝ)) / 4 := by field_simp
  rw [hlow, hupp, e2]
  rw [hall, hMn, h2n, e1] at hsplit
  linarith

/-- **The finite part of the jets row is Euler's constant**: the row minus `log M` tends to
`γ − 3/(4n)`. -/
theorem tendsto_sum_jetKernel_row_sub_log {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun M : ℕ => ∑ m ∈ Ico 1 n, jetKernel m n + ∑ m ∈ Ioc n M, jetKernel m n -
      Real.log M) atTop (𝓝 (Real.eulerMascheroniConstant - 3 / (4 * (n : ℝ)))) := by
  have f1 : Tendsto (fun M : ℕ => harm (M - n) - Real.log ((M - n : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := tendsto_harm_sub_log.comp (tendsto_sub_atTop_nat n)
  have f2 : Tendsto (fun M : ℕ => harm (M + n) - Real.log ((M + n : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := tendsto_harm_sub_log.comp (tendsto_add_atTop_nat n)
  have g2 : Tendsto (fun M : ℕ => Real.log ((M + n : ℕ) : ℝ) - Real.log M) atTop (𝓝 0) := by
    have h := (Real.tendsto_log_comp_add_sub_log (n : ℝ)).comp tendsto_natCast_atTop_atTop
    refine h.congr fun M => ?_
    simp only [Function.comp_apply]
    push_cast
    rfl
  have g1 : Tendsto (fun M : ℕ => Real.log ((M - n : ℕ) : ℝ) - Real.log M) atTop (𝓝 0) := by
    have h := (Real.tendsto_log_comp_add_sub_log (-(n : ℝ))).comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop n] with M hM
    simp only [Function.comp_apply]
    rw [Nat.cast_sub hM]
    ring_nf
  have hlim := ((f1.add f2).div_const 2).add ((g1.add g2).div_const 2)
  have hlim' := hlim.sub_const (3 / (4 * (n : ℝ)))
  have hval : (Real.eulerMascheroniConstant + Real.eulerMascheroniConstant) / 2 + (0 + 0) / 2 -
      3 / (4 * (n : ℝ)) = Real.eulerMascheroniConstant - 3 / (4 * (n : ℝ)) := by ring
  rw [hval] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop n] with M hM
  rw [sum_jetKernel_row hn hM]
  ring

/-! ### The row of the diagonal graph -/

/-- **The row of `Γ_1`**: `Σ_{2 ≤ m ≤ M} N(m)/m = Σ_{m ≤ M} Λ(m)/m + H_M − 3/4 − 1/(2M(M+1))`. -/
theorem sum_pointCount_div {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 2 M, pointCount m / m =
      ∑ m ∈ Icc 1 M, Λ m / m + harm M - 3 / 4 - 1 / (2 * (M : ℝ) * ((M : ℝ) + 1)) := by
  induction M, hM using Nat.le_induction with
  | base => simp [harm]; norm_num
  | succ M hM ih =>
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1), Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
      ih, harm_succ, pointCount_eq (by omega : 2 ≤ M + 1)]
    have h1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [h1]
    have h2 : ((M : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith
    have h3 : (M : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- **The finite part of the row of the diagonal graph**: `Σ_{2 ≤ m ≤ M} N(m)/m − 2 log M → −3/4`.
The Euler constants of the cusp and of the primes cancel. -/
theorem tendsto_sum_pointCount_div_sub :
    Tendsto (fun M : ℕ => ∑ m ∈ Icc 2 M, pointCount m / m - 2 * Real.log M) atTop
      (𝓝 (-3 / 4)) := by
  have hΛ := _root_.RHTower.tendsto_sum_vonMangoldt_div_sub_log
  have hH := tendsto_harm_sub_log
  have hsmall : Tendsto (fun M : ℕ => 1 / (2 * (M : ℝ) * ((M : ℝ) + 1))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun M => by positivity) ?_
      tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_le_div_iff₀ (by positivity) hM0]
    nlinarith
  have hlim := ((hΛ.add hH).sub_const (3 / 4)).sub hsmall
  have hval : -Real.eulerMascheroniConstant + Real.eulerMascheroniConstant - 3 / 4 - 0 =
      -3 / 4 := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [sum_pointCount_div hM]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
