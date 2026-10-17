import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Powers and traces of infinite matrices with geometric decay

`M : ℕ → ℕ → ℂ` has geometric decay (`GeomDecay M C η`) when `|M i j| ≤ C η^i η^j`, `0 ≤ η < 1`.
Its truncation `trunc M N` is the `N × N` matrix of the first `N` indices.

* `fpow M N n` is the `n`-th power of the truncation, as a function on `ℕ × ℕ`
  (`trunc_pow_apply`), and `ipow M n` is the `n`-th power of `M`, both by recursion.
* `norm_fpow_succ_le`, `norm_ipow_succ_le`: `|M^{n+1}_{ij}| ≤ C (C S)^n η^i η^j`, `S = 1/(1 − η²)`.
* `tendsto_fpow`: the truncated powers converge entrywise to the infinite powers.
* `tendsto_trace_trunc_pow`: `tr((trunc M N)^{n+1}) → itrace M (n+1) = Σ_i (M^{n+1})_{ii}`, with
  `|itrace M (n+1)| ≤ (C S)^{n+1}` (`norm_itrace_succ_le`).
-/

open Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry.GeomFredholm

/-- Geometric decay in both indices. -/
structure GeomDecay (M : ℕ → ℕ → ℂ) (C η : ℝ) : Prop where
  const_nonneg : 0 ≤ C
  rate_nonneg : 0 ≤ η
  rate_lt_one : η < 1
  bound : ∀ i j, ‖M i j‖ ≤ C * η ^ i * η ^ j

/-- `S(η) = Σ_k η^{2k} = 1/(1 − η²)`. -/
def sqSum (η : ℝ) : ℝ := (1 - η ^ 2)⁻¹

theorem sq_lt_one {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) : η ^ 2 < 1 := by nlinarith

theorem hasSum_pow_two_mul {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) :
    HasSum (fun k : ℕ => η ^ k * η ^ k) (sqSum η) := by
  have h := hasSum_geometric_of_lt_one (sq_nonneg η) (sq_lt_one h0 h1)
  simp only [sqSum]
  convert h using 1
  funext k; rw [← pow_mul, ← mul_pow, ← sq]; ring_nf

theorem sqSum_pos {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) : 0 < sqSum η := by
  unfold sqSum; have := sq_lt_one h0 h1; exact inv_pos.mpr (by linarith)

theorem one_le_sqSum {η : ℝ} (h0 : 0 ≤ η) (h1 : η < 1) : 1 ≤ sqSum η := by
  unfold sqSum
  have h2 := sq_lt_one h0 h1
  rw [one_le_inv₀ (by linarith)]
  nlinarith [sq_nonneg η]

/-- The truncation to the first `N` indices. -/
def trunc (M : ℕ → ℕ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => M i j

/-- Powers of the truncation, as functions on `ℕ × ℕ`. -/
def fpow (M : ℕ → ℕ → ℂ) (N : ℕ) : ℕ → ℕ → ℕ → ℂ
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑ k ∈ range N, M i k * fpow M N n k j

/-- Powers of the infinite matrix. -/
def ipow (M : ℕ → ℕ → ℂ) : ℕ → ℕ → ℕ → ℂ
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, M i k * ipow M n k j

/-- The trace `Σ_i (M^n)_{ii}`. -/
def itrace (M : ℕ → ℕ → ℂ) (n : ℕ) : ℂ := ∑' i, ipow M n i i

variable {M : ℕ → ℕ → ℂ} {C η : ℝ}

theorem trunc_pow_apply (M : ℕ → ℕ → ℂ) (N n : ℕ) (i j : Fin N) :
    (trunc M N ^ n) i j = fpow M N n i j := by
  induction n generalizing i j with
  | zero => simp [fpow, Matrix.one_apply, Fin.val_inj]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih]
    simp only [fpow, trunc, Matrix.of_apply]
    exact Fin.sum_univ_eq_sum_range (fun k => M i k * fpow M N n k j) N

theorem trace_trunc_pow (M : ℕ → ℕ → ℂ) (N n : ℕ) :
    (trunc M N ^ n).trace = ∑ i ∈ range N, fpow M N n i i := by
  rw [Matrix.trace]
  simp only [Matrix.diag, trunc_pow_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => fpow M N n i i) N

/-! ## Bounds -/

theorem GeomDecay.summable_mul (hM : GeomDecay M C η) (a b : ℝ) :
    Summable fun k : ℕ => a * η ^ k * (b * η ^ k) := by
  have h := (hasSum_pow_two_mul hM.rate_nonneg hM.rate_lt_one).summable.mul_left (a * b)
  exact h.congr fun k => by ring

theorem norm_fpow_succ_le (hM : GeomDecay M C η) (N n i j : ℕ) :
    ‖fpow M N (n + 1) i j‖ ≤ C * (C * sqSum η) ^ n * η ^ i * η ^ j := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  induction n generalizing i j with
  | zero =>
    simp only [fpow, pow_zero, mul_one, mul_ite, mul_zero, Finset.sum_ite_eq']
    split_ifs
    · exact hM.bound i j
    · rw [norm_zero]; positivity
  | succ n ih =>
    rw [fpow]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ range N, ‖M i k * fpow M N (n + 1) k j‖ ≤
        C * η ^ i * η ^ k * (C * (C * sqSum η) ^ n * η ^ k * η ^ j) := fun k _ => by
      rw [norm_mul]; exact mul_le_mul (hM.bound i k) (ih k j) (norm_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    have hS2 : ∑ k ∈ range N, η ^ k * η ^ k ≤ sqSum η :=
      sum_le_hasSum _ (fun k _ => by positivity) (hasSum_pow_two_mul hη hM.rate_lt_one)
    calc ∑ k ∈ range N, C * η ^ i * η ^ k * (C * (C * sqSum η) ^ n * η ^ k * η ^ j)
        = C * C * (C * sqSum η) ^ n * η ^ i * η ^ j * ∑ k ∈ range N, η ^ k * η ^ k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ C * C * (C * sqSum η) ^ n * η ^ i * η ^ j * sqSum η :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = C * (C * sqSum η) ^ (n + 1) * η ^ i * η ^ j := by ring

theorem norm_ipow_succ_le (hM : GeomDecay M C η) (n i j : ℕ) :
    ‖ipow M (n + 1) i j‖ ≤ C * (C * sqSum η) ^ n * η ^ i * η ^ j := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  induction n generalizing i j with
  | zero =>
    simp only [ipow, pow_zero, mul_one]
    rw [tsum_eq_single j (fun k hk => by simp [hk])]
    simp only [if_true, mul_one]
    exact hM.bound i j
  | succ n ih =>
    rw [ipow]
    have hterm : ∀ k, ‖M i k * ipow M (n + 1) k j‖ ≤
        C * C * (C * sqSum η) ^ n * η ^ i * η ^ j * (η ^ k * η ^ k) := fun k => by
      rw [norm_mul]
      calc ‖M i k‖ * ‖ipow M (n + 1) k j‖
          ≤ (C * η ^ i * η ^ k) * (C * (C * sqSum η) ^ n * η ^ k * η ^ j) :=
            mul_le_mul (hM.bound i k) (ih k j) (norm_nonneg _)
              (le_trans (norm_nonneg _) (hM.bound i k))
        _ = _ := by ring
    have hsum := (hasSum_pow_two_mul hη hM.rate_lt_one).mul_left
      (C * C * (C * sqSum η) ^ n * η ^ i * η ^ j)
    have hns : Summable fun k => ‖M i k * ipow M (n + 1) k j‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum.summable
    calc ‖∑' k, M i k * ipow M (n + 1) k j‖ ≤ ∑' k, ‖M i k * ipow M (n + 1) k j‖ :=
          norm_tsum_le_tsum_norm hns
      _ ≤ C * C * (C * sqSum η) ^ n * η ^ i * η ^ j * sqSum η :=
          hns.tsum_le_tsum hterm hsum.summable |>.trans (le_of_eq hsum.tsum_eq)
      _ = C * (C * sqSum η) ^ (n + 1) * η ^ i * η ^ j := by ring

/-! ## Convergence of the truncated powers -/

theorem fpow_one_eventually (M : ℕ → ℕ → ℂ) (i j : ℕ) :
    ∀ᶠ N in atTop, fpow M N 1 i j = M i j := by
  filter_upwards [eventually_gt_atTop j] with N hN
  simp only [fpow]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (fun h => absurd (mem_range.mpr hN) h)]
  simp

theorem ipow_one (M : ℕ → ℕ → ℂ) (i j : ℕ) : ipow M 1 i j = M i j := by
  simp only [ipow]
  rw [tsum_eq_single j (fun k hk => by simp [hk])]
  simp

theorem sum_range_eq_tsum_indicator (f : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range N, f k = ∑' k, (if k < N then f k else 0) := by
  rw [tsum_eq_sum (s := range N) (fun k hk => by simp only [mem_range] at hk; simp [hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [mem_range.mp hk]

/-- **The truncated powers converge entrywise.** -/
theorem tendsto_fpow (hM : GeomDecay M C η) (n i j : ℕ) :
    Tendsto (fun N => fpow M N (n + 1) i j) atTop (𝓝 (ipow M (n + 1) i j)) := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  induction n generalizing i j with
  | zero =>
    rw [ipow_one]
    exact tendsto_const_nhds.congr' ((fpow_one_eventually M i j).mono fun N h => h.symm)
  | succ n ih =>
    have e : ∀ N, fpow M N (n + 2) i j =
        ∑' k, (if k < N then M i k * fpow M N (n + 1) k j else 0) := fun N => by
      rw [fpow, sum_range_eq_tsum_indicator]
    simp_rw [e]
    rw [ipow]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun k => C * η ^ i * η ^ k * (C * (C * sqSum η) ^ n * η ^ j * η ^ k))
      (hM.summable_mul _ _) (fun k => ?_) (Eventually.of_forall fun N k => ?_)
    · have h1 : ∀ᶠ N in atTop, (if k < N then M i k * fpow M N (n + 1) k j else 0) =
          M i k * fpow M N (n + 1) k j := by
        filter_upwards [eventually_gt_atTop k] with N hN; simp [hN]
      exact ((ih k j).const_mul (M i k)).congr' (h1.mono fun N h => h.symm)
    · split_ifs
      · rw [norm_mul]
        calc ‖M i k‖ * ‖fpow M N (n + 1) k j‖
            ≤ (C * η ^ i * η ^ k) * (C * (C * sqSum η) ^ n * η ^ k * η ^ j) :=
              mul_le_mul (hM.bound i k) (norm_fpow_succ_le hM N n k j) (norm_nonneg _)
                (le_trans (norm_nonneg _) (hM.bound i k))
          _ = _ := by ring
      · rw [norm_zero]; positivity

/-- **The traces of the truncated powers converge.** -/
theorem tendsto_trace_trunc_pow (hM : GeomDecay M C η) (n : ℕ) :
    Tendsto (fun N => (trunc M N ^ (n + 1)).trace) atTop (𝓝 (itrace M (n + 1))) := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  simp_rw [trace_trunc_pow, sum_range_eq_tsum_indicator]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun i => C * (C * sqSum η) ^ n * η ^ i * (1 * η ^ i))
    ((hM.summable_mul (C * (C * sqSum η) ^ n) 1)) (fun i => ?_)
    (Eventually.of_forall fun N i => ?_)
  · have h1 : ∀ᶠ N in atTop, (if i < N then fpow M N (n + 1) i i else 0) =
        fpow M N (n + 1) i i := by
      filter_upwards [eventually_gt_atTop i] with N hN; simp [hN]
    exact (tendsto_fpow hM n i i).congr' (h1.mono fun N h => h.symm)
  · split_ifs
    · refine (norm_fpow_succ_le hM N n i i).trans (le_of_eq ?_); ring
    · rw [norm_zero]; positivity

theorem norm_itrace_succ_le (hM : GeomDecay M C η) (n : ℕ) :
    ‖itrace M (n + 1)‖ ≤ (C * sqSum η) ^ (n + 1) := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  have hsum := (hasSum_pow_two_mul hη hM.rate_lt_one).mul_left (C * (C * sqSum η) ^ n)
  have hb : ∀ i, ‖ipow M (n + 1) i i‖ ≤ C * (C * sqSum η) ^ n * (η ^ i * η ^ i) := fun i =>
    (norm_ipow_succ_le hM n i i).trans (le_of_eq (by ring))
  have hns : Summable fun i => ‖ipow M (n + 1) i i‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum.summable
  unfold itrace
  calc ‖∑' i, ipow M (n + 1) i i‖ ≤ ∑' i, ‖ipow M (n + 1) i i‖ := norm_tsum_le_tsum_norm hns
    _ ≤ C * (C * sqSum η) ^ n * sqSum η :=
        (hns.tsum_le_tsum hb hsum.summable).trans (le_of_eq hsum.tsum_eq)
    _ = (C * sqSum η) ^ (n + 1) := by ring

theorem norm_trace_trunc_pow_le (hM : GeomDecay M C η) (N n : ℕ) :
    ‖(trunc M N ^ (n + 1)).trace‖ ≤ (C * sqSum η) ^ (n + 1) := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (sqSum_pos hη hM.rate_lt_one).le
  rw [trace_trunc_pow]
  refine (norm_sum_le _ _).trans ?_
  have hS2 : ∑ k ∈ range N, η ^ k * η ^ k ≤ sqSum η :=
    sum_le_hasSum _ (fun k _ => by positivity) (hasSum_pow_two_mul hη hM.rate_lt_one)
  calc ∑ i ∈ range N, ‖fpow M N (n + 1) i i‖
      ≤ ∑ i ∈ range N, C * (C * sqSum η) ^ n * (η ^ i * η ^ i) :=
        Finset.sum_le_sum fun i _ => (norm_fpow_succ_le hM N n i i).trans (le_of_eq (by ring))
    _ = C * (C * sqSum η) ^ n * ∑ i ∈ range N, η ^ i * η ^ i := by rw [Finset.mul_sum]
    _ ≤ C * (C * sqSum η) ^ n * sqSum η := mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = (C * sqSum η) ^ (n + 1) := by ring

end GaloisForLFunctions.HTGeometry.GeomFredholm

end
