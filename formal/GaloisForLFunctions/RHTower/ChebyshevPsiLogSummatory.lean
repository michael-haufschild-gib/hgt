import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.RHTower.TatuzawaIsekiIdentity
import GaloisForLFunctions.RHTower.DirichletSummatorySwap

/-!
# Chebyshev `ψ`, its floor summatory, and the Stirling log sandwich

Three inputs for the Tatuzawa–Iseki instantiation:

* `chebyshevPsi`: `ψ(k) = ∑_{m ≤ k} Λ(m)`.
* `floorSummatory_chebyshevPsi`: `∑_{d ≤ N} ψ(⌊N/d⌋) = ∑_{m ≤ N} log m` —
  the summed form of `ζ * Λ = log`, the transpose of the hyperbola swap in
  `MertensFirst.log_summatory_eq` (which pairs `Λ` against floors).
* the Stirling-strength sandwich
  `k·log k − k + 1 ≤ ∑_{m ≤ k} log m ≤ (k+1)·log(k+1) − (k+1) + 1`
  from left/right Riemann comparison against `∫₁^y log t dt = y log y − y + 1`,
  sharpening `MertensFirst.sum_log_le/ge` from `O(k)` to `O(log k)` error.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Chebyshev's summatory function `ψ(k) = ∑_{m ≤ k} Λ(m)`. -/
def chebyshevPsi (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k, vonMangoldt m

/-- `∫₁^y log t dt = y·log y − y + 1`. -/
theorem integral_log_one (y : ℝ) :
    ∫ t in (1:ℝ)..y, Real.log t = y * Real.log y - y + 1 := by
  rw [integral_log, Real.log_one]
  ring

/-- Monotonicity of `log` on `[1, ∞)`. -/
theorem monotoneOn_log {a b : ℝ} (ha : 1 ≤ a) :
    MonotoneOn (fun t : ℝ => Real.log t) (Set.Icc a b) := by
  intro x hx y _ hxy
  exact Real.log_le_log (by linarith [hx.1]) hxy

/-- **Stirling upper bound**: `∑_{m ≤ k} log m ≤ (k+1)log(k+1) − (k+1) + 1`. -/
theorem sum_log_le_stirling (k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Icc 1 k, Real.log m
      ≤ ((k:ℝ) + 1) * Real.log ((k:ℝ) + 1) - ((k:ℝ) + 1) + 1 := by
  have hmono : MonotoneOn (fun t : ℝ => Real.log t)
      (Set.Icc ((1:ℕ):ℝ) ((k + 1 : ℕ):ℝ)) := by
    apply monotoneOn_log
    norm_num
  have h := MonotoneOn.sum_le_integral_Ico
    (a := 1) (b := k + 1) (by omega) hmono
  have hsum : ∑ x ∈ Finset.Ico 1 (k + 1), Real.log x
      = ∑ m ∈ Finset.Icc 1 k, Real.log m := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  have hint : (∫ x in ((1:ℕ):ℝ)..((k + 1 : ℕ):ℝ), Real.log x)
      = ((k:ℝ) + 1) * Real.log ((k:ℝ) + 1) - ((k:ℝ) + 1) + 1 := by
    rw [show (((1:ℕ)):ℝ) = (1:ℝ) from by norm_num,
      show (((k + 1 : ℕ)):ℝ) = ((k:ℝ) + 1) from by push_cast; ring]
    exact integral_log_one _
  rw [hsum, hint] at h
  exact h

/-- **Stirling lower bound**: `k·log k − k + 1 ≤ ∑_{m ≤ k} log m`. -/
theorem stirling_le_sum_log (k : ℕ) (hk : 1 ≤ k) :
    (k:ℝ) * Real.log k - (k:ℝ) + 1
      ≤ ∑ m ∈ Finset.Icc 1 k, Real.log m := by
  have hmono : MonotoneOn (fun t : ℝ => Real.log t)
      (Set.Icc ((1:ℕ):ℝ) ((k:ℕ):ℝ)) := by
    apply monotoneOn_log
    norm_num
  have h := MonotoneOn.integral_le_sum_Ico (a := 1) (b := k) hk hmono
  have hint : (∫ x in ((1:ℕ):ℝ)..((k:ℕ):ℝ), Real.log x)
      = (k:ℝ) * Real.log k - (k:ℝ) + 1 := by
    push_cast
    exact integral_log_one _
  rw [hint] at h
  refine le_trans h ?_
  calc (∑ i ∈ Finset.Ico 1 k, Real.log ((i + 1 : ℕ) : ℝ))
      = ∑ m ∈ Finset.Icc 2 k, Real.log (m : ℝ) := by
        apply Finset.sum_nbij' (i := fun i => i + 1) (j := fun m => m - 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_Icc]
          omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          rw [Finset.mem_Ico]
          omega
        · intro i _
          omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          omega
        · intro i _
          rfl
    _ ≤ ∑ m ∈ Finset.Icc 1 k, Real.log (m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by omega) le_rfl)
          (fun m hm _ => Real.log_nonneg (by
            rw [Finset.mem_Icc] at hm
            exact_mod_cast hm.1))

/-- **The `ψ` floor summatory**: `∑_{d ≤ N} ψ(⌊N/d⌋) = ∑_{m ≤ N} log m`. -/
theorem floorSummatory_chebyshevPsi (N : ℕ) :
    floorSummatory chebyshevPsi N = ∑ m ∈ Finset.Icc 1 N, Real.log m := by
  have hswap := sum_Icc_mul_apply
    ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) vonMangoldt N
  have hzl : ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      * vonMangoldt = ArithmeticFunction.log := by
    rw [mul_comm]
    exact vonMangoldt_mul_zeta
  rw [hzl] at hswap
  have hzeta1 : ∑ d ∈ Finset.Icc 1 N,
      ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) d
        * ∑ m ∈ Finset.Icc 1 (N / d), vonMangoldt m
      = floorSummatory chebyshevPsi N := by
    unfold floorSummatory chebyshevPsi
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [natCoe_apply, zeta_apply, if_neg (by omega)]
    norm_num
  have hlogs : ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.log n
      = ∑ m ∈ Finset.Icc 1 N, Real.log m := by
    apply Finset.sum_congr rfl
    intro n _
    rw [log_apply]
  rw [← hzeta1, ← hswap]
  exact hlogs

end RHTower
