/-
# A rational remainder for the truncated exponential

Truncating the exponential series of a Banach-algebra element after `N` terms leaves the factorial
tail.  Once the truncation order is past twice the size of the element, the tail is dominated by a
geometric series of ratio one half, so the remainder is at most `2‖X‖^N/N!` -- an explicit bound
which is rational whenever the size bound is, and which is therefore usable as a certificate.

Main results:
* `factorial_mul_pow_le_factorial_add` — `N!(N+1)^k ≤ (k+N)!`.
* `tsum_factorial_tail_le` — the geometric domination of the factorial tail.
* `norm_exp_sub_partialSum_le` — **the truncation remainder**.
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open Finset Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The factorial of a shifted index dominates the shift's own factorial times a power. -/
theorem factorial_mul_pow_le_factorial_add (N : ℕ) :
    ∀ k : ℕ, Nat.factorial N * (N + 1) ^ k ≤ Nat.factorial (k + N)
  | 0 => by simp
  | k + 1 => by
      have hstep := factorial_mul_pow_le_factorial_add N k
      have hfac : Nat.factorial (k + 1 + N) = (k + N + 1) * Nat.factorial (k + N) := by
        have : k + 1 + N = (k + N) + 1 := by omega
        rw [this, Nat.factorial_succ]
      rw [hfac, pow_succ, ← mul_assoc]
      calc Nat.factorial N * (N + 1) ^ k * (N + 1)
          ≤ Nat.factorial (k + N) * (N + 1) := Nat.mul_le_mul_right _ hstep
        _ ≤ (k + N + 1) * Nat.factorial (k + N) := by
            rw [mul_comm]
            exact Nat.mul_le_mul_right _ (by omega)

/-- **Geometric domination of the factorial tail.** -/
theorem tsum_factorial_tail_le {b : ℝ} (hb0 : 0 ≤ b) {N : ℕ} (hN : 2 * b ≤ (N : ℝ) + 1) :
    ∑' k : ℕ, b ^ (k + N) / (Nat.factorial (k + N)) ≤ 2 * b ^ N / Nat.factorial N := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hfacpos : ∀ m : ℕ, (0 : ℝ) < Nat.factorial m := fun m => by
    exact_mod_cast Nat.factorial_pos m
  have hterm : ∀ k : ℕ, b ^ (k + N) / (Nat.factorial (k + N))
      ≤ (b ^ N / Nat.factorial N) * (1 / 2) ^ k := by
    intro k
    have hlow : (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k ≤ (Nat.factorial (k + N) : ℝ) := by
      have := factorial_mul_pow_le_factorial_add N k
      have hcast : ((Nat.factorial N * (N + 1) ^ k : ℕ) : ℝ) ≤ ((Nat.factorial (k + N) : ℕ) : ℝ) :=
        by exact_mod_cast this
      push_cast at hcast
      exact hcast
    have hnum : b ^ (k + N) = b ^ N * b ^ k := by rw [pow_add]; ring
    have hratio : b ^ k ≤ ((N : ℝ) + 1) ^ k * (1 / 2) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ hb0 ?_ k
      linarith
    have hpos1 : (0 : ℝ) < (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k := by
      have := hfacpos N
      positivity
    calc b ^ (k + N) / (Nat.factorial (k + N))
        ≤ b ^ (k + N) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) := by
          refine div_le_div_of_nonneg_left (by positivity) hpos1 hlow
      _ = (b ^ N * b ^ k) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) := by rw [hnum]
      _ ≤ (b ^ N * (((N : ℝ) + 1) ^ k * (1 / 2) ^ k))
            / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) := by
          refine (div_le_div_iff_of_pos_right hpos1).mpr ?_
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (b ^ N / Nat.factorial N) * (1 / 2) ^ k := by
          field_simp
  have hgeo : Summable fun k : ℕ => (b ^ N / Nat.factorial N) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsummable : Summable fun k : ℕ => b ^ (k + N) / (Nat.factorial (k + N)) := by
    refine hgeo.of_nonneg_of_le (fun k => by positivity) hterm
  refine le_trans (Summable.tsum_mono hsummable hgeo hterm) (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, inv_inv]
  ring

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The truncation remainder of the exponential series.**  Past twice the size of the element the
factorial tail is geometric, so the error of the `N`-term truncation is at most `2b^N/N!`. -/
theorem norm_exp_sub_partialSum_le (X : A) (N : ℕ) {b : ℝ} (hb : ‖X‖ ≤ b)
    (hN : 2 * b ≤ (N : ℝ) + 1) :
    ‖NormedSpace.exp X - ∑ k ∈ Finset.range N, ((Nat.factorial k : ℂ))⁻¹ • X ^ k‖
      ≤ 2 * b ^ N / Nat.factorial N := by
  have hb0 : 0 ≤ b := le_trans (norm_nonneg X) hb
  have hnorm : Summable fun n : ℕ => ‖((Nat.factorial n : ℂ))⁻¹ • X ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) X
  have hsum : Summable fun n : ℕ => ((Nat.factorial n : ℂ))⁻¹ • X ^ n := hnorm.of_norm
  have hshift : Summable fun k : ℕ => ((Nat.factorial (k + N) : ℂ))⁻¹ • X ^ (k + N) :=
    (summable_nat_add_iff N).mpr hsum
  have hshiftnorm : Summable fun k : ℕ => ‖((Nat.factorial (k + N) : ℂ))⁻¹ • X ^ (k + N)‖ :=
    (summable_nat_add_iff N).mpr hnorm
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => ((Nat.factorial n : ℂ))⁻¹ • X ^ n) N hsum
  have hexp : NormedSpace.exp X = ∑' n : ℕ, ((Nat.factorial n : ℂ))⁻¹ • X ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have hdiff : NormedSpace.exp X - ∑ k ∈ Finset.range N, ((Nat.factorial k : ℂ))⁻¹ • X ^ k
      = ∑' k : ℕ, ((Nat.factorial (k + N) : ℂ))⁻¹ • X ^ (k + N) := by
    rw [hexp, ← hsplit]
    abel
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm hshiftnorm) ?_
  have hbound : ∀ k : ℕ, ‖((Nat.factorial (k + N) : ℂ))⁻¹ • X ^ (k + N)‖
      ≤ b ^ (k + N) / (Nat.factorial (k + N)) := by
    intro k
    rw [norm_smul]
    have hfac : ‖((Nat.factorial (k + N) : ℂ))⁻¹‖ = ((Nat.factorial (k + N) : ℝ))⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [hfac, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (norm_pow_le X (k + N)) (pow_le_pow_left₀ (norm_nonneg X) hb _)
  have htail : Summable fun k : ℕ => b ^ (k + N) / (Nat.factorial (k + N)) := by
    have hgeo : Summable fun k : ℕ => (b ^ N / Nat.factorial N) * (1 / 2 : ℝ) ^ k :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine hgeo.of_nonneg_of_le (fun k => by positivity) fun k => ?_
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hlow : (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k ≤ (Nat.factorial (k + N) : ℝ) := by
      have := factorial_mul_pow_le_factorial_add N k
      have hcast : ((Nat.factorial N * (N + 1) ^ k : ℕ) : ℝ) ≤ ((Nat.factorial (k + N) : ℕ) : ℝ) :=
        by exact_mod_cast this
      push_cast at hcast
      exact hcast
    have hpos1 : (0 : ℝ) < (Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k := by
      have : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
      positivity
    have hratio : b ^ k ≤ ((N : ℝ) + 1) ^ k * (1 / 2) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ hb0 ?_ k
      linarith
    calc b ^ (k + N) / (Nat.factorial (k + N))
        ≤ b ^ (k + N) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) :=
          div_le_div_of_nonneg_left (by positivity) hpos1 hlow
      _ = (b ^ N * b ^ k) / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) := by
          rw [pow_add]; ring_nf
      _ ≤ (b ^ N * (((N : ℝ) + 1) ^ k * (1 / 2) ^ k))
            / ((Nat.factorial N : ℝ) * ((N : ℝ) + 1) ^ k) := by
          refine (div_le_div_iff_of_pos_right hpos1).mpr ?_
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (b ^ N / Nat.factorial N) * (1 / 2) ^ k := by
          field_simp
  exact le_trans (Summable.tsum_mono hshiftnorm htail hbound) (tsum_factorial_tail_le hb0 hN)

end GaloisForLFunctions.HTGeometry

end
