import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectTsumDerivative
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# Quantitative truncation of the displaced direct derivative edge

Gaussian cutoff decay absorbs the logarithmic derivative coefficient.  The
resulting uniform `n^{-7/4}` majorant gives an explicit `L^{-3/4}` tail.
-/

noncomputable section

namespace RHTower

open Complex

theorem exists_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm_le_rpow
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (n : ℕ),
      ‖smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n‖ ≤
        C * (n + 1 : ℝ) ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨K, hK, hcut⟩ :=
    exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  refine ⟨4 * K * x ^ 2, by positivity, fun τ n => ?_⟩
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hlog : Real.log r ≤ 4 * r ^ (1 / 4 : ℝ) := by
    have hraw := Real.log_le_rpow_div hr0.le
      (show (0 : ℝ) < 1 / 4 by norm_num)
    calc
      Real.log r ≤ r ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hraw
      _ = 4 * r ^ (1 / 4 : ℝ) := by
        norm_num [div_eq_mul_inv]
        ring
  have harg : 0 < r / x := div_pos hr0 hx
  have hcut' := hcut harg
  have hcutPower :
      ‖smoothAFECutoff (r / x)‖ ≤ K * x ^ 2 * r ^ (-2 : ℝ) := by
    calc
      ‖smoothAFECutoff (r / x)‖ ≤ K * (r / x) ^ (-2 : ℝ) := hcut'
      _ = K * x ^ 2 * r ^ (-2 : ℝ) := by
        rw [Real.div_rpow hr0.le hx.le]
        rw [Real.rpow_neg hr0.le, Real.rpow_neg hx.le]
        have hr2 : r ^ (2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr0 2).ne'
        have hx2 : x ^ (2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx 2).ne'
        field_simp [hr2, hx2]
        rw [Real.rpow_two]
  rw [norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm]
  have hp : 0 ≤ r ^ (-(1 / 2 - d)) := Real.rpow_nonneg hr0.le _
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  calc
    r ^ (-(1 / 2 - d)) * Real.log r *
        ‖smoothAFECutoff (r / x)‖
      ≤ r ^ (-(1 / 2 - d)) * (4 * r ^ (1 / 4 : ℝ)) *
          (K * x ^ 2 * r ^ (-2 : ℝ)) := by gcongr
    _ = (4 * K * x ^ 2) * r ^ (d - 9 / 4) := by
      rw [show r ^ (-(1 / 2 - d)) * (4 * r ^ (1 / 4 : ℝ)) *
          (K * x ^ 2 * r ^ (-2 : ℝ)) =
          (4 * K * x ^ 2) *
            (r ^ (-(1 / 2 - d)) * r ^ (1 / 4 : ℝ) *
              r ^ (-2 : ℝ)) by ring_nf]
      rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
      congr 1
      ring_nf
    _ ≤ (4 * K * x ^ 2) * r ^ (-(7 / 4 : ℝ)) := by
      have hC : 0 ≤ 4 * K * x ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) hC
    _ = (4 * K * x ^ 2) * (n + 1 : ℝ) ^ (-(7 / 4 : ℝ)) := by
      rfl

theorem exists_norm_smoothAFEZetaDisplacedDirectHeightDerivativeSourceField_sub_sum_le
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (L : ℕ), 1 ≤ L →
      ‖smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x τ -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n‖ ≤
        C * (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm_le_rpow
      hdhalf hx
  refine ⟨C, hC, fun τ L hL => ?_⟩
  let f : ℕ → ℂ := fun n =>
    smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n
  have hnorm : Summable (fun n => ‖f n‖) := by
    simpa only [f] using
      summable_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm hdhalf hx τ
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [smoothAFEZetaDisplacedDirectHeightDerivativeSourceField, show
      (fun n => smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n) = f by rfl,
    heq]
  have hnormTail : Summable (fun j => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hp : (-(7 / 4 : ℝ)) < -1 := by norm_num
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-(7 / 4 : ℝ))) := by
    have hbase := Real.summable_nat_rpow.mpr hp
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      C * (((j + L + 1 : ℕ) : ℝ)) ^ (-(7 / 4 : ℝ))) :=
    hpow.mul_left C
  calc
    ‖∑' j : ℕ, f (j + L)‖
        ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ,
        C * (((j + L + 1 : ℕ) : ℝ)) ^ (-(7 / 4 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun j => by
        simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc] using
          hpoint τ (j + L)) hnormTail hmajor
    _ = C * ∑' j : ℕ,
        (((j + L + 1 : ℕ) : ℝ)) ^ (-(7 / 4 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ C * ((L : ℝ) ^ ((1 : ℝ) - 7 / 4) / ((7 : ℝ) / 4 - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le (show (1 : ℝ) < 7 / 4 by norm_num) hL) hC
    _ = C * (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
      ring_nf

end RHTower
