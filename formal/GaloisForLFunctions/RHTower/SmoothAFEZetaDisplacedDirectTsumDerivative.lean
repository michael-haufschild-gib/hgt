import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedClassicalHeadDerivative
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Termwise height derivative of the displaced direct Gaussian edge

Gaussian cutoff decay dominates the logarithm uniformly in height, so the
direct infinite Dirichlet edge differentiates term by term on every fixed
displaced line inside the critical strip.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaDisplacedDirectSourceField
    (d x τ : ℝ) : ℂ :=
  ∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x τ n

def smoothAFEZetaDisplacedDirectHeightDerivativeSourceField
    (d x τ : ℝ) : ℂ :=
  ∑' n : ℕ, smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n

theorem norm_natSucc_cpow_neg_displacedLinePt
    (d τ : ℝ) (n : ℕ) :
    ‖(n + 1 : ℂ) ^ (-displacedLinePt d τ)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 - d)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hpow := Complex.norm_cpow_eq_rpow_re_of_pos hn
    (-displacedLinePt d τ)
  rw [show (n + 1 : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_num]
  rw [hpow]
  have hre : (-displacedLinePt d τ).re = -(1 / 2 - d) := by
    simp [displacedLinePt]
  rw [hre]
  norm_num

theorem norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm
    (d x τ : ℝ) (n : ℕ) :
    ‖smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 - d)) *
        Real.log (n + 1 : ℝ) *
        ‖smoothAFECutoff ((n + 1 : ℝ) / x)‖ := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hlog0 : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hcast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [smoothAFEZetaDisplacedDirectHeightDerivativeTerm, norm_mul, norm_mul,
    norm_mul, norm_neg, norm_I, mul_one,
    norm_natSucc_cpow_neg_displacedLinePt]
  rw [hcast, ← Complex.ofReal_log hn.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hlog0]

theorem summable_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n‖) := by
  obtain ⟨K, hK, hcut⟩ :=
    exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  let C : ℝ := 4 * K * x ^ 2
  let q : ℕ → ℝ := fun n => C * (n + 1 : ℝ) ^ (-(7 / 4 : ℝ))
  have hq : Summable q := by
    have hbase := Real.summable_nat_rpow.mpr
      (show (-(7 / 4 : ℝ)) < -1 by norm_num)
    have hshift : Summable (fun n : ℕ =>
        (n + 1 : ℝ) ^ (-(7 / 4 : ℝ))) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff (f := fun n : ℕ =>
          (n : ℝ) ^ (-(7 / 4 : ℝ))) 1).mpr hbase
    exact hshift.mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hq
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by dsimp only [r]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hlog : Real.log r ≤ 4 * r ^ (1 / 4 : ℝ) := by
    have hraw := Real.log_le_rpow_div hr0.le
      (show (0 : ℝ) < 1 / 4 by norm_num)
    calc
      Real.log r ≤ r ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hraw
      _ = 4 * r ^ (1 / 4 : ℝ) := by norm_num [div_eq_mul_inv]; ring
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
    _ = C * r ^ (d - 9 / 4) := by
      dsimp only [C]
      rw [show r ^ (-(1 / 2 - d)) * (4 * r ^ (1 / 4 : ℝ)) *
          (K * x ^ 2 * r ^ (-2 : ℝ)) =
          (4 * K * x ^ 2) *
            (r ^ (-(1 / 2 - d)) * r ^ (1 / 4 : ℝ) *
              r ^ (-2 : ℝ)) by ring_nf]
      rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
      congr 1
      ring_nf
    _ ≤ C * r ^ (-(7 / 4 : ℝ)) := by
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) hC
    _ = q n := by rfl

theorem summable_norm_smoothAFEZetaDisplacedDirectTerm
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaDisplacedDirectTerm d x τ n‖) := by
  obtain ⟨K, hK, hcut⟩ :=
    exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  let C : ℝ := K * x ^ 2
  let q : ℕ → ℝ := fun n => C * (n + 1 : ℝ) ^ (-2 : ℝ)
  have hq : Summable q := by
    have hbase := Real.summable_nat_rpow.mpr
      (show (-2 : ℝ) < -1 by norm_num)
    have hshift : Summable (fun n : ℕ =>
        (n + 1 : ℝ) ^ (-2 : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff (f := fun n : ℕ =>
          (n : ℝ) ^ (-2 : ℝ)) 1).mpr hbase
    exact hshift.mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hq
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by
    dsimp only [r]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
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
  rw [smoothAFEZetaDisplacedDirectTerm, norm_mul,
    norm_natSucc_cpow_neg_displacedLinePt]
  have hp : 0 ≤ r ^ (-(1 / 2 - d)) := Real.rpow_nonneg hr0.le _
  calc
    r ^ (-(1 / 2 - d)) * ‖smoothAFECutoff (r / x)‖
      ≤ r ^ (-(1 / 2 - d)) * (K * x ^ 2 * r ^ (-2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcutPower hp
    _ = C * r ^ (d - 5 / 2) := by
      dsimp only [C]
      rw [show r ^ (-(1 / 2 - d)) * (K * x ^ 2 * r ^ (-2 : ℝ)) =
          (K * x ^ 2) *
            (r ^ (-(1 / 2 - d)) * r ^ (-2 : ℝ)) by ring_nf]
      rw [← Real.rpow_add hr0]
      congr 1
      ring_nf
    _ ≤ C * r ^ (-2 : ℝ) := by
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) hC
    _ = q n := by rfl

theorem hasDerivAt_smoothAFEZetaDisplacedDirectSourceField
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (smoothAFEZetaDisplacedDirectSourceField d x)
      (smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x τ) τ := by
  let f : ℕ → ℝ → ℂ := fun n u =>
    smoothAFEZetaDisplacedDirectTerm d x u n
  let f' : ℕ → ℝ → ℂ := fun n u =>
    smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x u n
  let q : ℕ → ℝ := fun n =>
    ‖smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n‖
  have hq : Summable q :=
    summable_norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm hdhalf hx τ
  have hderiv : ∀ n u, HasDerivAt (f n) (f' n u) u :=
    fun n u => hasDerivAt_smoothAFEZetaDisplacedDirectTerm d x u n
  have hbound : ∀ n u, ‖f' n u‖ ≤ q n := by
    intro n u
    dsimp only [f', q]
    rw [norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm,
      norm_smoothAFEZetaDisplacedDirectHeightDerivativeTerm]
  have hsum0 : Summable (fun n => f n τ) := by
    apply Summable.of_norm
    simpa only [f] using
      summable_norm_smoothAFEZetaDisplacedDirectTerm hdhalf hx τ
  have h := hasDerivAt_tsum hq hderiv hbound hsum0 τ
  change HasDerivAt
    (fun u => ∑' n : ℕ, smoothAFEZetaDisplacedDirectTerm d x u n)
    (∑' n : ℕ, smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n) τ
  simpa only [f, f'] using h

end RHTower
