import GaloisForLFunctions.RHTower.HighBlockSmoothToSharpEnergy
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.HighBlockDirectMeanSquare

/-!
# High-block law: the direct head's smooth weight has bounded variation

The displaced direct coefficient is `(n+1)^{−(½−d)} V((n+1)/x) = [(n+1)^d V((n+1)/x)] · (n+1)^{−½}`:
an increasing factor `(n+1)^d ≤ (L+1)^d` times the decreasing cutoff `V ∈ [0,1]`. Its forward
differences have `ℓ¹` norm at most `3 (L+1)^d`, so by the smooth-to-sharp transfer the direct
mollified energy is at most `9 (L+1)^{2d}` times the largest sharp-cutoff critical energy.
At `d = R/log U`, `L ≤ U` this factor is at most `9 e^{4R}`.
-/

open Finset Complex

namespace RHTower

noncomputable section

/-- Total variation of a product of an increasing nonnegative sequence with a decreasing
sequence in `[0,1]`, with the `g(L) := 0` convention. -/
theorem sum_norm_headDiff_prod_le {a v : ℕ → ℝ} (ha : Monotone a) (ha0 : ∀ u, 0 ≤ a u)
    (hv : Antitone v) (hv0 : ∀ u, 0 ≤ v u) (hv1 : ∀ u, v u ≤ 1) (L : ℕ) :
    ∑ u ∈ Finset.range L, ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) L u‖ ≤ 3 * a L := by
  cases L with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith [ha0 0]
  | succ K =>
    rw [Finset.sum_range_succ]
    have hlast : ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) (K + 1) K‖ ≤ a (K + 1) := by
      simp only [headDiff, if_neg (lt_irrefl (K + 1)), sub_zero, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (ha0 K) (hv0 K))]
      calc a K * v K ≤ a K * 1 := mul_le_mul_of_nonneg_left (hv1 K) (ha0 K)
        _ = a K := mul_one _
        _ ≤ a (K + 1) := ha (Nat.le_succ K)
    have hinner : ∀ u ∈ Finset.range K,
        ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) (K + 1) u‖ ≤
          (a (u + 1) - a u) + a (K + 1) * (v u - v (u + 1)) := by
      intro u hu
      rw [Finset.mem_range] at hu
      have hlt : u + 1 < K + 1 := by omega
      simp only [headDiff, if_pos hlt]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hsplit : a u * v u - a (u + 1) * v (u + 1) =
          (a u - a (u + 1)) * v u + a (u + 1) * (v u - v (u + 1)) := by ring
      rw [hsplit]
      have hau : a u ≤ a (u + 1) := ha (Nat.le_succ u)
      have hvu : v (u + 1) ≤ v u := hv (Nat.le_succ u)
      calc |(a u - a (u + 1)) * v u + a (u + 1) * (v u - v (u + 1))|
          ≤ |(a u - a (u + 1)) * v u| + |a (u + 1) * (v u - v (u + 1))| := abs_add_le _ _
        _ = (a (u + 1) - a u) * v u + a (u + 1) * (v u - v (u + 1)) := by
            rw [abs_mul, abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg (hv0 u),
              abs_of_nonneg (ha0 (u + 1)), abs_of_nonneg (by linarith)]
            ring
        _ ≤ (a (u + 1) - a u) * 1 + a (K + 1) * (v u - v (u + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left (hv1 u) (by linarith))
              (mul_le_mul_of_nonneg_right (ha (by omega)) (by linarith))
        _ = (a (u + 1) - a u) + a (K + 1) * (v u - v (u + 1)) := by ring
    have hsum : ∑ u ∈ Finset.range K, ((a (u + 1) - a u) + a (K + 1) * (v u - v (u + 1))) =
        (a K - a 0) + a (K + 1) * (v 0 - v K) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub, ← Finset.mul_sum, Finset.sum_range_sub']
    calc (∑ u ∈ Finset.range K, ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) (K + 1) u‖) +
          ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) (K + 1) K‖
        ≤ (∑ u ∈ Finset.range K, ((a (u + 1) - a u) + a (K + 1) * (v u - v (u + 1)))) +
          a (K + 1) := add_le_add (Finset.sum_le_sum hinner) hlast
      _ = (a K - a 0) + a (K + 1) * (v 0 - v K) + a (K + 1) := by rw [hsum]
      _ ≤ 3 * a (K + 1) := by
          have h1 : a K ≤ a (K + 1) := ha (Nat.le_succ K)
          have h2 : a (K + 1) * (v 0 - v K) ≤ a (K + 1) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hv0 K, hv1 0]) (ha0 (K + 1))
          linarith [ha0 0]

/-- The critical sharp head coefficient `(n+1)^{−½}`. -/
def criticalHeadCoeff (n : ℕ) : ℂ := (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- The smooth displaced weight `(n+1)^d · Re V((n+1)/x)`. -/
def directWeight (d x : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ d * (smoothAFECutoff ((n + 1 : ℝ) / x)).re

/-- The displaced direct coefficient at `λ = 0` factors as weight times critical head. -/
theorem smoothAFEZetaDisplacedDirectDetectorCoeff_zero_eq {d x : ℝ} (hx : 0 < x) (n : ℕ) :
    smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n =
      ((directWeight d x n : ℝ) : ℂ) * criticalHeadCoeff n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hpos : 0 < (n + 1 : ℝ) / x := by positivity
  have hV : smoothAFECutoff ((n + 1 : ℝ) / x) =
      (((smoothAFECutoff ((n + 1 : ℝ) / x)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [smoothAFECutoff_im_eq_zero hpos]
  have hpt : -displacedLinePt d 0 = (((d - 1 / 2 : ℝ)) : ℂ) := by
    simp [displacedLinePt]
    try ring
  have hcast : ((n : ℂ) + 1) = (((n + 1 : ℝ)) : ℂ) := by push_cast; ring
  have hcpow : (n + 1 : ℂ) ^ (-displacedLinePt d 0) =
      (((n + 1 : ℝ) ^ (d - 1 / 2) : ℝ) : ℂ) := by
    rw [hpt, hcast, Complex.ofReal_cpow hn.le]
  have hsplit : (n + 1 : ℝ) ^ (d - 1 / 2) = (n + 1 : ℝ) ^ d * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hn]
    ring_nf
  unfold smoothAFEZetaDisplacedDirectDetectorCoeff directWeight criticalHeadCoeff
  rw [hcpow, hsplit, Complex.ofReal_mul, Complex.ofReal_mul, hV]
  simp only [Complex.ofReal_re, Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
  ring

/-- **Direct energy against any mollifier is controlled by the sharp critical energies.** -/
theorem sum_normSq_dirConv_direct_le_sharp {d x : ℝ} (hd0 : 0 ≤ d) (hx : 0 < x) (L N : ℕ)
    (b : Fin N → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u ∈ Finset.range L,
      ∑ r : Fin (L * N), ‖Sieve.dirConv L N (sharpHead criticalHeadCoeff L u) b r‖ ^ 2 ≤ C) :
    ∑ r : Fin (L * N),
        ‖Sieve.dirConv L N (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n) b r‖ ^ 2 ≤
      (3 * ((L : ℝ) + 1) ^ d) ^ 2 * C := by
  set a : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ d with ha_def
  set v : ℕ → ℝ := fun n => (smoothAFECutoff ((n + 1 : ℝ) / x)).re with hv_def
  have hhead : (fun n : Fin L => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n) =
      fun n : Fin L => ((a n * v n : ℝ) : ℂ) * criticalHeadCoeff n := by
    funext n
    rw [smoothAFEZetaDisplacedDirectDetectorCoeff_zero_eq hx]
    rfl
  rw [hhead]
  have htrans := energy_smooth_le_sharp L N (fun n => ((a n * v n : ℝ) : ℂ)) criticalHeadCoeff b hC
  refine htrans.trans ?_
  have ha : Monotone a := by
    intro u u' huu'
    simp only [ha_def]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ huu') hd0
  have ha0 : ∀ u, 0 ≤ a u := fun u => by simp only [ha_def]; positivity
  have hv : Antitone v := by
    intro u u' huu'
    simp only [hv_def]
    have h1 : (0 : ℝ) < (u + 1 : ℝ) / x := by positivity
    have h2 : (0 : ℝ) < (u' + 1 : ℝ) / x := by positivity
    have hle : (u + 1 : ℝ) / x ≤ (u' + 1 : ℝ) / x := by
      apply div_le_div_of_nonneg_right _ hx.le
      exact_mod_cast Nat.succ_le_succ huu'
    exact smoothAFECutoff_re_antitoneOn h1 h2 hle
  have hv0 : ∀ u, 0 ≤ v u := fun u => smoothAFECutoff_re_nonneg (by positivity)
  have hv1 : ∀ u, v u ≤ 1 := fun u => smoothAFECutoff_re_le_one (by positivity)
  have hW := sum_norm_headDiff_prod_le ha ha0 hv hv0 hv1 L
  have hW0 : 0 ≤ ∑ u ∈ Finset.range L, ‖headDiff (fun n => ((a n * v n : ℝ) : ℂ)) L u‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have haL : a L = ((L : ℝ) + 1) ^ d := rfl
  rw [haL] at hW
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW0 hW 2) hC0

end

end RHTower
