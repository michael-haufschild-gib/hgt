import GaloisForLFunctions.RHTower.ChiPairWeightJets
import GaloisForLFunctions.RHTower.TitchmarshZetaInputs

/-!
# Height jets and size of the dual archimedean carrier `χ(s₁+w)·χ(s₂+w)`

On the Levinson lines `s₁ = σ+it`, `s₂ = σ−it` (`σ = 1/2 − d`) with the dual shift
`w = −(1+iv)`, the archimedean carrier of the dual side of the product approximate functional
equation is `G(t;v) = χ(s₁+w)χ(s₂+w)`.  It factors exactly as the modulus weight
`P(t) = χ(s₁)χ(s₂)` times the two-ratio product `F(t;v)`, and the Leibniz rule combines the two
jet laws `‖P^{(i)}‖ ≤ i!‖P‖(11/t)^i` and `‖F^{(j)}‖ ≤ j!‖F‖(22(1+|v|)/t)^j` into

`‖G^{(n)}(t;v)‖ ≤ n!·‖G(t;v)‖·(33(1+|v|)/t)^n`   for `t ≥ 4`, `2|v| ≤ t`.

The carrier itself is polynomially bounded: both factors sit on the abscissa `−1/2 − d ∈ [−1, −1/2]`
at heights `t − v` and `−t − v`, where `‖χ‖ ≤ e⁴(1+|height|)²`.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The dual carrier `G(t;v) = χ(s₁+w)·χ(s₂+w)`. -/
def chiCarrier (d v : ℝ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t + levinsonShift v) *
    zetaChi (displacedLinePt d (-t) + levinsonShift v)

theorem chiCarrier_eq {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v t : ℝ) :
    chiCarrier d v t = chiPairWeight d t * chiRatioProduct d v t := by
  unfold chiCarrier chiPairWeight chiRatioProduct smoothAFEZetaChiShiftRatio
  have h1 := zetaChi_displaced_ne_zero hd hdq t
  have h2 := zetaChi_displaced_ne_zero hd hdq (-t)
  field_simp

theorem chiCarrier_fun_eq {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v : ℝ) :
    chiCarrier d v = fun t => chiPairWeight d t * chiRatioProduct d v t :=
  funext (chiCarrier_eq hd hdq v)

theorem contDiff_chiCarrier {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (v : ℝ) (n : ℕ) :
    ContDiff ℝ n (chiCarrier d v) := by
  rw [chiCarrier_fun_eq hd hdq v]
  exact (contDiff_chiPairWeight hd n).mul (contDiff_chiRatioProduct hd hdq v n)

/-- `∑ aⁱ bⁿ⁻ⁱ ≤ (a+b)ⁿ` for nonnegative `a, b`. -/
theorem sum_pow_mul_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) ≤ (a + b) ^ n := by
  rw [add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : (1 : ℝ) ≤ (n.choose i : ℝ) := by
    have := Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    exact_mod_cast this
  calc a ^ i * b ^ (n - i) = a ^ i * b ^ (n - i) * 1 := by ring
    _ ≤ a ^ i * b ^ (n - i) * (n.choose i : ℝ) := by gcongr

/-- **All-order height jets of the dual carrier.** -/
theorem norm_iteratedDeriv_chiCarrier_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {v t : ℝ}
    (ht : 4 ≤ t) (hv : 2 * |v| ≤ t) (n : ℕ) :
    ‖iteratedDeriv n (chiCarrier d v) t‖
      ≤ n.factorial * ‖chiCarrier d v t‖ * (33 * (1 + |v|) / t) ^ n := by
  have ht0 : (0 : ℝ) < t := by linarith
  rw [chiCarrier_fun_eq hd hdq v]
  have hleib := norm_iteratedFDeriv_mul_le (contDiff_chiPairWeight hd n)
    (contDiff_chiRatioProduct hd hdq v n) t (le_refl ((n : ℕ∞) : WithTop ℕ∞))
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
  refine hleib.trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedDeriv i (chiPairWeight d) t‖
          * ‖iteratedDeriv (n - i) (chiRatioProduct d v) t‖
        ≤ n.factorial * (‖chiPairWeight d t‖ * ‖chiRatioProduct d v t‖)
            * ((11 / t) ^ i * (22 * (1 + |v|) / t) ^ (n - i)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedDeriv_chiPairWeight_le hd hdq ht i
    have h2 := norm_iteratedDeriv_chiRatioProduct_le hd hdq ht hv (n - i)
    have hfac : (n.choose i : ℝ) * i.factorial * (n - i).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
    calc (n.choose i : ℝ) * ‖iteratedDeriv i (chiPairWeight d) t‖
          * ‖iteratedDeriv (n - i) (chiRatioProduct d v) t‖
        ≤ (n.choose i : ℝ) * (i.factorial * ‖chiPairWeight d t‖ * (11 / t) ^ i)
            * ((n - i).factorial * ‖chiRatioProduct d v t‖ * (22 * (1 + |v|) / t) ^ (n - i)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
            (by positivity)
      _ = n.factorial * (‖chiPairWeight d t‖ * ‖chiRatioProduct d v t‖)
            * ((11 / t) ^ i * (22 * (1 + |v|) / t) ^ (n - i)) := by
          rw [← hfac]
          ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum := sum_pow_mul_pow_le (a := 11 / t) (b := 22 * (1 + |v|) / t) (by positivity)
    (by positivity) n
  have hab : 11 / t + 22 * (1 + |v|) / t ≤ 33 * (1 + |v|) / t := by
    rw [← add_div, div_le_div_iff_of_pos_right ht0]
    nlinarith [abs_nonneg v]
  have hpow : (11 / t + 22 * (1 + |v|) / t) ^ n ≤ (33 * (1 + |v|) / t) ^ n :=
    pow_le_pow_left₀ (by positivity) hab n
  calc (n.factorial : ℝ) * (‖chiPairWeight d t‖ * ‖chiRatioProduct d v t‖)
        * ∑ i ∈ Finset.range (n + 1), (11 / t) ^ i * (22 * (1 + |v|) / t) ^ (n - i)
      ≤ n.factorial * (‖chiPairWeight d t‖ * ‖chiRatioProduct d v t‖)
          * (11 / t + 22 * (1 + |v|) / t) ^ n :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ n.factorial * (‖chiPairWeight d t‖ * ‖chiRatioProduct d v t‖)
          * (33 * (1 + |v|) / t) ^ n :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = n.factorial * ‖chiPairWeight d t * chiRatioProduct d v t‖ * (33 * (1 + |v|) / t) ^ n := by
        rw [norm_mul]

/-! ## Size of the carrier -/

theorem displacedLinePt_add_levinsonShift_eq (d τ v : ℝ) :
    displacedLinePt d τ + levinsonShift v
      = ((-1 / 2 - d : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I := by
  unfold displacedLinePt levinsonShift
  push_cast
  ring

/-- **Polynomial size of the carrier**: `‖G(t;v)‖ ≤ e⁸ (1+|t−v|)² (1+|t+v|)²` for `t ≥ 4`,
`2|v| ≤ t`. -/
theorem norm_chiCarrier_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {v t : ℝ} (ht : 4 ≤ t)
    (hv : 2 * |v| ≤ t) :
    ‖chiCarrier d v t‖ ≤ Real.exp 8 * ((1 + |t - v|) ^ (2 : ℕ) * (1 + |t + v|) ^ (2 : ℕ)) := by
  have hv' : |v| ≤ t / 2 := by linarith
  have h1' : (2 : ℝ) ≤ |t - v| := by
    have := abs_sub_abs_le_abs_sub t v
    rw [abs_of_pos (by linarith : (0 : ℝ) < t)] at this
    linarith
  have h2' : (2 : ℝ) ≤ |-t - v| := by
    have := abs_sub_abs_le_abs_sub t (-v)
    rw [abs_of_pos (by linarith : (0 : ℝ) < t), abs_neg, sub_neg_eq_add] at this
    rw [show -t - v = -(t + v) by ring, abs_neg]
    linarith
  unfold chiCarrier
  rw [displacedLinePt_add_levinsonShift_eq, displacedLinePt_add_levinsonShift_eq, norm_mul]
  have h1 := norm_zetaChi_le_negative_one_strip (σ := -1 / 2 - d) (t := t - v) (by linarith)
    (by linarith) h1'
  have h2 := norm_zetaChi_le_negative_one_strip (σ := -1 / 2 - d) (t := -t - v) (by linarith)
    (by linarith) h2'
  calc ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((t - v : ℝ) : ℂ) * I)‖
        * ‖zetaChi (((-1 / 2 - d : ℝ) : ℂ) + ((-t - v : ℝ) : ℂ) * I)‖
      ≤ (Real.exp 4 * (1 + |t - v|) ^ (2 : ℕ)) * (Real.exp 4 * (1 + |-t - v|) ^ (2 : ℕ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = Real.exp 8 * ((1 + |t - v|) ^ (2 : ℕ) * (1 + |t + v|) ^ (2 : ℕ)) := by
        rw [show -t - v = -(t + v) by ring, abs_neg,
          show (8 : ℝ) = 4 + 4 by norm_num, Real.exp_add]
        ring

end RHTower

end
