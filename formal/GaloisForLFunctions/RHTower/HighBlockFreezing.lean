import GaloisForLFunctions.RHTower.HighBlockDualMeanSquare
import GaloisForLFunctions.RHTower.HighBlockTruncatedAFE
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualWeightDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualWeightHeightDerivative

/-!
# High-block law: the freezing error and the pole remainder (pointwise)

* The moving dual head `H_τ(τ) = Σ_{n<L} (n+1)^{s−1} W_{d,τ}((n+1)x)` differs from the head frozen
  at the sub-block base `T` by at most
  `A (τ−T) T^{−(d+5/4)} x^{d+1/4} Σ_{n<L} (n+1)^{−1/4}` (mean value inequality in the height, with
  the corpus's conductor-scale derivative bound `‖∂_u W_{d,u}(Y)‖ ≤ A Y^{d+η}/u^{d+η+1}` at
  `η = 1/4`).
* `Σ_{n<L} (n+1)^{−1/4} ≤ 1 + (4/3) L^{3/4}` (antitone sum–integral comparison).
* The pole residue is `≤ x^{1/2+d} e · e^{−τ²}/τ`.
On a sub-block of relative length `Δ` the freezing error is therefore `≲ Δ a^{1/4+}` pointwise, and
it is absorbed once `Δ ≤ a^{−1/4−θ−}`; the number of sub-blocks then stays `o(a^{1/2−θ−})`.
-/

open Complex Finset Set

namespace RHTower

noncomputable section

/-- The moving truncated dual head (without the `χ` factor). -/
def highBlockDualHead (d x τ : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.range L,
    (n + 1 : ℂ) ^ (displacedLinePt d τ - 1) * smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x)

theorem sum_highBlockDualTerm_eq (d x τ : ℝ) (L : ℕ) :
    ∑ n ∈ Finset.range L, highBlockDualTerm d x τ n =
      zetaChi (displacedLinePt d τ) * highBlockDualHead d x τ L := by
  unfold highBlockDualHead highBlockDualTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- Mean value inequality for the height variation of the dual weight. -/
theorem norm_dualWeight_sub_le_of_deriv {d Y T τ : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hY : 0 < Y) (hTτ : T ≤ τ) {A : ℝ}
    (hA : ∀ u ∈ Set.Icc T τ,
      ‖deriv (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y) u‖ ≤ A) :
    ‖smoothAFEZetaDisplacedDualWeight d τ Y - smoothAFEZetaDisplacedDualWeight d T Y‖ ≤
      A * (τ - T) := by
  have hderiv : ∀ u ∈ Set.Icc T τ,
      HasDerivWithinAt (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y)
        (deriv (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y) u) (Set.Icc T τ) u := by
    intro u _
    exact (hasDerivAt_smoothAFEZetaDisplacedDualWeight_via_neg hd hdhalf
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hY u).differentiableAt.hasDerivAt.hasDerivWithinAt
  have h := (convex_Icc T τ).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hA
    (Set.left_mem_Icc.mpr hTτ) (Set.right_mem_Icc.mpr hTτ)
  rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h

/-- **Freezing error of the dual head, pointwise.** -/
theorem exists_norm_highBlockDualHead_sub_frozen_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ x : ℝ, 0 < x → ∀ T τ : ℝ, 4 ≤ T → T ≤ τ →
      ∀ L : ℕ, ‖highBlockDualHead d x τ L - highBlockDualHeadFrozen d x T τ L‖ ≤
        A * (τ - T) * T ^ (-(d + 1 / 4 + 1)) * x ^ (d + 1 / 4) *
          ∑ n ∈ Finset.range L, ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_deriv_smoothAFEZetaDisplacedDualWeight_le (d0 := 1 / 4)
    (eta := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨A, hA0, ?_⟩
  intro d hd hd4 x hx T τ hT hTτ L
  have hT0 : 0 < T := by linarith
  unfold highBlockDualHead highBlockDualHeadFrozen
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hY : 0 < (n + 1 : ℝ) * x := by positivity
  rw [← mul_sub, norm_mul]
  have hcast : ((n : ℂ) + 1) = (((n + 1 : ℝ)) : ℂ) := by push_cast; ring
  have hpow : ‖(n + 1 : ℂ) ^ (displacedLinePt d τ - 1)‖ = (n + 1 : ℝ) ^ (-(1 / 2 + d)) := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn]
    congr 1
    rw [Complex.sub_re, displacedLinePt_re, Complex.one_re]
    ring
  have hderivb : ∀ u ∈ Set.Icc T τ,
      ‖deriv (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u ((n + 1 : ℝ) * x)) u‖ ≤
        A * ((n + 1 : ℝ) * x) ^ (d + 1 / 4) / T ^ (d + 1 / 4 + 1) := by
    intro u hu
    have hu4 : 4 ≤ u := le_trans hT hu.1
    refine (hA d hd hd4 hu4 hY).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact Real.rpow_le_rpow hT0.le hu.1 (by positivity)
  have hdiff := norm_dualWeight_sub_le_of_deriv hd (by linarith) hY hTτ hderivb
  rw [hpow]
  have hnn : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 + d)) := by positivity
  calc (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
        ‖smoothAFEZetaDisplacedDualWeight d τ ((n + 1 : ℝ) * x) -
          smoothAFEZetaDisplacedDualWeight d T ((n + 1 : ℝ) * x)‖
      ≤ (n + 1 : ℝ) ^ (-(1 / 2 + d)) *
          (A * ((n + 1 : ℝ) * x) ^ (d + 1 / 4) / T ^ (d + 1 / 4 + 1) * (τ - T)) :=
        mul_le_mul_of_nonneg_left hdiff hnn
    _ = A * (τ - T) * T ^ (-(d + 1 / 4 + 1)) * x ^ (d + 1 / 4) * (n + 1 : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.mul_rpow hn.le hx.le, Real.rpow_neg hT0.le]
        have h1 : (n + 1 : ℝ) ^ (-(1 / 2 + d)) * (n + 1 : ℝ) ^ (d + 1 / 4) =
            (n + 1 : ℝ) ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hn]
          congr 1
          ring
        rw [← h1]
        field_simp
        try ring

/-- `Σ_{n<L} (n+1)^{−1/4} ≤ 1 + (4/3) L^{3/4}`. -/
theorem sum_rpow_neg_quarter_le (L : ℕ) :
    ∑ n ∈ Finset.range L, ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)) ≤ 1 + (4 / 3) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  set f : ℝ → ℝ := fun u => (max u 1) ^ (-(1 / 4 : ℝ)) with hf
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) (0 + (L : ℝ))) := by
    intro u _ v _ huv
    simp only [hf]
    exact Real.rpow_le_rpow_of_nonpos (lt_max_of_lt_right one_pos) (max_le_max huv le_rfl)
      (by norm_num)
  have hsum := hanti.sum_le_integral
  have heq : ∀ n : ℕ, f (0 + ((n + 1 : ℕ) : ℝ)) = ((n + 1 : ℝ)) ^ (-(1 / 4 : ℝ)) := by
    intro n
    simp only [hf]
    rw [zero_add]
    push_cast
    rw [max_eq_left (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
  rw [Finset.sum_congr rfl (fun n _ => (heq n).symm)]
  refine hsum.trans ?_
  rw [zero_add]
  -- split the integral at 1
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hint01 : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hanti.mono (Set.Icc_subset_Icc le_rfl (by rw [zero_add]; exact hL1))
  have hint1L : IntervalIntegrable f MeasureTheory.volume 1 L := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hL1]
    exact hanti.mono (Set.Icc_subset_Icc zero_le_one (by rw [zero_add]))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint01 hint1L
  rw [← hsplit]
  have hleft : ∫ u in (0 : ℝ)..1, f u = 1 := by
    have : Set.EqOn f (fun _ => (1 : ℝ)) (Set.uIcc 0 1) := by
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      simp only [hf]
      rw [max_eq_right hu.2, Real.one_rpow]
    rw [intervalIntegral.integral_congr this]
    simp
  have hright : ∫ u in (1 : ℝ)..L, f u = ((L : ℝ) ^ (3 / 4 : ℝ) - 1) / (3 / 4) := by
    have : Set.EqOn f (fun u => u ^ (-(1 / 4 : ℝ))) (Set.uIcc 1 L) := by
      intro u hu
      rw [Set.uIcc_of_le hL1] at hu
      simp only [hf]
      rw [max_eq_left hu.1]
    rw [intervalIntegral.integral_congr this, integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [hleft, hright]
  have h0 : 0 ≤ (L : ℝ) ^ (3 / 4 : ℝ) := by positivity
  linarith

/-- The pole residue on the displaced line is Gaussian-small in the height. -/
theorem norm_smoothAFEZetaShiftedPoleResidue_displaced_le_highBlockFreezing {d x τ : ℝ} (hd0 : 0 ≤ d)
    (hd4 : d ≤ 1 / 4) (hx : 0 < x) (hτ : 1 ≤ τ) :
    ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x‖ ≤
      x ^ (1 / 2 + d) * Real.exp 1 * Real.exp (-(τ ^ 2)) / τ := by
  unfold smoothAFEZetaShiftedPoleResidue
  have h1s : 1 - displacedLinePt d τ = (((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [h1s, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  have hre : ((((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I).re = 1 / 2 + d := by simp
  have hre2 : (((((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I) ^ 2).re = (1 / 2 + d) ^ 2 - τ ^ 2 := by
    simp [sq]
    try ring
  rw [hre, hre2]
  have hnorm : τ ≤ ‖(((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I)
    have him : ((((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I).im = -τ := by simp
    rw [him, abs_neg, abs_of_pos (by linarith)] at this
    exact this
  have hexp : Real.exp ((1 / 2 + d) ^ 2 - τ ^ 2) ≤ Real.exp 1 * Real.exp (-(τ ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2 - τ ^ 2) /
        ‖(((1 / 2 + d : ℝ)) : ℂ) + ((-τ : ℝ) : ℂ) * I‖
      ≤ x ^ (1 / 2 + d) * (Real.exp 1 * Real.exp (-(τ ^ 2))) / τ := by
        gcongr
    _ = x ^ (1 / 2 + d) * Real.exp 1 * Real.exp (-(τ ^ 2)) / τ := by ring

end

end RHTower
