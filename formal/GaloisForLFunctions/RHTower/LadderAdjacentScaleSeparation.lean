import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# Adjacent scale separation of the constrained prolate ladder

At every fixed depth `k` the two-mode Fuchs rung converges, after normalization by its dominant
leakage, to the Hermite constant `θ_k = Q_k/Q_{k+1}`.  Dividing two consecutive rungs cancels the
common exponential clock of the Fuchs rates and leaves an exact power of the aperture:

```text
μ_{k+1}/μ_k ~ [Q_{k+1}²/(Q_k Q_{k+2})] · (A_{k+2}/A_{k+1}) · λ⁸.
```

The radial index step of the positive-parity family is `4`, so one rung advances the Fuchs index by
`4` and the leakage ratio by `λ^(8 : ℕ)`; in the finite-prime parameter `c = λ²` this is the fourth power
`c⁴`.  The limiting coefficient is the pure Hermite quantity `Q_{k+1}²/(Q_k Q_{k+2})`, which at
`k = 0` is `242/211`.
-/

open Filter

namespace RHTower

/-- The two-mode secular root is positive whenever both leakage scales are positive and both
coordinates are nonzero. -/
theorem twoModeSecularRoot_pos {d₀ d₁ ℓ₀ ℓ₁ : ℝ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (h₀ : ℓ₀ ≠ 0) (h₁ : ℓ₁ ≠ 0) :
    0 < GaloisForLFunctions.twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ := by
  have hl₀ : (0 : ℝ) < ℓ₀ ^ (2 : ℕ) := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h₀))
  have hl₁ : (0 : ℝ) < ℓ₁ ^ (2 : ℕ) := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h₁))
  unfold GaloisForLFunctions.twoModeSecularRoot
  exact div_pos (add_pos (mul_pos hl₀ hd₁) (mul_pos hl₁ hd₀)) (add_pos hl₀ hl₁)

/-- The depth-`k` rung of the constrained prolate ladder in the Fuchs-rate model: the two-mode
secular root of the aggregated head coordinate against the next Hermite coordinate. -/
noncomputable def ladderTwoModeRoot (A : ℕ → ℝ) (k : ℕ) (lam : ℝ) : ℝ :=
  GaloisForLFunctions.twoModeSecularRoot
    (fuchsRate (A k) (4 * k) lam) (fuchsRate (A (k + 1)) (4 * (k + 1)) lam)
    (Real.sqrt (constrainedProlateHermiteSquareSum k))
    (constrainedProlateHermiteCoordinate (k + 1))

theorem ladderTwoModeRoot_pos {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) (k : ℕ) {lam : ℝ}
    (hlam : 0 < lam) : 0 < ladderTwoModeRoot A k lam :=
  twoModeSecularRoot_pos (fuchsRate_pos (hA k) _ hlam) (fuchsRate_pos (hA (k + 1)) _ hlam)
    (Real.sqrt_pos.2 (constrainedProlateHermiteSquareSum_pos k)).ne'
    (constrainedProlateHermiteCoordinate_ne_zero (k + 1))

/-- Each rung, normalized by its dominant leakage, converges to `θ_k`. -/
theorem ladderTwoModeRoot_ratio_tendsto {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) (k : ℕ) :
    Tendsto (fun lam : ℝ =>
        ladderTwoModeRoot A k lam / fuchsRate (A (k + 1)) (4 * (k + 1)) lam)
      atTop (nhds (constrainedProlateHermiteTheta k)) :=
  constrainedProlate_fixedMode_twoMode_fuchs_ratio (hA k) (hA (k + 1)) k

/-- The adjacent ratio of the Hermite constants is the pure partial-sum quantity
`Q_{k+1}²/(Q_k Q_{k+2})`. -/
theorem constrainedProlateHermiteTheta_adjacent_ratio (k : ℕ) :
    constrainedProlateHermiteTheta (k + 1) / constrainedProlateHermiteTheta k
      = constrainedProlateHermiteWeightSum (k + 1) ^ (2 : ℕ) /
          (constrainedProlateHermiteWeightSum k *
            constrainedProlateHermiteWeightSum (k + 2)) := by
  have h0 := constrainedProlateHermiteWeightSum_pos k
  have h1 := constrainedProlateHermiteWeightSum_pos (k + 1)
  have h2 := constrainedProlateHermiteWeightSum_pos (k + 2)
  unfold constrainedProlateHermiteTheta
  field_simp

/-- **Adjacent rung separation, leakage-normalized form.**  The ratio of two consecutive ladder
rungs, corrected by the ratio of their dominant leakages, converges to the Hermite quotient
`θ_{k+1}/θ_k = Q_{k+1}²/(Q_k Q_{k+2})`. -/
theorem ladder_adjacent_ratio_tendsto {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) (k : ℕ) :
    Tendsto (fun lam : ℝ =>
        (ladderTwoModeRoot A (k + 1) lam / ladderTwoModeRoot A k lam) *
          (fuchsRate (A (k + 1)) (4 * (k + 1)) lam /
            fuchsRate (A (k + 2)) (4 * (k + 2)) lam))
      atTop (nhds (constrainedProlateHermiteTheta (k + 1) /
        constrainedProlateHermiteTheta k)) := by
  have h1 := ladderTwoModeRoot_ratio_tendsto hA (k + 1)
  have h2 := ladderTwoModeRoot_ratio_tendsto hA k
  have hθ : constrainedProlateHermiteTheta k ≠ 0 :=
    (constrainedProlateHermiteTheta_mem_Ioo k).1.ne'
  have h := h1.div h2 hθ
  have hlim : Tendsto (fun lam : ℝ =>
      (ladderTwoModeRoot A (k + 1) lam / fuchsRate (A (k + 2)) (4 * (k + 2)) lam) /
        (ladderTwoModeRoot A k lam / fuchsRate (A (k + 1)) (4 * (k + 1)) lam))
      atTop (nhds (constrainedProlateHermiteTheta (k + 1) /
        constrainedProlateHermiteTheta k)) := by
    simpa only [Pi.div_apply] using! h
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd1 : fuchsRate (A (k + 1)) (4 * (k + 1)) lam ≠ 0 :=
    (fuchsRate_pos (hA (k + 1)) _ hlam).ne'
  have hd2 : fuchsRate (A (k + 2)) (4 * (k + 2)) lam ≠ 0 :=
    (fuchsRate_pos (hA (k + 2)) _ hlam).ne'
  have hμ : ladderTwoModeRoot A k lam ≠ 0 := (ladderTwoModeRoot_pos hA k hlam).ne'
  field_simp

/-- **The `λ⁸` adjacent scale separation.**  Consecutive rungs of the constrained ladder separate
by exactly the eighth power of the aperture, with the explicit coefficient
`[Q_{k+1}²/(Q_k Q_{k+2})] · (A_{k+2}/A_{k+1})`.  In the finite-prime parameter `c = λ²` this is
the fourth power `c⁴`. -/
theorem ladder_adjacent_ratio_scaled_tendsto {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) (k : ℕ) :
    Tendsto (fun lam : ℝ =>
        (ladderTwoModeRoot A (k + 1) lam / ladderTwoModeRoot A k lam) / lam ^ (8 : ℕ))
      atTop (nhds ((constrainedProlateHermiteTheta (k + 1) /
        constrainedProlateHermiteTheta k) * (A (k + 2) / A (k + 1)))) := by
  have hprev := ladder_adjacent_ratio_tendsto hA k
  have h := hprev.const_mul (A (k + 2) / A (k + 1))
  rw [mul_comm (A (k + 2) / A (k + 1))] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd1 : fuchsRate (A (k + 1)) (4 * (k + 1)) lam ≠ 0 :=
    (fuchsRate_pos (hA (k + 1)) _ hlam).ne'
  have hd2 : fuchsRate (A (k + 2)) (4 * (k + 2)) lam ≠ 0 :=
    (fuchsRate_pos (hA (k + 2)) _ hlam).ne'
  have hμ : ladderTwoModeRoot A k lam ≠ 0 := (ladderTwoModeRoot_pos hA k hlam).ne'
  have hlam8 : lam ^ (8 : ℕ) ≠ 0 := pow_ne_zero _ hlam.ne'
  have hA1 : A (k + 1) ≠ 0 := (hA (k + 1)).ne'
  have hA2 : A (k + 2) ≠ 0 := (hA (k + 2)).ne'
  have hr : fuchsRate (A (k + 2)) (4 * (k + 2)) lam /
      fuchsRate (A (k + 1)) (4 * (k + 1)) lam = A (k + 2) / A (k + 1) * lam ^ (8 : ℕ) :=
    fuchsRate_radial_ratio (A (k + 2)) (A (k + 1)) (hA (k + 1)).ne' hlam.ne' (k + 1)
  have hd12 : fuchsRate (A (k + 1)) (4 * (k + 1)) lam /
      fuchsRate (A (k + 2)) (4 * (k + 2)) lam = A (k + 1) / (A (k + 2) * lam ^ (8 : ℕ)) := by
    have hinv := congrArg (fun t : ℝ => t⁻¹) hr
    simp only [inv_div] at hinv
    rw [hinv]
    field_simp
  rw [hd12]
  field_simp

/-- The first excited adjacent coefficient is the exact rational constant `242/211`. -/
theorem ladder_firstExcited_ratio_scaled_tendsto {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) :
    Tendsto (fun lam : ℝ =>
        (ladderTwoModeRoot A 1 lam / ladderTwoModeRoot A 0 lam) / lam ^ (8 : ℕ))
      atTop (nhds (242 / 211 * (A 2 / A 1))) := by
  have h := ladder_adjacent_ratio_scaled_tendsto hA 0
  rwa [constrainedProlateHermiteTheta_zero, constrainedProlateHermiteTheta_one,
    show (176 / 211 : ℝ) / (8 / 11) = 242 / 211 by norm_num] at h

end RHTower
