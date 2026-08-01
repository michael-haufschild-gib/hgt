import GaloisForLFunctions.RHTower.SoninShellTailWeightedSum

/-!
# Height-uniform shell bound with a moving physical threshold

A packet carrier need not coincide with a shell radius.  Splitting at a shell index would therefore
introduce an artificial rounding problem.  This file instead splits each term by whether its radius
lies below or above a real threshold.  Below the threshold Bessel controls total mass; above it a
power tail pays for every logarithmic weight.  Summing a full geometric majorant removes tower
height entirely.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap GaloisForLFunctions.HTGeometry
open scoped InnerProduct InnerProductSpace

/-- **Moving-threshold height-uniform bound.**  Below `T`, logarithmic weights are bounded by `M`;
above `T`, an inverse `(p+1)`-st power bound on outer mass pays for the whole tail. -/
theorem norm_evenLogShellChannel_apply_le_of_moving_powerTail
    {a r T : ℝ} (ha : 0 < a) (hr : 1 < r) (hT : 1 ≤ T)
    {p : ℕ} (hp : p ≠ 0) (n : ℕ) (u : evenSubspace) {M C : ℝ}
    (hM : ∀ k : ℕ, logShellRadius a r k ≤ T →
      |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, T ≤ t →
      ‖u - evenIndicatorCutoff t u‖ ^ 2 ≤ C / t ^ (p + 1)) :
    ‖evenLogShellChannel a r n u‖ ≤
      Real.sqrt (M ^ 2 * ‖u‖ ^ 2 +
        4 * C / a ^ p * (1 - (r ^ p)⁻¹)⁻¹) := by
  classical
  have hrp : (1 : ℝ) < r ^ p := one_lt_pow₀ hr hp
  have hrp0 : (0 : ℝ) < r ^ p := zero_lt_one.trans hrp
  have hx0 : (0 : ℝ) ≤ (r ^ p)⁻¹ := (inv_pos.mpr hrp0).le
  have hx1 : (r ^ p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hrp
  have hap : (0 : ℝ) < a ^ p := pow_pos ha p
  have hD0 : (0 : ℝ) ≤ 4 * C / a ^ p := by positivity
  have hterm : ∀ k ∈ Finset.range n,
      |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
        M ^ 2 * ‖evenIndicatorLayer (logShellRadius a r k)
            (logShellRadius a r (k + 1)) u‖ ^ 2 +
          (4 * C / a ^ p) * (r ^ p)⁻¹ ^ k := by
    intro k hk
    by_cases hnear : logShellRadius a r k ≤ T
    · have hlog := hM k hnear
      have hsq : |Real.log (logShellRadius a r k)| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (Real.log (logShellRadius a r k))]
      have hmass0 : 0 ≤
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 :=
        sq_nonneg _
      have hmain := mul_le_mul_of_nonneg_right hsq hmass0
      have hgeom0 : 0 ≤ (4 * C / a ^ p) * (r ^ p)⁻¹ ^ k := by positivity
      linarith
    · have hfar : T ≤ logShellRadius a r k := le_of_lt (lt_of_not_ge hnear)
      have hρpos : 0 < logShellRadius a r k := logShellRadius_pos ha hr k
      have hρ1 : 1 ≤ logShellRadius a r k := le_trans hT hfar
      have hshell := norm_evenIndicatorLayer_apply_le_high
        (logShellRadius_mono ha hr (Nat.le_succ k)) u
      have hsqmass :
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
            ‖u - evenIndicatorCutoff (logShellRadius a r k) u‖ ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) hshell
      have hmass := hsqmass.trans (htail _ hfar)
      have hlogsq : |Real.log (logShellRadius a r k)| ^ 2 ≤
          4 * logShellRadius a r k := sq_abs_log_le_four_mul hρ1
      have hweighted : |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
            4 * C / a ^ p * (r ^ p)⁻¹ ^ k := by
        have hmul : |Real.log (logShellRadius a r k)| ^ 2 *
            ‖evenIndicatorLayer (logShellRadius a r k)
                (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
              4 * logShellRadius a r k *
                (C / logShellRadius a r k ^ (p + 1)) :=
          mul_le_mul hlogsq hmass (sq_nonneg _) (by positivity)
        refine hmul.trans (le_of_eq ?_)
        have hne : logShellRadius a r k ≠ 0 := ne_of_gt hρpos
        have hstep : 4 * logShellRadius a r k *
            (C / logShellRadius a r k ^ (p + 1)) =
              4 * C / logShellRadius a r k ^ p := by
          rw [pow_succ]
          field_simp
        rw [hstep, logShellRadius_pow a r p k, inv_pow]
        field_simp
      have hfirst0 : 0 ≤ M ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k)
            (logShellRadius a r (k + 1)) u‖ ^ 2 := by positivity
      linarith
  have hgeom : ∑ k ∈ Finset.range n, (r ^ p)⁻¹ ^ k ≤ (1 - (r ^ p)⁻¹)⁻¹ := by
    rw [Finset.range_eq_Ico]
    simpa using sum_Ico_geom_le hx0 hx1 0 n
  have hmass := sum_norm_sq_evenIndicatorLayer_le a r ha hr n u
  have hsq : ‖evenLogShellChannel a r n u‖ ^ 2 ≤
      M ^ 2 * ‖u‖ ^ 2 + 4 * C / a ^ p * (1 - (r ^ p)⁻¹)⁻¹ := by
    rw [norm_sq_evenLogShellChannel_apply a r ha hr n u]
    calc ∑ k ∈ Finset.range n, |Real.log (logShellRadius a r k)| ^ 2 *
            ‖evenIndicatorLayer (logShellRadius a r k)
              (logShellRadius a r (k + 1)) u‖ ^ 2
        ≤ ∑ k ∈ Finset.range n,
            (M ^ 2 * ‖evenIndicatorLayer (logShellRadius a r k)
                (logShellRadius a r (k + 1)) u‖ ^ 2 +
              (4 * C / a ^ p) * (r ^ p)⁻¹ ^ k) := Finset.sum_le_sum hterm
      _ = M ^ 2 * (∑ k ∈ Finset.range n,
            ‖evenIndicatorLayer (logShellRadius a r k)
              (logShellRadius a r (k + 1)) u‖ ^ 2) +
          (4 * C / a ^ p) * (∑ k ∈ Finset.range n, (r ^ p)⁻¹ ^ k) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ M ^ 2 * ‖u‖ ^ 2 + 4 * C / a ^ p * (1 - (r ^ p)⁻¹)⁻¹ :=
        add_le_add (mul_le_mul_of_nonneg_left hmass (sq_nonneg M))
          (mul_le_mul_of_nonneg_left hgeom hD0)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- Frequency-side form of the moving-threshold bound. -/
theorem norm_evenFourierLogShellChannel_apply_le_of_moving_powerTail
    {a r T : ℝ} (ha : 0 < a) (hr : 1 < r) (hT : 1 ≤ T)
    {p : ℕ} (hp : p ≠ 0) (n : ℕ) (w : evenSubspace) {M C : ℝ}
    (hM : ∀ k : ℕ, logShellRadius a r k ≤ T →
      |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, T ≤ t →
      ‖evenFourierTransform w - evenIndicatorCutoff t (evenFourierTransform w)‖ ^ 2 ≤
        C / t ^ (p + 1)) :
    ‖evenFourierLogShellChannel a r n w‖ ≤
      Real.sqrt (M ^ 2 * ‖w‖ ^ 2 +
        4 * C / a ^ p * (1 - (r ^ p)⁻¹)⁻¹) := by
  rw [norm_evenFourierLogShellChannel_apply]
  have h := norm_evenLogShellChannel_apply_le_of_moving_powerTail ha hr hT hp n
    (evenFourierTransform w) hM hC htail
  rwa [evenFourierTransform_isometry] at h

end RHTower
